import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The propagation argument adapts the checked parent reduction R_meta_2504_1.
theorem PEqualNP.Outside.R_meta_3338_27
    (cofactor :
      let z := fun (x : Fin 8 → Bool) =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
      ∀ (pre post : List Gate) (q o : ℕ), FanInTwo ⟨pre ++ post, o⟩ →
        (∀ x : Fin 8 → Bool,
          let w := (Circuit.mk pre 0).wires [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1]
          (Circuit.mk post o).eval (w ++ [w.getD q false]) = z x) →
        13 ≤ pre.length + post.length)
    (paired :
      let z := fun (x : Fin 8 → Bool) =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
      let v := fun (b : Bool) (x : Fin 8 → Bool) =>
        [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]
      ∀ (pre post : List Gate) (q o : ℕ), FanInTwo ⟨pre ++ post,o⟩ →
        pre.length + post.length = 13 →
        q ∉ ([0,2,7,8,9] : List ℕ) →
        (∀ x : Fin 8 → Bool, x 1 = true → x 3 = true → z x = false →
          ((Circuit.mk pre 0).wires (v false x)).getD q false = false) →
        ¬ ∀ (b : Bool) (x : Fin 8 → Bool),
          let w := (Circuit.mk pre 0).wires (v b x)
          (Circuit.mk post o).eval (w ++ [b || w.getD q false]) = (z x || (b && (x 0 || x 3)))) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) =>   have x4 : ℕ := PEqualNP.MetaComplexity.tableIndex x3;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x4 / (64 : ℕ)) (0 : ℕ)).testBit (x4 % (64 : ℕ)); ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 →     x4.length + x5.length ≤ (13 : ℕ) →       (∀ x11 ∈ x4 ++ x5, x1 x11 = Bool.false) →         x1 x6 = Bool.true →           x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →             (have x14 : Fin (8 : ℕ) → Bool := fun (x14 : Fin (8 : ℕ)) => Decidable.decide (x14 = (1 : Fin (8 : ℕ)) ∨ x14 = (3 : Fin (8 : ℕ)));               have x15 : Bool → Bool := fun (x15 : Bool) => x6.op.eval (List.map (fun (x16 : ℕ) => ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x15 x14)).getD x16 Bool.false) x6.inputs);               x15 Bool.true ≠ x15 Bool.false) →               (∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x3 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x16) ≠ (x3 x16 || x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ))) := by
  intro read input target pre post g out D fan budget rest reads op _ correct
  by_contra! full
  have noReadGate (g : Gate) (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (skip : read g = false) (w w' : List Bool)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
    obtain ⟨op,pins⟩ := g
    rcases basis with h|h|h <;> change op = _ at h <;> subst op
    · apply congrArg GateOp.and.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · apply congrArg GateOp.or.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · cases pins with
      | nil => rfl
      | cons i rest =>
        change (decide (i = 6) || false) = false at skip
        have ne : i ≠ 6 := by simpa using skip
        exact congrArg Bool.not (agree i ne)
  let stepSix (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have noReadSuffix (gs : List Gate)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ read g = false)
      (w w' : List Bool) (len : w.length = w'.length)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      ∀ i, i ≠ 6 → (gs.foldl stepSix w).getD i false = (gs.foldl stepSix w').getD i false := by
    induction gs generalizing w w' with
    | nil => exact agree
    | cons g gs ih =>
      obtain ⟨basis,skip⟩ := ok g (by simp)
      apply ih (fun h hh => ok h (List.mem_cons_of_mem g hh)) (stepSix w g) (stepSix w' g)
      · simp [stepSix,len]
      · intro i ne
        by_cases h : i < w.length
        · simpa only [stepSix,List.getD_append _ _ false i h,List.getD_append _ _ false i (len ▸ h)] using agree i ne
        · have he := noReadGate g basis skip w w' agree
          simp only [stepSix,List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : w'.length ≤ i),len,he]
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepSix w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (stepSix w g) (by simp [stepSix]; omega)]
      exact List.getD_append _ _ false i hi
  have lenRun (gs : List Gate) (v : List Bool) :
      (gs.foldl stepSix v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons h gs ih => rw [List.foldl_cons,ih]; simp [stepSix]; omega
  have six : out ≠ 6 := by
    rintro rfl
    let x : Fin 8 → Bool := fun _ => false
    have eq := full x
    change ((pre ++ g :: post).foldl stepSix _).getD 6 false = _ at eq
    rw [preserve _ (input true x) 6 (by decide)] at eq
    exact (by decide : (input true x).getD 6 false ≠ (target x || x 0 || x 3)) eq
  have gmem : g ∈ D.gates := by simp [D]
  have has : 6 ∈ g.inputs := by
    change ((if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any _) = true at reads
    rw [op] at reads
    change (g.inputs.any fun i => decide (i = 6)) = true at reads
    simpa using reads
  have n := (fan g gmem).2
  have shape : ∃ q ∈ g.inputs, ∀ w : List Bool,
      g.op.eval (g.inputs.map fun i => w.getD i false) = (w.getD 6 false || w.getD q false) := by
    rw [op]
    cases e : g.inputs with
    | nil => simp [e] at has
    | cons i l =>
      cases l with
      | nil =>
        have hi : 6 = i := by simpa [e] using has
        subst i
        exact ⟨6,by simp,fun w => by change (_ || false) = (_ || _); simp⟩
      | cons j l =>
        have nil : l = [] := List.length_eq_zero_iff.mp (by rw [e] at n; simp only [List.length_cons] at n; omega)
        subst l
        rcases (by simpa [e] using has : 6 = i ∨ 6 = j) with h|h
        · subst i; exact ⟨j,by simp,fun w => by change (_ || (_ || false)) = (_ || _); simp⟩
        · subst j; exact ⟨i,by simp,fun w => by change (_ || (_ || false)) = (_ || _); simp [Bool.or_comm]⟩
  obtain ⟨q,pin,gate⟩ := shape
  let v (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]
  let W (b : Bool) (x : Fin 8 → Bool) := pre.foldl stepSix (v b x)
  let A (b : Bool) (x : Fin 8 → Bool) := pre.foldl stepSix (input b x)
  have part (l : List Gate) (sub : ∀ h ∈ l, h ∈ pre ++ post) :
      ∀ h ∈ l, (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ read h = false := by
    intro h m
    have hp := sub h m
    have hc : h ∈ D.gates := by
      rcases List.mem_append.mp hp with e|e <;> simp [D,e]
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan h hc).1,rest h hp⟩
  have comp (b : Bool) (x : Fin 8 → Bool) :
      (Circuit.mk post out).eval (W b x ++ [b || (W b x).getD q false]) =
        (target x || (b && (x 0 || x 3))) := by
    have init (i : ℕ) (ne : i ≠ 6) : (input b x).getD i false = (v b x).getD i false := by
      by_cases h : i < 10
      · interval_cases i <;> first | rfl | contradiction
      · rw [List.getD_eq_default _ false (by change i ≥ 10; omega),
            List.getD_eq_default _ false (by change i ≥ 10; omega)]
    have early := noReadSuffix pre (part pre (fun _ h => List.mem_append_left _ h))
      (input b x) (v b x) rfl init
    have len : (A b x).length = (W b x).length := by simp only [A,W,lenRun]; rfl
    have at6 : (A b x).getD 6 false = b := preserve pre (input b x) 6 (by change 6 < 10; decide)
    have value : g.op.eval (g.inputs.map fun i => (A b x).getD i false) =
        (b || (W b x).getD q false) := by
      rw [gate,at6]
      by_cases h : q = 6
      · subst q
        rw [at6,show (W b x).getD 6 false = false from preserve pre (v b x) 6 (by change 6 < 10; decide)]
        simp
      · rw [show (A b x).getD q false = (W b x).getD q false from early q h]
    let bit := b || (W b x).getD q false
    have next (i : ℕ) (ne : i ≠ 6) : (stepSix (A b x) g).getD i false =
        (W b x ++ [bit]).getD i false := by
      simp only [stepSix,value,bit]
      by_cases h : i < (A b x).length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (len ▸ h)]
        exact early i ne
      · simp only [List.getD_append_right _ _ _ _ (by omega : (A b x).length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : (W b x).length ≤ i),len]
    have eq := noReadSuffix post (part post (fun _ h => List.mem_append_right _ h))
      _ _ (by simp [stepSix,len]) next out six
    have link : D.eval (input b x) = (Circuit.mk post out).eval (W b x ++ [bit]) := by
      change ((pre ++ g :: post).foldl stepSix _).getD out false = (post.foldl stepSix (W b x ++ [bit])).getD out false
      simpa only [List.foldl_append,List.foldl_cons,A] using eq
    rw [← link]
    cases b
    · simpa using correct x
    · simpa [Bool.or_assoc] using full x
  have legal : FanInTwo ⟨pre ++ post,out⟩ := by
    intro h e
    apply fan
    rcases List.mem_append.mp e with m|m <;> simp [D,m]
  have low := cofactor pre post q out legal (fun x => by
    have base : v false x = [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1] := by simp [v]
    dsimp only
    rw [← base]
    change (Circuit.mk post out).eval (W false x ++ [(W false x).getD q false]) = target x
    simpa only [Bool.false_or,Bool.false_and,Bool.or_false] using comp false x)
  have zero (x : Fin 8 → Bool) (h1 : x 1 = true) (h3 : x 3 = true) (hz : target x = false) :
      (W false x).getD q false = false := by
    have same : W false x = W true x := by simp [W,v,h1]
    have pair (b : Bool) := comp b x
    by_contra! nonzero
    have on : (W false x).getD q false = true := by simpa using nonzero
    have f := pair false
    have t := pair true
    simp only [on,hz,Bool.false_or,Bool.false_and] at f
    rw [← same] at t
    simp [h3,hz] at t
    exact Bool.noConfusion (f.symm.trans t)
  have permitted : q ∉ ([0,2,7,8,9] : List ℕ) := by
    intro bad
    have witness : ∃ x : Fin 8 → Bool, x 1 = true ∧ x 3 = true ∧ target x = false ∧
        (v false x).getD q false = true ∧ q < 10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
      rcases bad with e|e|e|e|e <;> subst q
      · exact ⟨fun j => decide (j = 1 ∨ j = 3), by decide⟩
      · exact ⟨fun j => decide (j = 1 ∨ j = 3 ∨ j = 4), by decide⟩
      · exact ⟨fun j => decide (j = 1 ∨ j = 3 ∨ j = 6), by decide⟩
      · exact ⟨fun j => decide (j = 1 ∨ j = 3), by decide⟩
      · exact ⟨fun j => decide (j = 1 ∨ j = 3), by decide⟩
    obtain ⟨x,h1,h3,hz,high,bound⟩ := witness
    have lo := zero x h1 h3 hz
    have hi := (preserve pre (v false x) q bound).trans high
    exact Bool.noConfusion (lo.symm.trans hi)
  exact paired pre post q out legal (by omega) permitted zero comp
