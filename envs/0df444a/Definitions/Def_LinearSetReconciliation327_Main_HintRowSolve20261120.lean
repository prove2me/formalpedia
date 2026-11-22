-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowSolve20261120
-- name    : LinearSetReconciliation327_Main_HintRowSolve20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:32:37.030181+00:00
-- url     : https://prove2.me/theorems/2f237804-312f-460b-a328-2fcbd5fdf889
-- title:
--   LinearSetReconciliation327 — HintRowSolve (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowSolve20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

abbrev HintVec (d : ℕ) := Fin d → ZMod 2

structure HintElimState (a h : ℕ) where
  residual : HintVec a →ₗ[ZMod 2] HintVec a
  lift : HintVec a →ₗ[ZMod 2] HintVec h

def hintRead {a : ℕ} (p : Fin a) : HintVec a →ₗ[ZMod 2] ZMod 2 where
  toFun v := v p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hintScale {a h : ℕ} (f : HintVec a →ₗ[ZMod 2] ZMod 2) (v : HintVec h) :
    HintVec a →ₗ[ZMod 2] HintVec h where
  toFun x := f x • v
  map_add' x y := by rw [map_add, add_smul]
  map_smul' c x := by rw [map_smul]; simp only [smul_eq_mul, smul_smul, RingHom.id_apply]

def hintElimInit (a h : ℕ) : HintElimState a h := ⟨LinearMap.id, 0⟩

def hintElimKernel {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (j : Fin h) : HintVec h :=
  Pi.single j 1 + E.lift (A (Pi.single j 1))

def hintElimInsert {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (j : Fin h) (p : Fin a) : HintElimState a h :=
  let f := (hintRead p).comp E.residual
  ⟨E.residual + hintScale f (E.residual (A (Pi.single j 1))),
    E.lift + hintScale f (hintElimKernel A E j)⟩

theorem hintVec_add_self {d : ℕ} (v : HintVec d) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

structure HintElimInvariant {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (done : Finset (Fin h)) (E : HintElimState a h) : Prop where
  decompose : ∀ v, A (E.lift v) + E.residual v = v
  fixed : ∀ j ∈ done, E.lift (A (Pi.single j 1)) = Pi.single j 1
  killed : ∀ j ∈ done, E.residual (A (Pi.single j 1)) = 0
  support : ∀ v j, j ∉ done → E.lift v j = 0

theorem hintElimInit_invariant {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) :
    HintElimInvariant A ∅ (hintElimInit a h) := by
  constructor
  · intro v
    simp [hintElimInit]
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj
  · intro v j _
    rfl

theorem hintElimInsert_residual {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (j : Fin h) (p : Fin a) (v : HintVec a) :
    (hintElimInsert A E j p).residual v =
      E.residual v + E.residual v p • E.residual (A (Pi.single j 1)) := rfl

theorem hintElimInsert_lift {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (j : Fin h) (p : Fin a) (v : HintVec a) :
    (hintElimInsert A E j p).lift v =
      E.lift v + E.residual v p • hintElimKernel A E j := rfl

theorem hintElimKernel_image {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (done : Finset (Fin h)) (E : HintElimState a h) (j : Fin h)
    (hInv : HintElimInvariant A done E) :
    A (hintElimKernel A E j) = E.residual (A (Pi.single j 1)) := by
  rw [hintElimKernel, map_add]
  conv_lhs => arg 1; rw [← hInv.decompose (A (Pi.single j 1))]
  calc
    (A (E.lift (A (Pi.single j 1))) + E.residual (A (Pi.single j 1))) +
        A (E.lift (A (Pi.single j 1))) =
        E.residual (A (Pi.single j 1)) +
          (A (E.lift (A (Pi.single j 1))) + A (E.lift (A (Pi.single j 1)))) := by abel
    _ = _ := by rw [hintVec_add_self, add_zero]

theorem hintElimKernel_nonzero {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (done : Finset (Fin h)) (E : HintElimState a h) (j : Fin h)
    (hInv : HintElimInvariant A done E) (hj : j ∉ done) : hintElimKernel A E j ≠ 0 := by
  intro hz
  have hh := congrFun hz j
  simpa [hintElimKernel, hInv.support _ j hj] using hh

theorem hintElimInsert_invariant {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (done : Finset (Fin h)) (E : HintElimState a h) (j : Fin h) (p : Fin a)
    (hInv : HintElimInvariant A done E) (hPivot : E.residual (A (Pi.single j 1)) p = 1) :
    HintElimInvariant A (insert j done) (hintElimInsert A E j p) := by
  classical
  constructor
  · intro v
    rw [hintElimInsert_lift, hintElimInsert_residual, map_add, map_smul, hintElimKernel_image A done E j hInv]
    calc
      A (E.lift v) + E.residual v p • E.residual (A (Pi.single j 1)) +
          (E.residual v + E.residual v p • E.residual (A (Pi.single j 1))) =
          (A (E.lift v) + E.residual v) +
            (E.residual v p • E.residual (A (Pi.single j 1)) + E.residual v p • E.residual (A (Pi.single j 1))) := by abel
      _ = v := by rw [hInv.decompose, hintVec_add_self, add_zero]
  · intro k hk
    rcases Finset.mem_insert.mp hk with hkj | hk
    · subst k
      rw [hintElimInsert_lift, hPivot, one_smul, hintElimKernel]
      calc
        E.lift (A (Pi.single j 1)) + (Pi.single j 1 + E.lift (A (Pi.single j 1))) =
          Pi.single j 1 + (E.lift (A (Pi.single j 1)) + E.lift (A (Pi.single j 1))) := by abel
        _ = _ := by rw [hintVec_add_self, add_zero]
    · rw [hintElimInsert_lift, hInv.killed k hk]
      simpa using hInv.fixed k hk
  · intro k hk
    rcases Finset.mem_insert.mp hk with hkj | hk
    · subst k
      rw [hintElimInsert_residual, hPivot, one_smul, hintVec_add_self]
    · rw [hintElimInsert_residual, hInv.killed k hk]
      simp
  · intro v k hk
    have hk' : k ≠ j ∧ k ∉ done := by simpa only [Finset.mem_insert, not_or] using hk
    rw [hintElimInsert_lift]
    simp [hintElimKernel, hInv.support v k hk'.2, hInv.support _ k hk'.2,
      Pi.single_apply, hk'.1]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintFindPivotList {a : ℕ} (v : HintVec a) : List (Fin a) → Option (Fin a)
  | [] => none
  | p :: rest => if v p = 1 then some p else hintFindPivotList v rest

def hintFindPivot {a : ℕ} (v : HintVec a) : Option (Fin a) := hintFindPivotList v (List.finRange a)

theorem hintFindPivotList_some {a : ℕ} (v : HintVec a) (L : List (Fin a)) (p : Fin a)
    (hFind : hintFindPivotList v L = some p) : v p = 1 := by
  induction L with
  | nil => simp [hintFindPivotList] at hFind
  | cons q rest ih =>
      by_cases hq : v q = 1
      · simp only [hintFindPivotList, if_pos hq] at hFind
        exact (Option.some.inj hFind) ▸ hq
      · apply ih
        simpa only [hintFindPivotList, if_neg hq] using hFind

theorem hintFindPivotList_none {a : ℕ} (v : HintVec a) (L : List (Fin a))
    (hFind : hintFindPivotList v L = none) : ∀ p ∈ L, v p ≠ 1 := by
  induction L with
  | nil => simp
  | cons q rest ih =>
      have hq : v q ≠ 1 := by
        intro hq
        simp only [hintFindPivotList, if_pos hq] at hFind
        contradiction
      have hRest : hintFindPivotList v rest = none := by
        simpa only [hintFindPivotList, if_neg hq] using hFind
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · simpa only [hp] using hq
      · exact ih hRest p hp

theorem hintFindPivot_some {a : ℕ} (v : HintVec a) (p : Fin a)
    (hFind : hintFindPivot v = some p) : v p = 1 := hintFindPivotList_some v _ p hFind

theorem hintFindPivot_none {a : ℕ} (v : HintVec a) (hFind : hintFindPivot v = none) : v = 0 := by
  funext p
  have hNot := hintFindPivotList_none v (List.finRange a) hFind p (by simp)
  have hTwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact (hTwo (v p)).resolve_right hNot

def hintElimScan {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) : List (Fin h) → Sum (HintVec h) (HintElimState a h)
  | [] => .inr E
  | j :: rest =>
      match hintFindPivot (E.residual (A (Pi.single j 1))) with
      | none => .inl (hintElimKernel A E j)
      | some p => hintElimScan A (hintElimInsert A E j p) rest

def HintElimOutcomeSpec {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (done : Finset (Fin h)) : Sum (HintVec h) (HintElimState a h) → Prop
  | .inl k => k ≠ 0 ∧ A k = 0
  | .inr E => HintElimInvariant A done E

theorem hintElimScan_spec {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) (L : List (Fin h)) :
    ∀ (done : Finset (Fin h)) (E : HintElimState a h), HintElimInvariant A done E →
      L.Nodup → (∀ j ∈ L, j ∉ done) →
      HintElimOutcomeSpec A (done ∪ L.toFinset) (hintElimScan A E L) := by
  classical
  induction L with
  | nil =>
      intro done E hInv _ _
      simpa only [List.toFinset_nil, Finset.union_empty, hintElimScan, HintElimOutcomeSpec] using hInv
  | cons j rest ih =>
      intro done E hInv hNodup hDisjoint
      have hj : j ∉ done := hDisjoint j (by simp)
      have hRest := List.nodup_cons.mp hNodup
      cases hPivot : hintFindPivot (E.residual (A (Pi.single j 1))) with
      | none =>
          rw [hintElimScan, hPivot]
          exact ⟨hintElimKernel_nonzero A done E j hInv hj,
            (hintElimKernel_image A done E j hInv).trans (hintFindPivot_none _ hPivot)⟩
      | some p =>
          have hInv' := hintElimInsert_invariant A done E j p hInv (hintFindPivot_some _ p hPivot)
          have hDisjoint' : ∀ k ∈ rest, k ∉ insert j done := by
            intro k hk hIn
            rcases Finset.mem_insert.mp hIn with hkj | hkd
            · exact hRest.1 (hkj ▸ hk)
            · exact hDisjoint k (by simp [hk]) hkd
          have hDone : insert j done ∪ rest.toFinset = done ∪ (j :: rest).toFinset := by
            ext k
            simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
            tauto
          rw [hintElimScan, hPivot]
          simpa only [hDone] using ih (insert j done) (hintElimInsert A E j p) hInv' hRest.2 hDisjoint'

def hintElimBuild {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) : Sum (HintVec h) (HintElimState a h) :=
  hintElimScan A (hintElimInit a h) (List.finRange h)

theorem hintElimBuild_spec {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) :
    HintElimOutcomeSpec A Finset.univ (hintElimBuild A) := by
  have hDone : (∅ : Finset (Fin h)) ∪ (List.finRange h).toFinset = Finset.univ := by ext j; simp
  have hh := hintElimScan_spec A (List.finRange h) ∅ (hintElimInit a h)
    (hintElimInit_invariant A) (List.nodup_finRange h) (by intro j _; simp)
  simpa only [hDone, hintElimBuild] using hh

theorem hintVec_expand {h : ℕ} (x : HintVec h) :
    x = ∑ j : Fin h, x j • Pi.single j (1 : ZMod 2) := by
  classical
  funext k
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem hintElim_left_inverse {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (hInv : HintElimInvariant A Finset.univ E) (x : HintVec h) :
    E.lift (A x) = x := by
  classical
  calc
    E.lift (A x) = E.lift (A (∑ j : Fin h, x j • Pi.single j 1)) := by rw [← hintVec_expand x]
    _ = ∑ j : Fin h, x j • E.lift (A (Pi.single j 1)) := by simp only [map_sum, map_smul]
    _ = ∑ j : Fin h, x j • Pi.single j 1 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hInv.fixed j (Finset.mem_univ j)]
    _ = x := (hintVec_expand x).symm

theorem hintElim_solution_iff {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (hInv : HintElimInvariant A Finset.univ E) (v : HintVec a) :
    (∃ x, A x = v) ↔ E.residual v = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    have hh := hInv.decompose (A x)
    rw [hintElim_left_inverse A E hInv x] at hh
    exact add_left_cancel (hh.trans (add_zero (A x)).symm)
  · intro hZero
    refine ⟨E.lift v, ?_⟩
    simpa only [hZero, add_zero] using hInv.decompose v

theorem hintElim_solution_unique {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (E : HintElimState a h) (hInv : HintElimInvariant A Finset.univ E)
    (v : HintVec a) (hZero : E.residual v = 0) : ∃! x, A x = v := by
  refine ⟨E.lift v, ?_, ?_⟩
  · simpa only [hZero, add_zero] using hInv.decompose v
  · intro x hx
    rw [← hintElim_left_inverse A E hInv x, hx]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintSolve {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) (v : HintVec a) : Option (HintVec h) :=
  match hintElimBuild A with
  | .inl _ => none
  | .inr E =>
      match hintFindPivot (E.residual v) with
      | none => some (E.lift v)
      | some _ => none

theorem hintKernel_no_unique {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (k : HintVec h) (hNonzero : k ≠ 0) (hKernel : A k = 0) (v : HintVec a) :
    ¬ ∃! x, A x = v := by
  rintro ⟨x, hx, hUnique⟩
  have hOther : A (x + k) = v := by rw [map_add, hx, hKernel, add_zero]
  have hEq := hUnique (x + k) hOther
  exact hNonzero (add_left_cancel (hEq.trans (add_zero x).symm))

/-- The algorithm returns exactly the unique member of the affine fiber.
    A nontrivial kernel, inconsistency and an empty fiber all return none. -/
theorem hintSolve_spec {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (v : HintVec a) (z : HintVec h) :
    hintSolve A v = some z ↔ A z = v ∧ ∀ x, A x = v → x = z := by
  have hSpec := hintElimBuild_spec A
  cases hBuild : hintElimBuild A with
  | inl k =>
      rw [hBuild] at hSpec
      change k ≠ 0 ∧ A k = 0 at hSpec
      have hNoUnique := hintKernel_no_unique A k hSpec.1 hSpec.2 v
      constructor
      · intro hSome
        simp only [hintSolve, hBuild] at hSome
        contradiction
      · rintro ⟨hz, hUnique⟩
        exact (hNoUnique ⟨z, hz, hUnique⟩).elim
  | inr E =>
      rw [hBuild] at hSpec
      change HintElimInvariant A Finset.univ E at hSpec
      cases hPivot : hintFindPivot (E.residual v) with
      | none =>
          have hZero := hintFindPivot_none _ hPivot
          have hSolution : A (E.lift v) = v := by
            simpa only [hZero, add_zero] using hSpec.decompose v
          simp only [hintSolve, hBuild, hPivot, Option.some.injEq]
          constructor
          · intro hEq
            refine ⟨by rw [← hEq]; exact hSolution, ?_⟩
            intro x hx
            calc
              x = E.lift (A x) := (hintElim_left_inverse A E hSpec x).symm
              _ = E.lift v := congrArg E.lift hx
              _ = z := hEq
          · rintro ⟨_, hUnique⟩
            exact hUnique _ hSolution
      | some p =>
          constructor
          · intro hSome
            simp only [hintSolve, hBuild, hPivot] at hSome
            contradiction
          · rintro ⟨hz, _⟩
            have hZero := (hintElim_solution_iff A E hSpec v).mp ⟨z, hz⟩
            have hOne := hintFindPivot_some (E.residual v) p hPivot
            rw [hZero] at hOne
            exact (zero_ne_one hOne).elim

theorem hintSolve_exists_iff {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a) (v : HintVec a) :
    (∃ z, hintSolve A v = some z) ↔ ∃! x, A x = v := by
  constructor
  · rintro ⟨z, hSome⟩
    exact ⟨z, (hintSolve_spec A v z).mp hSome⟩
  · rintro ⟨z, hz, hUnique⟩
    exact ⟨z, (hintSolve_spec A v z).mpr ⟨hz, hUnique⟩⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSolve_spec


