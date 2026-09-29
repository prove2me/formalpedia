-- Prove2me | Definitions.Def_mme_CW_canonical_grading
-- name    : mme_CW_canonical_grading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-02T19:15:06.349137+00:00
-- url     : https://prove2.me/theorems/e788c218-800e-4f14-abfe-de524fd32249
-- statement:
--   The canonical 3-grading on the Coppersmith-Winograd tensor object $\mathrm{CWObj}\,K\,q$. Each of the three modes is graded into three type-classes: class $0$ is the span of the left-boundary basis vector $e_0$ (1-dimensional), class $1$ is the span of the middle basis vectors $\{e_1, \dots, e_q\}$ ($q$-dimensional), and class $2$ is the span of the right-boundary basis vector $e_{q+1}$ (1-dimensional). This is a type-grading on the underlying tensor space; combined with the CW tensor $T_q$ it provides the laser-method scaffolding for the analysis in Coppersmith-Winograd 1990 / Wigderson-Zuiddam.
--
--   Provides: `typeOfCW`, `cwGradePiece`, `mem_cwGradePiece_iff`, `cwProject`, `isInternal_cwGradePiece`, and the bundled `cwCanonicalGrading q : (CWObj K q).TypeGrading 3`, plus simp lemmas. Sorry-free.
-- source:
--   Coppersmith-Winograd 1990 §6; Wigderson-Zuiddam §6 laser method

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_type_grading

/-! # Canonical 3-grading on `CWObj K q`

A concrete `TypeGrading` on the CW tensor object: class 0 = span of `e_0`
(left boundary), class 1 = span of `{e_1, …, e_q}` (middle), class 2 = span
of `e_{q+1}` (right boundary). Per-mode the same grading on each of the three
modes (since `CWSpace K q i = Fin (q+2) → K` for all `i : Fin 3`).

Re-uses the gradePiece / IsInternal machinery from
`Solutions/Sol_mme_CW_laser_witness_wz.lean` (which is platform-PROVED, so the
construction is validated). Exposed here as a public Def so that the per-s MM
witnesses (`mme_CW_block_is_MM_at_*`) can be stated against a *concrete*
grading without needing a per-theorem canonical-shape hypothesis.

**Status.** Sorry-free; LOCAL ONLY (not yet uploaded to Prove2Me). -/

universe u

open MME PiTensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K]

/-- The "type" of an index `k : Fin (q+2)`: `0` for the left boundary `0`,
`2` for the right boundary `q+1`, `1` for anything in between. -/
def typeOfCW (q : ℕ) (k : Fin (q+2)) : Fin 3 :=
  if k.val = 0 then 0
  else if k.val = q + 1 then 2
  else 1

/-- The `α`-th piece of the canonical 3-grading on `Fin (q+2) → K`. -/
def cwGradePiece (K : Type u) [Field K] (q : ℕ) (α : Fin 3) :
    Submodule K (Fin (q+2) → K) :=
  Submodule.span K (Set.range (fun k : {k : Fin (q+2) // typeOfCW q k = α} =>
    (Pi.single (k : Fin (q+2)) (1 : K) : Fin (q+2) → K)))

lemma mem_cwGradePiece_iff (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    f ∈ cwGradePiece K q α ↔ ∀ k : Fin (q+2), typeOfCW q k ≠ α → f k = 0 := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction (p := fun g _ => ∀ k, typeOfCW q k ≠ α → g k = 0)
      ?_ ?_ ?_ ?_ hf
    · rintro g ⟨k, rfl⟩ j hj
      by_cases hjk : j = (k : Fin (q+2))
      · subst hjk; exact absurd k.2 hj
      · simp [Pi.single_apply, if_neg hjk]
    · intro k _; rfl
    · intro x y _ _ hx hy k hk
      simp [hx k hk, hy k hk]
    · intro c x _ hx k hk
      simp [hx k hk]
  · intro h
    have hsum :
        f = ∑ k ∈ (Finset.univ.filter (fun k : Fin (q+2) => typeOfCW q k = α)),
                f k • (Pi.single k (1 : K) : Fin (q+2) → K) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : typeOfCW q j = α
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
            simp [Pi.single_apply, if_neg (Ne.symm hk)]
          rw [this]; ring
        · intro hjmem
          exfalso; apply hjmem
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      · symm
        rw [h j hj]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkj : j ≠ k := by
          intro heq
          rw [heq] at hj
          exact hj hk.2
        have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
          simp [Pi.single_apply, if_neg hkj]
        rw [this]; ring
    rw [hsum]
    apply Submodule.sum_mem
    intro k hk
    rw [Finset.mem_filter] at hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨k, hk.2⟩, rfl⟩

lemma single_mem_cwGradePiece (q : ℕ) (k : Fin (q+2)) :
    (Pi.single k 1 : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q k) := by
  apply Submodule.subset_span
  exact ⟨⟨k, rfl⟩, rfl⟩

/-- Projection helper. -/
def cwProject (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) : Fin (q+2) → K :=
  fun k => if typeOfCW q k = α then f k else 0

lemma cwProject_mem (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    cwProject q α f ∈ cwGradePiece K q α := by
  rw [mem_cwGradePiece_iff]
  intro k hk
  simp [cwProject, hk]

lemma cwSum_project (q : ℕ) (f : Fin (q+2) → K) :
    (∑ α : Fin 3, cwProject q α f) = f := by
  funext k
  simp only [Finset.sum_apply, cwProject]
  have : ∑ α : Fin 3, (if typeOfCW q k = α then f k else 0) = f k := by
    rw [Finset.sum_eq_single (typeOfCW q k)]
    · simp
    · intros α _ hα
      rw [if_neg (Ne.symm hα)]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact this

lemma isInternal_cwGradePiece (q : ℕ) :
    DirectSum.IsInternal (fun α : Fin 3 => cwGradePiece K q α) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
    intro s v hv hsum α hα
    have hvα : ∀ k, typeOfCW q k ≠ α → v α k = 0 :=
      (mem_cwGradePiece_iff q α (v α)).mp (hv α hα)
    funext k
    have hk_sum : (∑ β ∈ s, v β) k = 0 := by rw [hsum]; rfl
    rw [Finset.sum_apply] at hk_sum
    by_cases hk : typeOfCW q k = α
    · have hall : ∀ β ∈ s, β ≠ α → v β k = 0 := by
        intro β hβ hβne
        have hvβ : ∀ j, typeOfCW q j ≠ β → v β j = 0 :=
          (mem_cwGradePiece_iff q β (v β)).mp (hv β hβ)
        apply hvβ
        rw [hk]; exact hβne.symm
      rw [← Finset.add_sum_erase s _ hα] at hk_sum
      have hzero : (∑ β ∈ s.erase α, v β k) = 0 := by
        apply Finset.sum_eq_zero
        intro β hβ
        rw [Finset.mem_erase] at hβ
        exact hall β hβ.2 hβ.1
      rw [hzero, add_zero] at hk_sum
      exact hk_sum
    · exact hvα k hk
  · rw [eq_top_iff]
    intro f _
    rw [← cwSum_project q f]
    apply Submodule.sum_mem
    intro α _
    exact Submodule.mem_iSup_of_mem α (cwProject_mem q α f)

/-- The canonical 3-grading on `CWObj K q`. -/
noncomputable def cwCanonicalGrading (q : ℕ) : (CWObj K q).TypeGrading 3 where
  decomp := fun i α =>
    match i with
    | ⟨0, _⟩ => cwGradePiece K q α
    | ⟨1, _⟩ => cwGradePiece K q α
    | ⟨2, _⟩ => cwGradePiece K q α
  is_internal := fun i => by
    match i with
    | ⟨0, _⟩ => exact isInternal_cwGradePiece q
    | ⟨1, _⟩ => exact isInternal_cwGradePiece q
    | ⟨2, _⟩ => exact isInternal_cwGradePiece q

@[simp] lemma typeOfCW_zero (q : ℕ) :
    typeOfCW q (⟨0, by omega⟩ : Fin (q+2)) = 0 := by
  simp [typeOfCW]

@[simp] lemma typeOfCW_qPlusOne (q : ℕ) :
    typeOfCW q (⟨q+1, by omega⟩ : Fin (q+2)) = 2 := by
  simp [typeOfCW]

@[simp] lemma typeOfCW_middle (q : ℕ) (i : Fin q) :
    typeOfCW q (⟨i.val + 1, by omega⟩ : Fin (q+2)) = 1 := by
  simp [typeOfCW]
  intro h
  omega

end MME


