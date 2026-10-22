-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
-- name    : LPCA_Solutions_LPCA_FinitePiGrading_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:38.590635+00:00
-- url     : https://prove2.me/theorems/bbac92a9-82ed-47c4-8580-70a41e683d1b
-- title:
--   Finite Pi Grading for localized persistent commutative algebra
-- statement:
--   This bundle supplies finite Pi Grading for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Finiteness of the product index ensures that the union of the supports of all coordinate decompositions is still finite.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FinitePiGrading.lean, selected declarations in lines 14–70; source SHA-256 c6e08e6cc1f43909cdfacc41c5fe820126922f9139b9822fd97a18596f2331f7; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false

namespace LPCA

universe u

variable {R : Type u} [Ring R]
variable {I J : Type u} [Fintype I] [DecidableEq I] [DecidableEq J]
variable {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

abbrev finitePiPiece (A : ∀ i, J → Submodule R (M i)) (a : J) :
    Submodule R (∀ i, M i) := Submodule.pi Set.univ (fun i => A i a)

theorem finitePiPieces_iSupIndep (A : ∀ i, J → Submodule R (M i))
    (hA : ∀ i, iSupIndep (A i)) : iSupIndep (finitePiPiece A) := by
  intro a
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  funext i
  apply Submodule.disjoint_def.mp (hA i a) (x i)
  · exact (Submodule.mem_pi.mp hx) i (Set.mem_univ i)
  · have hl : (⨆ b, ⨆ (_ : b ≠ a), finitePiPiece A b) ≤
        (⨆ b, ⨆ (_ : b ≠ a), A i b).comap (LinearMap.proj i) := by
      apply iSup_le
      intro b
      apply iSup_le
      intro hba y hy
      exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hba
        ((Submodule.mem_pi.mp hy) i (Set.mem_univ i)))
    exact hl hy

/-- Finiteness of the product index ensures that the union of the supports
of all coordinate decompositions is still finite. -/
theorem finitePiPieces_iSup_eq_top (A : ∀ i, J → Submodule R (M i))
    (hA : ∀ i, (⨆ a, A i a) = ⊤) : (⨆ a, finitePiPiece A a) = ⊤ := by
  have hsingle : ∀ (i : I) (z : M i),
      Pi.single i z ∈ ⨆ a, finitePiPiece A a := by
    intro i z
    have hl : (⊤ : Submodule R (M i)) ≤
        (⨆ a, finitePiPiece A a).comap (LinearMap.single R M i) := by
      rw [← hA i]
      apply iSup_le
      intro a y hy
      apply Submodule.mem_iSup_of_mem a
      apply Submodule.mem_pi.mpr
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using hy
      · simpa [LinearMap.single_apply, Pi.single_apply, hji, Ne.symm hji] using
          (Submodule.zero_mem (A j a))
    exact hl (Submodule.mem_top)
  apply top_unique
  intro y _
  have hy : (∑ i, Pi.single i (y i)) = y := by
    funext i
    simp
  rw [← hy]
  apply Submodule.sum_mem
  intro i _
  exact hsingle i (y i)

theorem finitePiGradingIsInternal (A : ∀ i, J → Submodule R (M i))
    (hA : ∀ i, DirectSum.IsInternal (A i)) : DirectSum.IsInternal (finitePiPiece A) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (finitePiPieces_iSupIndep A (fun i => (hA i).submodule_iSupIndep))
    (finitePiPieces_iSup_eq_top A (fun i => (hA i).submodule_iSup_eq_top))

end LPCA


