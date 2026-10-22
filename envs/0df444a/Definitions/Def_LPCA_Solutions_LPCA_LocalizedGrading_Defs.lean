-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
-- name    : LPCA_Solutions_LPCA_LocalizedGrading_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:25:15.541548+00:00
-- url     : https://prove2.me/theorems/8dbce2e9-9f89-4c3e-beb1-37d5e6f71061
-- title:
--   Localized Grading for localized persistent commutative algebra
-- statement:
--   This bundle supplies localized Grading for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Distinct integer degrees are independent inside the actual localization. For each nonzero piece, evaluation on its supporting face and extraction of the corresponding Laurent coefficient annihilate every other degree.
--   - The homogeneous pieces form an exhaustive internal direct sum of the actual localization, rather than a family of abstract one-dimensional models.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizedGrading.lean, selected declarations in lines 14–64; source SHA-256 110b2bb0c6ed3e7bd33988eb64364c34d5ab1197996b83fbfee828c657456f9f; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Distinct integer degrees are independent inside the actual localization.
For each nonzero piece, evaluation on its supporting face and extraction of
the corresponding Laurent coefficient annihilate every other degree. -/
theorem localizedPieces_iSupIndep (K : Complex V) (F : Finset V) :
    iSupIndep (localizedPiece k K F) := by
  classical
  intro a
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  by_cases ha : LocalizationCriterion K F a
  · let G := positiveSupport a ∪ F
    have hG : G ∈ K.faces := ha.2
    have hFG : F ⊆ G := Finset.subset_union_right
    let ell : LocalizedFaceRing k K F →ₗ[k] k :=
      (laurentDegreeCoefficient k a).comp (laurentLocalizationLinearMap k K G hG F hFG)
    have hker : (⨆ b, ⨆ (_ : b ≠ a), localizedPiece k K F b) ≤ LinearMap.ker ell := by
      apply iSup_le
      intro b
      apply iSup_le
      intro hba z hz
      exact laurentDegreeCoefficient_piece_ne k K G hG F hFG a b (Ne.symm hba) hz
    have hzero : ell x = 0 := hker hy
    obtain ⟨m, N, hm, hsupp⟩ := exists_positive_denominator_rep F a ha.1
    have hline := localizedPiece_eq_span_of_rep k K F a m N hm
    rw [hline] at hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    have hone : ell (localizedMonomial k K F m N) = 1 := by
      change laurentDegreeCoefficient k a
        (laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N)) = 1
      rw [laurentLocalizationMap_monomial k K G hG F hFG a m N
        (by simpa only [hsupp] using (Finset.Subset.refl G)) hm]
      change (AddMonoidAlgebra.single a (1 : k)).coeff a = 1
      simp
    rw [← hc, map_smul, hone, smul_eq_mul, mul_one] at hzero
    calc
      x = c • localizedMonomial k K F m N := hc.symm
      _ = (0 : k) • localizedMonomial k K F m N := by rw [hzero]
      _ = algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
          (algebraMap k (FaceRing k K) (0 : k)) * localizedMonomial k K F m N :=
        localized_smul_base k K F 0 _
      _ = 0 := by rw [map_zero, map_zero, zero_mul]
  · have hb := (localizedPiece_eq_bot_iff k K F a).mpr ha
    rw [hb] at hx
    exact hx

/-- The homogeneous pieces form an exhaustive internal direct sum of the
actual localization, rather than a family of abstract one-dimensional models. -/
theorem localizedGradingIsInternal (K : Complex V) (F : Finset V) :
    DirectSum.IsInternal (localizedPiece k K F) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (localizedPieces_iSupIndep k K F) (localizedPieces_iSup_eq_top k K F)



end LPCA


