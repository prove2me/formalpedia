-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
-- name    : LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:59:25.547679+00:00
-- url     : https://prove2.me/theorems/5f165f1a-fce6-43a5-b3d9-5a6fae61d874
-- title:
--   Hom Localization Differential for localized persistent commutative algebra
-- statement:
--   This bundle supplies hom Localization Differential for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual localization map, with its numerator factor at every coordinate-power stage. No denominator cancellation is assumed.
--   - Each weighted Koszul-Hom entry becomes the signed genuine localization entry under the actual column cocones.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HomLocalizationDifferential.lean, selected declarations in lines 16–112; source SHA-256 b63bf51cbd558018bffbbf195bfc9734b795ed7fc28d0f785e66e51a2051fa0d; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem invertedMonomial_mul_sdiff (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    invertedMonomial k K F * invertedMonomial k K (G \ F) = invertedMonomial k K G := by
  have hd : Disjoint F (G \ F) := by
    apply Finset.disjoint_left.mpr
    intro j hjF hjG
    exact (Finset.mem_sdiff.mp hjG).2 hjF
  unfold invertedMonomial
  rw [← Finset.prod_union hd, Finset.union_sdiff_of_subset hFG]

/-- The actual localization map, with its numerator factor at every
coordinate-power stage. No denominator cancellation is assumed. -/
theorem faceLocalizationMap_stage (K : Complex V) (F G : Finset V) (hFG : F ⊆ G)
    (n : ℕ) (r : FaceRing k K) :
    localizationMap k K F G hFG (localizationTelescopeStage (invertedMonomial k K F) n r) =
      localizationTelescopeStage (invertedMonomial k K G) n
        (invertedMonomial k K (G \ F) ^ (n + 1) * r) := by
  have hs : localizationMap k K F G hFG
      (localizationTelescopeStage (invertedMonomial k K F) n r) *
        algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          (invertedMonomial k K F ^ (n + 1)) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G) r := by
    rw [← localizationMap_base k K F G hFG, ← map_mul,
      localizationTelescopeStage_eq, IsLocalization.mk'_spec, localizationMap_base]
  rw [localizationTelescopeStage_eq (invertedMonomial k K G)]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change localizationMap k K F G hFG
      (localizationTelescopeStage (invertedMonomial k K F) n r) *
        algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          (invertedMonomial k K G ^ (n + 1)) = _
  have hp : algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
      (invertedMonomial k K G ^ (n + 1)) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
        (invertedMonomial k K F ^ (n + 1)) *
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
        (invertedMonomial k K (G \ F) ^ (n + 1)) := by
    calc
      _ = algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          ((invertedMonomial k K F * invertedMonomial k K (G \ F)) ^ (n + 1)) :=
        congrArg (fun t : FaceRing k K =>
          algebraMap (FaceRing k K) (LocalizedFaceRing k K G) (t ^ (n + 1)))
          (invertedMonomial_mul_sdiff k K F G hFG).symm
      _ = _ := by rw [mul_pow, map_mul]
  rw [hp, ← mul_assoc, hs, ← map_mul, mul_comm r]

noncomputable def ambientFaceRingStage (K : Complex V) (F : Finset V) (n : ℕ) :
    ModuleCat.of (MvPolynomial V k) (FaceRing k K) ⟶ ambientLocalizedModule k K F :=
  (restrictedFaceRingIso k K).inv ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).map
      (ModuleCat.ofHom (localizationTelescopeStage (invertedMonomial k K F) n))



theorem coordinateKoszulCoefficient_power (rank : V ↪ ℕ) (n : ℕ) (F G : Finset V) :
    coordinateKoszulCoefficient k rank n F G =
      MvPolynomial.C (cechCoefficient k rank F G) *
        polynomialFaceMonomial k (G \ F) ^ (n + 1) := by
  unfold coordinateKoszulCoefficient polynomialFaceMonomial
  rw [Finset.prod_pow]

/-- Each weighted Koszul-Hom entry becomes the signed genuine localization
entry under the actual column cocones. -/
theorem ambientCechEntry_stage (rank : V ↪ ℕ) (K : Complex V)
    (n : ℕ) (F G : Finset V) (r : FaceRing k K) :
    ambientCechEntry k rank K F G (ambientFaceRingStage k K F n r) =
      ambientFaceRingStage k K G n (coordinateKoszulCoefficient k rank n F G • r) := by
  classical
  by_cases hFG : F ⊆ G
  · simp only [ambientCechEntry, ambientLocalizationEntry, dif_pos hFG,
      LinearMap.smul_apply]
    rw [coordinateKoszulCoefficient_power, mul_smul, map_smul,
      polynomialFaceMonomial_smul]
    apply congrArg (fun x : ambientLocalizedModule k K G =>
      (MvPolynomial.C (cechCoefficient k rank F G) : MvPolynomial V k) • x)
    exact faceLocalizationMap_stage k K F G hFG n r
  · have hz := cechCoefficient_zero_of_not_subset k rank F G hFG
    simp [ambientCechEntry, coordinateKoszulCoefficient, hz]

theorem ambientCechDifferential_stage (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (p n : ℕ) (y : CechSlot T p → FaceRing k K) :
    ambientCechDifferential k rank K T p
        (fun F => ambientFaceRingStage k K F.1 n (y F)) =
      fun G => ambientFaceRingStage k K G.1 n
        (coordinateKoszulHomDifferential k rank n T p
          (ModuleCat.of (MvPolynomial V k) (FaceRing k K)) y G) := by
  classical
  funext G
  change (∑ F : CechSlot T p, ambientCechEntry k rank K F.1 G.1
    (ambientFaceRingStage k K F.1 n (y F))) =
      ambientFaceRingStage k K G.1 n
        (∑ F : CechSlot T p, coordinateKoszulCoefficient k rank n F.1 G.1 • y F)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F _
  exact ambientCechEntry_stage k rank K n F.1 G.1 (y F)

end LPCA


