-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalSingleSectionReciprocalPatchesAndChartEquivalencesDataExplicitEquationDegreeV220261019
-- name    : MazurTransfer_Order13MixedOriginalSingleSectionReciprocalPatchesAndChartEquivalencesDataExplicitEquationDegreeV220261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T06:08:55.799993+00:00
-- url     : https://prove2.me/theorems/f8a6b8c5-20ed-4b1a-bee4-5660320ffd7a
-- title:
--   Original mixed reciprocal patches and chart equivalences
-- statement:
--   The original reciprocal patches, fraction-field embeddings and chosen ordinary/reciprocal chart algebra equivalences over integral coefficient rings, with their original complete types and chosen values. Named downstream consumer: the actual two affine finite-map charts.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original single-section and inverse-parameter reciprocal
patches, fraction-field injections and integral-domain chart equivalences.
Named downstream consumer: the actual single-section and inverse finite
scheme atlases used by the degree-three FiniteMapData construction.
Original per-file headers and attribution are retained below.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_mixed_single_section_reciprocal_recovery
import Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_both_field_chart_domains
section
universe u
namespace MazurTransfer.MixedQuadraticEquationIrreducible
theorem ordinary_field_isDomain (K : Type u) [Field K] :
    IsDomain (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K) :=
  MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains.1 K
end MazurTransfer.MixedQuadraticEquationIrreducible
namespace MazurTransfer.Order13MixedQuadraticFieldChartDomains
theorem reciprocal_field_isDomain (K : Type u) [Field K] :
    IsDomain (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K) :=
  MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains.2 K
end MazurTransfer.Order13MixedQuadraticFieldChartDomains
namespace MazurTransfer.MixedQuadraticEquationIrreducible
open Polynomial MixedQuadraticCoordinateJacobian
variable (R : Type u) [CommRing R] [IsDomain R]
theorem equation_natDegree (h f : Polynomial R) : (equation R h f).natDegree = 2 := by
  unfold equation
  rw [natDegree_sub_C]
  calc
    _ = natDegree (X ^ 2 : Polynomial (Polynomial R)) := by
      apply natDegree_add_eq_left_of_natDegree_lt
      calc
        natDegree (C h * X : Polynomial (Polynomial R)) ≤ natDegree (C h) + natDegree X := natDegree_mul_le
        _ = 1 := by simp
        _ < natDegree (X ^ 2 : Polynomial (Polynomial R)) := by simp
    _ = 2 := by simp

end MazurTransfer.MixedQuadraticEquationIrreducible
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the injective localized inclusion of the actual parameter
subalgebra, with recovered x,y coordinates satisfying the literal mixed equation.
Named downstream consumer: the actual D(t) affine-chart isomorphism in the
single-section complement comparison. No full complement is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

abbrev parameterLocalization := Localization.Away (parameterElement R)
abbrev ordinaryParameterLocalization := Localization.Away (t R)

def pElement : candidateAlgebra R := ⟨p R, Algebra.subset_adjoin (by simp)⟩
def qElement : candidateAlgebra R := ⟨q R, Algebra.subset_adjoin (by simp)⟩

def inclusion : candidateAlgebra R →ₐ[R] ordinaryCoordinateRing R where
  __ := (candidateAlgebra R).val.toRingHom
  commutes' r := by
    change aeval (t R) (C r) = _
    exact aeval_C _ _

theorem parameterElement_coe : (parameterElement R : ordinaryCoordinateRing R) = t R := by
  change aeval (t R) X = t R
  exact aeval_X _

theorem inclusion_parameter : inclusion R (parameterElement R) = t R := by
  change aeval (t R) X = t R
  exact aeval_X _

def localizedInclusion : parameterLocalization R →ₐ[R] ordinaryParameterLocalization R := by
  letI : IsLocalization.Away (inclusion R (parameterElement R))
      (ordinaryParameterLocalization R) := by
    rw [inclusion_parameter]
    infer_instance
  exact IsLocalization.Away.mapₐ _ _ (inclusion R) (parameterElement R)

theorem localizedInclusion_algebraMap (b : candidateAlgebra R) :
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (b : ordinaryCoordinateRing R) := by
  simp [localizedInclusion, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    IsLocalization.map_eq, inclusion]

theorem localizedInclusion_injective : Function.Injective (localizedInclusion R) := by
  letI : IsLocalization.Away (inclusion R (parameterElement R))
      (ordinaryParameterLocalization R) := by
    rw [inclusion_parameter]
    infer_instance
  exact IsLocalization.Away.mapₐ_injective_of_injective (parameterElement R)
    (f := inclusion R) Subtype.val_injective

theorem localizedInclusion_invSelf :
    localizedInclusion R (IsLocalization.Away.invSelf (parameterElement R)) =
      IsLocalization.Away.invSelf (t R) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (t R)
    (S := ordinaryParameterLocalization R)
  apply hu.mul_right_inj.mp
  calc
    _ = localizedInclusion R
        (algebraMap (candidateAlgebra R) (parameterLocalization R) (parameterElement R) *
          IsLocalization.Away.invSelf (parameterElement R)) := by
      rw [map_mul, localizedInclusion_algebraMap, parameterElement_coe]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (t R)).symm

def recoveredX : parameterLocalization R :=
  algebraMap (candidateAlgebra R) (parameterLocalization R) (pElement R) *
    IsLocalization.Away.invSelf (parameterElement R)

def recoveredY : parameterLocalization R :=
  algebraMap (candidateAlgebra R) (parameterLocalization R) (parameterElement R) -
    recoveredX R ^ 3 - recoveredX R ^ 2 - 1

theorem localizedInclusion_recoveredX :
    localizedInclusion R (recoveredX R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) := by
  rw [recoveredX, map_mul, localizedInclusion_algebraMap, localizedInclusion_invSelf]
  change algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R * t R) * _ = _
  rw [map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

theorem localizedInclusion_recoveredY :
    localizedInclusion R (recoveredY R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (yCoordinate R) := by
  rw [recoveredY, map_sub, map_sub, map_sub, map_pow, map_pow, map_one,
    localizedInclusion_algebraMap, parameterElement_coe, localizedInclusion_recoveredX]
  change algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R) -
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) ^ 3 -
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) ^ 2 - 1 = _
  simp only [t,map_add,map_pow,map_one]
  ring

theorem recovered_equation : recoveredY R ^ 2 +
    (recoveredX R ^ 3 + recoveredX R ^ 2 + 1) * recoveredY R -
    recoveredX R * (recoveredX R + 1) = 0 := by
  apply localizedInclusion_injective R
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero,
    localizedInclusion_recoveredX, localizedInclusion_recoveredY]
  have h := congrArg
    (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)) (ordinary_relation R)
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at h
  exact h

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.localizedInclusion_injective
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recovered_equation

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact unit-ideal and principal-open covers of the actual
ordinary coordinate algebra and candidate single-section algebra.
Named downstream consumer: gluing the three actual localization comparisons.
No reciprocal comparison or full complement identification is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def infinityPatchElement : candidateAlgebra R :=
  pElement R * (pElement R + parameterElement R)

theorem ordinary_two_generator_unit_ideal :
    Ideal.span ({t R,p R + 1} : Set (ordinaryCoordinateRing R)) = ⊤ := by
  let I : Ideal (ordinaryCoordinateRing R) := Ideal.span {t R,p R + 1}
  have ht : t R ∈ I := Ideal.subset_span (by simp)
  have hk : p R + 1 ∈ I := Ideal.subset_span (by simp)
  have h2mem : (1 : ordinaryCoordinateRing R) ∈ I := by
    have hm := I.sub_mem hk (I.mul_mem_left (xCoordinate R) ht)
    have heq : p R + 1 - xCoordinate R * t R = 1 := by dsimp [p]; ring
    rwa [heq] at hm
  exact I.eq_top_of_isUnit_mem h2mem isUnit_one

theorem ordinary_two_principal_open_cover :
    PrimeSpectrum.basicOpen (t R) ⊔ PrimeSpectrum.basicOpen (p R + 1) = ⊤ := by
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr (ordinary_two_generator_unit_ideal R)
  simpa only [iSup_insert,iSup_singleton] using h

theorem candidate_three_generator_unit_ideal :
    Ideal.span ({parameterElement R,pElement R + 1,infinityPatchElement R} :
      Set (candidateAlgebra R)) = ⊤ := by
  let I : Ideal (candidateAlgebra R) :=
    Ideal.span {parameterElement R,pElement R + 1,infinityPatchElement R}
  have ht : parameterElement R ∈ I := Ideal.subset_span (by simp)
  have hk : pElement R + 1 ∈ I := Ideal.subset_span (by simp)
  have hr : infinityPatchElement R ∈ I := Ideal.subset_span (by simp)
  have h4 : (1 : candidateAlgebra R) ∈ I := by
    have hm := I.sub_mem (I.sub_mem hr (I.mul_mem_right (pElement R - 1) hk))
      (I.mul_mem_right (pElement R) ht)
    have heq : infinityPatchElement R - (pElement R + 1) * (pElement R - 1) -
        parameterElement R * pElement R = 1 := by dsimp [infinityPatchElement]; ring
    rwa [heq] at hm
  exact I.eq_top_of_isUnit_mem h4 isUnit_one

theorem candidate_three_principal_open_cover :
    PrimeSpectrum.basicOpen (parameterElement R) ⊔
      (PrimeSpectrum.basicOpen (pElement R + 1) ⊔
        PrimeSpectrum.basicOpen (infinityPatchElement R)) = ⊤ := by
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr (candidate_three_generator_unit_ideal R)
  simpa only [iSup_insert,iSup_singleton] using h

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinary_two_principal_open_cover
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidate_three_principal_open_cover

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact integral identities recovering reciprocal coordinates
from the mixed single-section parameter and the inverse of p.
Named downstream consumer: the actual reciprocal principal-patch comparison.
-/

noncomputable section
namespace MazurTransfer.Order13MixedSingleSectionReciprocalRecoveryIdentities
variable {A : Type*} [CommRing A]

theorem recovered_coordinate_identity (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    t * (t * u) ^ 3 - (1 + t * u + (t * u) ^ 3) = (1 + t * u) * u := by
  exact (MazurTransfer.mixed_single_section_reciprocal_recovery t p u hu htp).1

theorem recovered_reciprocal_equation (t p u : A) (hu : p * u = 1)
    (htp : t ^ 4 - p ^ 3 - p ^ 2 * t - t ^ 3 - p ^ 2 - p * t = 0) :
    ((1 + t * u) * u) ^ 2 + (1 + t * u + (t * u) ^ 3) * ((1 + t * u) * u) -
      ((t * u) ^ 4 + (t * u) ^ 5) = 0 := by
  exact (MazurTransfer.mixed_single_section_reciprocal_recovery t p u hu htp).2

universe u
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

theorem actual_parameter_quartic :
    t R ^ 4 - p R ^ 3 - p R ^ 2 * t R - t R ^ 3 - p R ^ 2 - p R * t R = 0 := by
  have h := candidate_equation R
  dsimp only [p]
  linear_combination (t R) ^ 2 * h

end MazurTransfer.Order13MixedSingleSectionReciprocalRecoveryIdentities
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalRecoveryIdentities.recovered_reciprocal_equation
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalRecoveryIdentities.actual_parameter_quartic

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the existing reciprocal principal-patch method to the mixed model.
Design boundary: the literal open D(w*(1+z)) around negative infinity and
regular parameter coordinates there, without inversion of two.
Named downstream consumer: the mixed single-section affine-complement atlas.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionReciprocalPatch
open Polynomial Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities Order13MixedQuadraticInfinitySections
variable (R : Type u) [CommRing R]

def denominator : reciprocalCoordinateRing R := wCoordinate R * (1 + zCoordinate R)
abbrev PatchRing := Localization.Away (denominator R)
def z : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (zCoordinate R)
def w : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (wCoordinate R)

theorem w_mul_one_add_z_isUnit : IsUnit (w R * (1 + z R)) := by
  change IsUnit (algebraMap (reciprocalCoordinateRing R) (PatchRing R) (wCoordinate R) *
    (1 + algebraMap (reciprocalCoordinateRing R) (PatchRing R) (zCoordinate R)))
  rw [← map_one (algebraMap (reciprocalCoordinateRing R) (PatchRing R)), ← map_add, ← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator R)

theorem w_isUnit : IsUnit (w R) := isUnit_of_mul_isUnit_left (w_mul_one_add_z_isUnit R)
theorem one_add_z_isUnit : IsUnit (1 + z R) := isUnit_of_mul_isUnit_right (w_mul_one_add_z_isUnit R)

def wInverse : PatchRing R := (1 + z R) * IsLocalization.Away.invSelf (denominator R)
def oneAddZInverse : PatchRing R := w R * IsLocalization.Away.invSelf (denominator R)

theorem w_mul_wInverse : w R * wInverse R = 1 := by
  rw [wInverse, ← mul_assoc]
  change algebraMap (reciprocalCoordinateRing R) (PatchRing R) (wCoordinate R) *
    (1 + algebraMap (reciprocalCoordinateRing R) (PatchRing R) (zCoordinate R)) * _ = 1
  rw [← map_one (algebraMap (reciprocalCoordinateRing R) (PatchRing R)), ← map_add, ← map_mul]
  rw [map_one]
  change algebraMap (reciprocalCoordinateRing R) (PatchRing R) (denominator R) *
    IsLocalization.Away.invSelf (denominator R) = 1
  exact IsLocalization.Away.mul_invSelf (denominator R) (S := PatchRing R)

theorem one_add_z_mul_inverse : (1 + z R) * oneAddZInverse R = 1 := by
  rw [oneAddZInverse, ← mul_assoc, mul_comm (1 + z R)]
  change algebraMap (reciprocalCoordinateRing R) (PatchRing R) (wCoordinate R) *
    (1 + algebraMap (reciprocalCoordinateRing R) (PatchRing R) (zCoordinate R)) * _ = 1
  rw [← map_one (algebraMap (reciprocalCoordinateRing R) (PatchRing R)), ← map_add, ← map_mul]
  rw [map_one]
  change algebraMap (reciprocalCoordinateRing R) (PatchRing R) (denominator R) *
    IsLocalization.Away.invSelf (denominator R) = 1
  exact IsLocalization.Away.mul_invSelf (denominator R) (S := PatchRing R)

def tau : PatchRing R := z R * (1 + z R) * wInverse R
def mu : PatchRing R := (1 + z R) * wInverse R
def nu : PatchRing R := z R ^ 2 * (z R + z R ^ 2 - w R) * wInverse R ^ 2

theorem tau_eq_z_mul_mu : tau R = z R * mu R := by dsimp only [tau,mu];ring

theorem z_mul_nu : z R * nu R = mu R + 1 := by
  have he := congrArg (algebraMap (reciprocalCoordinateRing R) (PatchRing R))
    (reciprocal_secondary_identity R)
  simp only [map_mul,map_add,map_sub,map_pow,map_one] at he
  change w R * (w R + 1 + z R) = z R ^ 3 * (z R + z R ^ 2 - w R) at he
  calc
    _ = z R ^ 3 * (z R + z R ^ 2 - w R) * wInverse R ^ 2 := by dsimp only [nu];ring
    _ = w R * (w R + 1 + z R) * wInverse R ^ 2 := by rw [he]
    _ = (w R * wInverse R) ^ 2 + (1 + z R) * wInverse R * (w R * wInverse R) := by ring
    _ = mu R + 1 := by rw [w_mul_wInverse];dsimp only [mu];ring

theorem mu_squared : mu R ^ 2 = tau R * nu R - mu R := by
  rw [tau_eq_z_mul_mu]
  linear_combination -(mu R) * z_mul_nu R

theorem mu_mul_w : mu R * w R = 1 + z R := by
  dsimp only [mu]
  calc
    _ = (1 + z R) * (w R * wInverse R) := by ring
    _ = _ := by rw [w_mul_wInverse,mul_one]

theorem mu_isUnit : IsUnit (mu R) := by
  have h := one_add_z_isUnit R
  rw [← mu_mul_w] at h
  exact isUnit_of_mul_isUnit_left h

theorem mu_mul_mu_add_tau_isUnit : IsUnit (mu R * (mu R + tau R)) := by
  have he : mu R + tau R = mu R * (1 + z R) := by rw [tau_eq_z_mul_mu];ring
  rw [he]
  exact (mu_isUnit R).mul ((mu_isUnit R).mul (one_add_z_isUnit R))

theorem negative_infinity_denominator : infinityPointNegOne R (denominator R) = -1 := by
  have hz : infinityPointNegOne R (zCoordinate R) = 0 := by
    simp only [infinityPointNegOne,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X]
  have hw : infinityPointNegOne R (wCoordinate R) = -1 := AdjoinRoot.liftAlgHom_root _ _ _ _
  simp only [denominator,map_mul,map_add,map_one,hz,hw]
  ring

theorem positive_infinity_denominator : infinityPointZero R (denominator R) = 0 := by
  have hw : infinityPointZero R (wCoordinate R) = 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
  simp only [denominator,map_mul,hw,zero_mul]

end MazurTransfer.Order13MixedSingleSectionReciprocalPatch
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalPatch.z_mul_nu
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalPatch.mu_isUnit
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalPatch.negative_infinity_denominator
#print axioms MazurTransfer.Order13MixedSingleSectionReciprocalPatch.positive_infinity_denominator

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: construct the actual reciprocal-patch algebra map into the
localized finite coordinate algebra by recovered z,w and their literal mixed equation.
Named downstream consumer: the third single-section chart comparison.
No bijectivity or whole-curve complement is assumed or asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticPolynomialEvaluations
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

abbrev infinityLocalization := Localization.Away (infinityPatchElement R)
def infinityParameter : infinityLocalization R :=
  algebraMap (candidateAlgebra R) (infinityLocalization R) (parameterElement R)
def infinityP : infinityLocalization R :=
  algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R)
def infinityQ : infinityLocalization R :=
  algebraMap (candidateAlgebra R) (infinityLocalization R) (qElement R)
def infinityPInverse : infinityLocalization R :=
  (infinityP R + infinityParameter R) * IsLocalization.Away.invSelf (infinityPatchElement R)

theorem infinityP_mul_inverse : infinityP R * infinityPInverse R = 1 := by
  rw [infinityPInverse,← mul_assoc]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) *
    (algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) +
      algebraMap (candidateAlgebra R) (infinityLocalization R) (parameterElement R)) * _ = 1
  rw [← map_add,← map_mul]
  exact IsLocalization.Away.mul_invSelf (infinityPatchElement R)

theorem infinityP_mul_P_add_parameter_isUnit :
    IsUnit (infinityP R * (infinityP R + infinityParameter R)) := by
  change IsUnit (algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) *
    (algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) +
      algebraMap (candidateAlgebra R) (infinityLocalization R) (parameterElement R)))
  rw [← map_add,← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (infinityPatchElement R)

theorem infinityP_isUnit : IsUnit (infinityP R) :=
  isUnit_of_mul_isUnit_left (infinityP_mul_P_add_parameter_isUnit R)
theorem infinityP_add_parameter_isUnit : IsUnit (infinityP R + infinityParameter R) :=
  isUnit_of_mul_isUnit_right (infinityP_mul_P_add_parameter_isUnit R)
theorem infinityPInverse_isUnit : IsUnit (infinityPInverse R) := by
  have h : IsUnit (infinityP R * infinityPInverse R) := by rw [infinityP_mul_inverse]; exact isUnit_one
  exact isUnit_of_mul_isUnit_right h

def infinityRecoveredZ : infinityLocalization R := infinityParameter R * infinityPInverse R
def infinityRecoveredW : infinityLocalization R :=
  (1 + infinityRecoveredZ R) * infinityPInverse R

theorem infinityP_mul_one_add_recoveredZ :
    infinityP R * (1 + infinityRecoveredZ R) = infinityP R + infinityParameter R := by
  dsimp only [infinityRecoveredZ]
  linear_combination (infinityParameter R) * infinityP_mul_inverse R

theorem one_add_infinityRecoveredZ_isUnit : IsUnit (1 + infinityRecoveredZ R) := by
  have h := infinityP_add_parameter_isUnit R
  rw [← infinityP_mul_one_add_recoveredZ] at h
  exact isUnit_of_mul_isUnit_right h

theorem infinityRecoveredW_isUnit : IsUnit (infinityRecoveredW R) :=
  (one_add_infinityRecoveredZ_isUnit R).mul (infinityPInverse_isUnit R)

theorem candidate_parameter_quartic :
    parameterElement R ^ 4 - pElement R ^ 3 - pElement R ^ 2 * parameterElement R -
      parameterElement R ^ 3 - pElement R ^ 2 - pElement R * parameterElement R = 0 := by
  apply Subtype.val_injective
  change (parameterElement R : ordinaryCoordinateRing R) ^ 4 - p R ^ 3 -
    p R ^ 2 * (parameterElement R : ordinaryCoordinateRing R) -
    (parameterElement R : ordinaryCoordinateRing R) ^ 3 - p R ^ 2 -
    p R * (parameterElement R : ordinaryCoordinateRing R) = 0
  rw [parameterElement_coe]
  exact Order13MixedSingleSectionReciprocalRecoveryIdentities.actual_parameter_quartic R

theorem infinity_parameter_quartic :
    infinityParameter R ^ 4 - infinityP R ^ 3 - infinityP R ^ 2 * infinityParameter R -
      infinityParameter R ^ 3 - infinityP R ^ 2 - infinityP R * infinityParameter R = 0 := by
  simpa only [map_sub,map_mul,map_pow,map_zero,infinityParameter,infinityP]
    using congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) (candidate_parameter_quartic R)

theorem infinity_recovered_coordinate_identity :
    infinityParameter R * infinityRecoveredZ R ^ 3 -
      (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) = infinityRecoveredW R :=
  Order13MixedSingleSectionReciprocalRecoveryIdentities.recovered_coordinate_identity
    (infinityParameter R) (infinityP R) (infinityPInverse R)
    (infinityP_mul_inverse R) (infinity_parameter_quartic R)

theorem infinity_recovered_reciprocal_equation :
    infinityRecoveredW R ^ 2 + (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) *
      infinityRecoveredW R - (infinityRecoveredZ R ^ 4 + infinityRecoveredZ R ^ 5) = 0 :=
  Order13MixedSingleSectionReciprocalRecoveryIdentities.recovered_reciprocal_equation
    (infinityParameter R) (infinityP R) (infinityPInverse R)
    (infinityP_mul_inverse R) (infinity_parameter_quartic R)

def recoveredReciprocalBase : reciprocalCoordinateRing R →ₐ[R] infinityLocalization R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R))
    (aeval (infinityRecoveredZ R)) (infinityRecoveredW R) (by
      change eval₂ (aeval (infinityRecoveredZ R)).toRingHom (infinityRecoveredW R)
        (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
      simp only [eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
      rw [map_reciprocalH R _,map_reciprocalF R _]
      simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X]
      exact infinity_recovered_reciprocal_equation R)

theorem recoveredReciprocalBase_z : recoveredReciprocalBase R (zCoordinate R) = infinityRecoveredZ R := by
  simp only [recoveredReciprocalBase,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X]
theorem recoveredReciprocalBase_w : recoveredReciprocalBase R (wCoordinate R) = infinityRecoveredW R :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def recoveredReciprocalPatch : Order13MixedSingleSectionReciprocalPatch.PatchRing R →ₐ[R]
    infinityLocalization R :=
  IsLocalization.Away.liftAlgHom (Order13MixedSingleSectionReciprocalPatch.denominator R)
    (f := recoveredReciprocalBase R) (by
      rw [Order13MixedSingleSectionReciprocalPatch.denominator,map_mul,map_add,map_one,
        recoveredReciprocalBase_w,recoveredReciprocalBase_z]
      exact (infinityRecoveredW_isUnit R).mul (one_add_infinityRecoveredZ_isUnit R))

theorem recoveredReciprocalPatch_algebraMap (b : reciprocalCoordinateRing R) :
    recoveredReciprocalPatch R
      (algebraMap (reciprocalCoordinateRing R) (Order13MixedSingleSectionReciprocalPatch.PatchRing R) b) =
      recoveredReciprocalBase R b := by
  simp only [recoveredReciprocalPatch,IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq] <;> rfl

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.infinity_recovered_reciprocal_equation
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatch

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: faithful ordinary comparison for the third candidate chart,
and the inverse-abscissa identity of its recovered reciprocal coordinate.
Named downstream consumer: injectivity of the actual reciprocal-patch map.
No injectivity of that reciprocal map or whole-curve complement is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

abbrev ordinaryInfinityLocalization := Localization.Away (p R * (p R + t R))

theorem inclusion_infinityPatchElement :
    inclusion R (infinityPatchElement R) = p R * (p R + t R) := by
  rw [infinityPatchElement,map_mul,map_add,inclusion_parameter]
  rfl

def infinityLocalizedInclusion : infinityLocalization R →ₐ[R] ordinaryInfinityLocalization R := by
  letI : IsLocalization.Away (inclusion R (infinityPatchElement R))
      (ordinaryInfinityLocalization R) := by rw [inclusion_infinityPatchElement];infer_instance
  exact IsLocalization.Away.mapₐ _ _ (inclusion R) (infinityPatchElement R)

theorem infinityLocalizedInclusion_algebraMap (b : candidateAlgebra R) :
    infinityLocalizedInclusion R (algebraMap (candidateAlgebra R) (infinityLocalization R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (b : ordinaryCoordinateRing R) := by
  simp [infinityLocalizedInclusion,IsLocalization.Away.mapₐ,IsLocalization.Away.map,
    IsLocalization.map_eq,inclusion]

theorem infinityLocalizedInclusion_injective : Function.Injective (infinityLocalizedInclusion R) := by
  let : IsLocalization.Away (inclusion R (infinityPatchElement R))
      (ordinaryInfinityLocalization R) := by rw [inclusion_infinityPatchElement];infer_instance
  exact IsLocalization.Away.mapₐ_injective_of_injective (infinityPatchElement R)
    (f := inclusion R) Subtype.val_injective

theorem infinityLocalizedInclusion_parameter :
    infinityLocalizedInclusion R (infinityParameter R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (t R) := by
  rw [infinityParameter,infinityLocalizedInclusion_algebraMap,parameterElement_coe]

theorem infinityLocalizedInclusion_p : infinityLocalizedInclusion R (infinityP R) =
    algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (p R) := by
  rw [infinityP,infinityLocalizedInclusion_algebraMap];rfl

theorem ordinary_x_mul_infinityRecoveredZ :
    algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (xCoordinate R) *
      infinityLocalizedInclusion R (infinityRecoveredZ R) = 1 := by
  have h := congrArg (infinityLocalizedInclusion R) (infinityP_mul_inverse R)
  rw [map_mul,map_one,infinityLocalizedInclusion_p] at h
  rw [infinityRecoveredZ,map_mul,infinityLocalizedInclusion_parameter]
  change algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R)
    (xCoordinate R * t R) * infinityLocalizedInclusion R (infinityPInverse R) = 1 at h
  rw [map_mul] at h
  simpa only [mul_assoc] using h

theorem ordinary_x_isUnit_on_infinity_chart :
    IsUnit (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (xCoordinate R)) := by
  have h := (infinityP_isUnit R).map (infinityLocalizedInclusion R)
  rw [infinityLocalizedInclusion_p] at h
  change IsUnit (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (xCoordinate R * t R)) at h
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

theorem infinityLocalizedInclusion_recoveredZ_isUnit :
    IsUnit (infinityLocalizedInclusion R (infinityRecoveredZ R)) := by
  have h : IsUnit (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (xCoordinate R) *
      infinityLocalizedInclusion R (infinityRecoveredZ R)) := by
    rw [ordinary_x_mul_infinityRecoveredZ];exact isUnit_one
  exact isUnit_of_mul_isUnit_right h

theorem infinityRecoveredZ_mul_injective :
    Function.Injective (fun a : infinityLocalization R => infinityRecoveredZ R * a) := by
  intro a b hab
  apply infinityLocalizedInclusion_injective R
  have h := congrArg (infinityLocalizedInclusion R) hab
  rw [map_mul,map_mul] at h
  exact (infinityLocalizedInclusion_recoveredZ_isUnit R).mul_right_inj.mp h

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.infinityLocalizedInclusion_injective
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.infinityRecoveredZ_mul_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the recovered ordinate equals the actual reciprocal
ordinate in the ordinary comparison localization. Named downstream consumer:
the full reciprocal-chart comparison square and its injectivity.
-/

noncomputable section
namespace MazurTransfer.Order13MixedReciprocalOrdinateIdentity
variable {A : Type*} [CommRing A]

theorem recovered_ordinate (x y t z w : A) (hx : x * z = 1)
    (ht : t = y + x ^ 3 + x ^ 2 + 1)
    (hw : t * z ^ 3 - (1 + z + z ^ 3) = w) : w = y * z ^ 3 := by
  have hx2 : x ^ 2 * z ^ 2 = 1 := by rw [← mul_pow,hx,one_pow]
  have hx3 : x ^ 3 * z ^ 3 = 1 := by rw [← mul_pow,hx,one_pow]
  linear_combination -hw + z ^ 3 * ht + hx3 + z * hx2

end MazurTransfer.Order13MixedReciprocalOrdinateIdentity

universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

theorem infinityLocalizedInclusion_recoveredW :
    infinityLocalizedInclusion R (infinityRecoveredW R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (yCoordinate R) *
        infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  let a : ordinaryCoordinateRing R →+* ordinaryInfinityLocalization R := algebraMap _ _
  let x := a (xCoordinate R)
  let y := a (yCoordinate R)
  let tt := a (t R)
  let zz := infinityLocalizedInclusion R (infinityRecoveredZ R)
  let ww := infinityLocalizedInclusion R (infinityRecoveredW R)
  have hx : x * zz = 1 := ordinary_x_mul_infinityRecoveredZ R
  have ht : tt = y + x ^ 3 + x ^ 2 + 1 := by
    dsimp only [tt,t,x,y]
    simp only [map_add,map_pow,map_one]
    ring
  have hw : tt * zz ^ 3 - (1 + zz + zz ^ 3) = ww := by
    have h := congrArg (infinityLocalizedInclusion R) (infinity_recovered_coordinate_identity R)
    simpa only [map_sub,map_mul,map_pow,map_add,map_one,infinityLocalizedInclusion_parameter] using h
  exact Order13MixedReciprocalOrdinateIdentity.recovered_ordinate x y tt zz ww hx ht hw

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedReciprocalOrdinateIdentity.recovered_ordinate
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.infinityLocalizedInclusion_recoveredW

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual mixed quadratic chart rings are domains over
any integral coefficient ring, by their flat embeddings in fraction-field
charts. Named downstream consumer: faithfulness of reciprocal principal
patches in the mixed single-section affine-complement comparison.
-/

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticIntegralChartDomains
open Polynomial Algebra TensorProduct
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticChartFiniteAlgebras
open Order13MixedQuadraticAffineBaseChange Order13MixedQuadraticFieldChartDomains
universe u
variable (R : Type u) [CommRing R] [IsDomain R]

def ordinaryFractionMap : ordinaryCoordinateRing R →+* ordinaryCoordinateRing (FractionRing R) :=
  (ordinaryAlgebraEquiv R (FractionRing R)).toRingHom.comp
    (Algebra.TensorProduct.includeRight.toRingHom)

def reciprocalFractionMap : reciprocalCoordinateRing R →+* reciprocalCoordinateRing (FractionRing R) :=
  (reciprocalAlgebraEquiv R (FractionRing R)).toRingHom.comp
    (Algebra.TensorProduct.includeRight.toRingHom)

theorem ordinaryFractionMap_injective : Function.Injective (ordinaryFractionMap R) := by
  let : Module.Free (Polynomial R) (ordinaryCoordinateRing R) := (ordinaryEquation_monic R).free_adjoinRoot
  let : Module.Flat R (ordinaryCoordinateRing R) := Module.Flat.trans R (Polynomial R) _
  exact (ordinaryAlgebraEquiv R (FractionRing R)).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R (FractionRing R)))

theorem reciprocalFractionMap_injective : Function.Injective (reciprocalFractionMap R) := by
  let : Module.Free (Polynomial R) (reciprocalCoordinateRing R) := (reciprocalEquation_monic R).free_adjoinRoot
  let : Module.Flat R (reciprocalCoordinateRing R) := Module.Flat.trans R (Polynomial R) _
  exact (reciprocalAlgebraEquiv R (FractionRing R)).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R (FractionRing R)))

theorem ordinary_isDomain : IsDomain (ordinaryCoordinateRing R) := by
  let := MixedQuadraticEquationIrreducible.ordinary_field_isDomain (FractionRing R)
  exact Function.Injective.isDomain (ordinaryFractionMap R) (ordinaryFractionMap_injective R)

theorem reciprocal_isDomain : IsDomain (reciprocalCoordinateRing R) := by
  let := reciprocal_field_isDomain (FractionRing R)
  exact Function.Injective.isDomain (reciprocalFractionMap R) (reciprocalFractionMap_injective R)

end MazurTransfer.Order13MixedQuadraticIntegralChartDomains
#print axioms MazurTransfer.Order13MixedQuadraticIntegralChartDomains.ordinary_isDomain
#print axioms MazurTransfer.Order13MixedQuadraticIntegralChartDomains.reciprocal_isDomain

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the owned localization-faithfulness proofs to the mixed model.
Design boundary: actual ordinary and reciprocal localizations are faithful
over every integral coefficient ring, with no inversion of two or thirteen.
Named downstream consumer: reciprocal principal-patch map injectivity.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticIntegralChartDomains
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

section DomainCoordinates
variable [IsDomain R]

private theorem mixed_polynomial_inclusion_injective (h f : Polynomial R) :
    Function.Injective (AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation R h f)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [Polynomial.degree_eq_natDegree
    (Order13MixedQuadraticChartFiniteAlgebras.mixed_equation_monic R h f).ne_zero,
    MixedQuadraticEquationIrreducible.equation_natDegree R h f]
  decide

theorem ordinary_polynomial_inclusion_injective : Function.Injective
    (AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation R)) :=
  mixed_polynomial_inclusion_injective R _ _
theorem reciprocal_polynomial_inclusion_injective : Function.Injective
    (AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation R)) :=
  mixed_polynomial_inclusion_injective R _ _

theorem actual_ordinary_x_ne_zero : xCoordinate R ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation R) X = AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation R) 0 := by
    simpa only [xCoordinate,map_zero] using h
  exact Polynomial.X_ne_zero (ordinary_polynomial_inclusion_injective R hx)

theorem actual_ordinary_x_add_one_ne_zero : xCoordinate R + 1 ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation R) (X + 1) = AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation R) 0 := by
    simpa only [xCoordinate,map_add,map_one,map_zero] using h
  have hp := ordinary_polynomial_inclusion_injective R hx
  exact Polynomial.X_add_C_ne_zero (1 : R) hp

theorem actual_reciprocal_z_ne_zero : zCoordinate R ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation R) X = AdjoinRoot.of (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation R) 0 := by
    simpa only [zCoordinate,map_zero] using h
  exact Polynomial.X_ne_zero (reciprocal_polynomial_inclusion_injective R hx)

theorem actual_ordinary_parameter_ne_zero : t R ≠ 0 := by
  let := ordinary_isDomain R
  exact isRegular_iff_ne_zero.mp (Order13MixedSingleSectionParameterRegular.parameter_regular R)

end DomainCoordinates

def ordinaryOverlapToInfinity : OrdinaryOverlapRing R →ₐ[R] ordinaryInfinityLocalization R :=
  IsLocalization.Away.liftAlgHom (xCoordinate R)
    (f := IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R))
    (ordinary_x_isUnit_on_infinity_chart R)

theorem ordinaryOverlapToInfinity_algebraMap (b : ordinaryCoordinateRing R) :
    ordinaryOverlapToInfinity R (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) b := by
  simp [ordinaryOverlapToInfinity,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

section IntegralGeometry
variable [IsDomain R]

theorem actual_infinity_ordinary_denominator_ne_zero : p R * (p R + t R) ≠ 0 := by
  letI : IsDomain (ordinaryCoordinateRing R) := ordinary_isDomain R
  have he : p R * (p R + t R) = xCoordinate R * (xCoordinate R + 1) * t R ^ 2 := by
    dsimp [p];ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (actual_ordinary_x_ne_zero R) (actual_ordinary_x_add_one_ne_zero R))
    (pow_ne_zero 2 (actual_ordinary_parameter_ne_zero R))

theorem ordinaryInfinity_algebraMap_injective :
    Function.Injective (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R)) := by
  letI : IsDomain (ordinaryCoordinateRing R) := ordinary_isDomain R
  exact IsLocalization.injective (ordinaryInfinityLocalization R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (actual_infinity_ordinary_denominator_ne_zero R))

theorem reciprocalOverlap_algebraMap_injective :
    Function.Injective (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)) := by
  letI : IsDomain (reciprocalCoordinateRing R) := reciprocal_isDomain R
  exact IsLocalization.injective (ReciprocalOverlapRing R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (actual_reciprocal_z_ne_zero R))

theorem ordinaryOverlapToInfinity_injective : Function.Injective (ordinaryOverlapToInfinity R) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (OrdinaryOverlapRing R)
    (M := Submonoid.powers (xCoordinate R))
    (ordinaryOverlapToInfinity R).toRingHom
  intro a ha
  change ordinaryOverlapToInfinity R
    (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) a) = 0 at ha
  rw [ordinaryOverlapToInfinity_algebraMap] at ha
  have hh : a = 0 := ordinaryInfinity_algebraMap_injective R (by simpa only [map_zero] using ha)
  rw [hh,map_zero]

end IntegralGeometry
end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryInfinity_algebraMap_injective
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.reciprocalOverlap_algebraMap_injective
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryOverlapToInfinity_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the inverse positive-infinity chart maps into the literal
ordinary t-localization further localized at its actual H*L denominator;
its recovered coordinates agree with z=1/x and w=y/x³.
Named downstream consumer: faithful reciprocal-chart comparison and gluing.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedInverseParameterPolynomialIdentities
open Order13MixedSingleSectionPolynomialIdentities (t p q)

variable (R : Type u) [CommRing R]

abbrev ordinaryInfinityLocalization := Localization.Away (inclusion R (infinityPatchElement R))
def ordinaryInfinityMap : ordinaryParameterLocalization R →ₐ[R] ordinaryInfinityLocalization R :=
  IsScalarTower.toAlgHom R (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)
def ordinaryCoordinateMap : ordinaryCoordinateRing R →ₐ[R] ordinaryInfinityLocalization R :=
  (ordinaryInfinityMap R).comp (IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))
def ordinaryX : ordinaryInfinityLocalization R := ordinaryCoordinateMap R (xCoordinate R)
def ordinaryY : ordinaryInfinityLocalization R := ordinaryCoordinateMap R (yCoordinate R)
def ordinaryT : ordinaryInfinityLocalization R := ordinaryCoordinateMap R (t R)
def ordinaryS : ordinaryInfinityLocalization R := ordinaryInfinityMap R (s R)

def infinityLocalizedInclusion : infinityLocalization R →ₐ[R] ordinaryInfinityLocalization R :=
  IsLocalization.Away.liftAlgHom (infinityPatchElement R)
    (f := (ordinaryInfinityMap R).comp (inclusion R))
    (IsLocalization.Away.algebraMap_isUnit (inclusion R (infinityPatchElement R)))

theorem infinityLocalizedInclusion_algebraMap (c : candidateAlgebra R) :
    infinityLocalizedInclusion R (algebraMap (candidateAlgebra R) (infinityLocalization R) c) =
      ordinaryInfinityMap R (inclusion R c) := by
  simp [infinityLocalizedInclusion,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem ordinaryT_mul_S : ordinaryT R * ordinaryS R = 1 := by
  change ordinaryInfinityMap R (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R)) *
    ordinaryInfinityMap R (s R) = 1
  rw [← map_mul]
  change ordinaryInfinityMap R (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R) *
    IsLocalization.Away.invSelf (t R)) = 1
  rw [IsLocalization.Away.mul_invSelf,map_one]
theorem ordinaryS_isUnit : IsUnit (ordinaryS R) :=
  isUnit_iff_exists_inv.mpr ⟨ordinaryT R,by rw [mul_comm];exact ordinaryT_mul_S R⟩

theorem infinityLocalizedInclusion_S : infinityLocalizedInclusion R (infinityS R) = ordinaryS R := by
  rw [infinityS,infinityLocalizedInclusion_algebraMap,inclusion_sElement]
  rfl

theorem infinityLocalizedInclusion_A : infinityLocalizedInclusion R (infinityA R) =
    ordinaryX R * ordinaryS R := by
  rw [infinityA,infinityLocalizedInclusion_algebraMap]
  change ordinaryInfinityMap R (a R) = _
  have ht := ordinaryT_mul_S R
  simp only [a,p,s,map_mul,map_pow]
  change ordinaryX R * ordinaryT R * ordinaryS R ^ 2 = _
  linear_combination ordinaryX R * ordinaryS R * ht

theorem infinityLocalizedInclusion_L : infinityLocalizedInclusion R (infinityL R) =
    ordinaryX R * infinityLocalizedInclusion R (infinityB R) := by
  apply (ordinaryS_isUnit R).mul_right_inj.mp
  have h := congrArg (infinityLocalizedInclusion R) (infinity_A_B R)
  rw [map_mul,map_mul,infinityLocalizedInclusion_A,
    infinityLocalizedInclusion_S] at h
  linear_combination -h

theorem infinityLocalizedInclusion_H : infinityLocalizedInclusion R (infinityH R) =
    ordinaryX R ^ 3 * ordinaryS R := by
  apply ((ordinaryS_isUnit R).pow 2).mul_right_inj.mp
  have h := congrArg ((infinityLocalizedInclusion R).comp
    (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R))) (s_squared_mul_root R)
  simp only [AlgHom.comp_apply,map_mul,map_pow,_root_.map_ofNat] at h
  change infinityLocalizedInclusion R (infinityS R) ^ 2 * infinityLocalizedInclusion R (infinityH R) =
    infinityLocalizedInclusion R (infinityA R) ^ 3 at h
  rw [infinityLocalizedInclusion_S,infinityLocalizedInclusion_A] at h
  linear_combination h

theorem ordinaryX_isUnit : IsUnit (ordinaryX R) := by
  have h := (infinityL_isUnit R).map (infinityLocalizedInclusion R)
  rw [infinityLocalizedInclusion_L] at h
  exact isUnit_of_mul_isUnit_left h

theorem ordinaryX_mul_recoveredZ : ordinaryX R *
    infinityLocalizedInclusion R (infinityRecoveredZ R) = 1 := by
  apply (ordinaryS_isUnit R).mul_right_inj.mp
  have h := congrArg (infinityLocalizedInclusion R) (recoveredZ_mul_A R)
  rw [map_mul,infinityLocalizedInclusion_A,infinityLocalizedInclusion_S] at h
  linear_combination h

theorem infinityLocalizedInclusion_recoveredF :
    infinityLocalizedInclusion R (infinityRecoveredF R) = ordinaryT R *
      infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  apply ((infinityH_isUnit R).map (infinityLocalizedInclusion R)).mul_right_inj.mp
  have hf := congrArg (infinityLocalizedInclusion R) (H_mul_recoveredF R)
  rw [map_mul,map_one] at hf
  rw [infinityLocalizedInclusion_H] at hf ⊢
  have hx := ordinaryX_mul_recoveredZ R
  have ht := ordinaryT_mul_S R
  linear_combination hf - ht -
    ordinaryT R * ordinaryS R *
      ((ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R)) ^ 2 +
        ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1) * hx

theorem infinityLocalizedInclusion_recoveredW :
    infinityLocalizedInclusion R (infinityRecoveredW R) = ordinaryY R *
      infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  rw [infinityRecoveredW,map_sub,map_add,map_add,map_one,map_pow,
    infinityLocalizedInclusion_recoveredF]
  have ht : ordinaryT R = ordinaryY R + ordinaryX R ^ 3 + ordinaryX R ^ 2 + 1 := by
    simp only [ordinaryT,t,map_add,map_pow,map_one,
      ordinaryX,ordinaryY]
    ring
  have hx := ordinaryX_mul_recoveredZ R
  rw [ht]
  linear_combination
    ((ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R)) ^ 2 +
      ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1 +
      infinityLocalizedInclusion R (infinityRecoveredZ R) *
        (ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1)) * hx

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.infinityLocalizedInclusion_recoveredW

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the recovered reciprocal patch map takes its three
regular parameters to the literal t,p,q in the localized finite algebra.
Named downstream consumer: surjectivity and the actual reciprocal chart
comparison. No whole-curve complement is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_z :
    recoveredReciprocalPatch R (Order13MixedSingleSectionReciprocalPatch.z R) = infinityRecoveredZ R :=
  (recoveredReciprocalPatch_algebraMap R (zCoordinate R)).trans (recoveredReciprocalBase_z R)

theorem recoveredReciprocalPatch_w :
    recoveredReciprocalPatch R (Order13MixedSingleSectionReciprocalPatch.w R) = infinityRecoveredW R :=
  (recoveredReciprocalPatch_algebraMap R (wCoordinate R)).trans (recoveredReciprocalBase_w R)

theorem recoveredReciprocalPatch_mu :
    recoveredReciprocalPatch R (Order13MixedSingleSectionReciprocalPatch.mu R) = infinityP R := by
  apply (infinityRecoveredW_isUnit R).mul_left_inj.mp
  have h := congrArg (recoveredReciprocalPatch R)
    (Order13MixedSingleSectionReciprocalPatch.mu_mul_w R)
  rw [map_mul,map_add,map_one,recoveredReciprocalPatch_w,recoveredReciprocalPatch_z] at h
  calc
    _ = 1 + infinityRecoveredZ R := h
    _ = _ := by
      dsimp only [infinityRecoveredW]
      linear_combination -(1 + infinityRecoveredZ R) * infinityP_mul_inverse R

theorem recoveredReciprocalPatch_tau :
    recoveredReciprocalPatch R (Order13MixedSingleSectionReciprocalPatch.tau R) = infinityParameter R := by
  rw [Order13MixedSingleSectionReciprocalPatch.tau_eq_z_mul_mu,map_mul,
    recoveredReciprocalPatch_z,recoveredReciprocalPatch_mu]
  dsimp only [infinityRecoveredZ]
  linear_combination (infinityParameter R) * infinityP_mul_inverse R

theorem infinity_p_squared : infinityP R ^ 2 = infinityParameter R * infinityQ R - infinityP R := by
  have h : pElement R ^ 2 = parameterElement R * qElement R - pElement R := by
    apply Subtype.val_injective
    change p R ^ 2 = (parameterElement R : ordinaryCoordinateRing R) * q R - p R
    rw [parameterElement_coe]
    exact p_squared R
  simpa only [map_pow,map_sub,map_mul,infinityParameter,infinityP,infinityQ]
    using congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) h

theorem infinity_recoveredZ_mul_q : infinityRecoveredZ R * infinityQ R = infinityP R + 1 := by
  dsimp only [infinityRecoveredZ]
  linear_combination -(infinityPInverse R) * infinity_p_squared R +
    (infinityP R + 1) * infinityP_mul_inverse R

theorem recoveredReciprocalPatch_nu :
    recoveredReciprocalPatch R (Order13MixedSingleSectionReciprocalPatch.nu R) = infinityQ R := by
  apply infinityRecoveredZ_mul_injective R
  calc
    _ = recoveredReciprocalPatch R
        (Order13MixedSingleSectionReciprocalPatch.z R * Order13MixedSingleSectionReciprocalPatch.nu R) := by
      rw [map_mul,recoveredReciprocalPatch_z]
    _ = infinityP R + 1 := by
      rw [Order13MixedSingleSectionReciprocalPatch.z_mul_nu,map_add,map_one,recoveredReciprocalPatch_mu]
    _ = infinityRecoveredZ R * infinityQ R := (infinity_recoveredZ_mul_q R).symm

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatch_mu
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatch_tau
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatch_nu

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjectivity of the actual recovered reciprocal-patch map.
Named downstream consumer: the third single-section chart isomorphism.
No injectivity or curve-complement identification is assumed or asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_polynomial_scalars (F : Polynomial R) :
    recoveredReciprocalPatch R (aeval (Order13MixedSingleSectionReciprocalPatch.tau R) F) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (algebraMap (Polynomial R) (candidateAlgebra R) F) := by
  have h : (recoveredReciprocalPatch R).comp (aeval (Order13MixedSingleSectionReciprocalPatch.tau R)) =
      (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R)).comp
        (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) := by
    apply Polynomial.algHom_ext
    change recoveredReciprocalPatch R (aeval (Order13MixedSingleSectionReciprocalPatch.tau R) X) =
      infinityParameter R
    rw [aeval_X,recoveredReciprocalPatch_tau]
  exact DFunLike.congr_fun h F

theorem recoveredReciprocalPatch_contains_candidate (b : candidateAlgebra R) :
    ∃ c : Order13MixedSingleSectionReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R c = algebraMap (candidateAlgebra R) (infinityLocalization R) b := by
  rcases b with ⟨b,hb⟩
  refine Algebra.adjoin_induction (R := Polynomial R)
    (p := fun x hx => ∃ c : Order13MixedSingleSectionReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R c =
        algebraMap (candidateAlgebra R) (infinityLocalization R) ⟨x,hx⟩) ?_ ?_ ?_ ?_ hb
  · intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Order13MixedSingleSectionReciprocalPatch.mu R,recoveredReciprocalPatch_mu R⟩
    · exact ⟨Order13MixedSingleSectionReciprocalPatch.nu R,recoveredReciprocalPatch_nu R⟩
  · intro F
    exact ⟨aeval (Order13MixedSingleSectionReciprocalPatch.tau R) F,
      recoveredReciprocalPatch_polynomial_scalars R F⟩
  · intro x y hx hy hcx hcy
    rcases hcx with ⟨c,hc⟩;rcases hcy with ⟨d,hd⟩
    refine ⟨c+d,?_⟩
    rw [map_add,hc,hd,← map_add]
    rfl
  · intro x y hx hy hcx hcy
    rcases hcx with ⟨c,hc⟩;rcases hcy with ⟨d,hd⟩
    refine ⟨c*d,?_⟩
    rw [map_mul,hc,hd,← map_mul]
    rfl

theorem recoveredReciprocalPatch_infinityPatchElement :
    recoveredReciprocalPatch R
      (Order13MixedSingleSectionReciprocalPatch.mu R *
        (Order13MixedSingleSectionReciprocalPatch.mu R + Order13MixedSingleSectionReciprocalPatch.tau R)) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) := by
  rw [map_mul,map_add,recoveredReciprocalPatch_mu,recoveredReciprocalPatch_tau]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) *
    (algebraMap (candidateAlgebra R) (infinityLocalization R) (pElement R) +
      algebraMap (candidateAlgebra R) (infinityLocalization R) (parameterElement R)) = _
  rw [← map_add,← map_mul]
  rfl

theorem recoveredReciprocalPatch_surjective :
    Function.Surjective (recoveredReciprocalPatch R) := by
  let v : Order13MixedSingleSectionReciprocalPatch.PatchRing R :=
    Order13MixedSingleSectionReciprocalPatch.mu R *
      (Order13MixedSingleSectionReciprocalPatch.mu R + Order13MixedSingleSectionReciprocalPatch.tau R)
  have hv : IsUnit v := Order13MixedSingleSectionReciprocalPatch.mu_mul_mu_add_tau_isUnit R
  let vi : Order13MixedSingleSectionReciprocalPatch.PatchRing R := ↑(hv.unit⁻¹)
  have hiv : recoveredReciprocalPatch R vi *
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) = 1 := by
    calc
      _ = recoveredReciprocalPatch R (vi * v) := by
        rw [map_mul,recoveredReciprocalPatch_infinityPatchElement]
      _ = 1 := by
        have h : vi * v = 1 := by rw [← hv.unit_spec];exact Units.inv_mul hv.unit
        rw [h,map_one]
  intro a
  obtain ⟨b,s,hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (infinityPatchElement R)) a
  obtain ⟨n,hn⟩ := (Submonoid.mem_powers_iff (s : candidateAlgebra R) (infinityPatchElement R)).mp s.property
  obtain ⟨c,hc⟩ := recoveredReciprocalPatch_contains_candidate R b
  refine ⟨c * vi ^ n,?_⟩
  rw [← hs]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [map_mul,map_pow,hc,← hn,map_pow]
  calc
    _ = algebraMap (candidateAlgebra R) (infinityLocalization R) b *
      (recoveredReciprocalPatch R vi *
        algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R)) ^ n := by ring
    _ = _ := by rw [hiv,one_pow,mul_one]

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatch_surjective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual third chart equivalence over arbitrary integral
coefficient rings, without inverting two, retaining the recovered reciprocal parameter map.
Named downstream consumer: gluing the single-section affine complement.
No whole-curve complement or full FiniteMapData is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticOverlapEquivalence
variable (R : Type u) [CommRing R]

theorem ordinaryOverlapToInfinity_inverse_x :
    ordinaryOverlapToInfinity R (IsLocalization.Away.invSelf (xCoordinate R)) =
      infinityLocalizedInclusion R (infinityRecoveredZ R) := by
  apply (ordinary_x_isUnit_on_infinity_chart R).mul_right_inj.mp
  calc
    _ = ordinaryOverlapToInfinity R
      (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R) *
        IsLocalization.Away.invSelf (xCoordinate R)) := by
      rw [map_mul,ordinaryOverlapToInfinity_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf,map_one]
    _ = _ := (ordinary_x_mul_infinityRecoveredZ R).symm

theorem ordinaryOverlapToInfinity_reciprocal_z :
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (zCoordinate R)) =
      infinityLocalizedInclusion R (infinityRecoveredZ R) := by
  rw [reciprocalToOrdinaryBase_z]
  change ordinaryOverlapToInfinity R (IsLocalization.Away.invSelf (xCoordinate R)) = _
  exact ordinaryOverlapToInfinity_inverse_x R

theorem ordinaryOverlapToInfinity_reciprocal_w :
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (wCoordinate R)) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (yCoordinate R) *
        infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  rw [reciprocalToOrdinaryBase_w]
  change ordinaryOverlapToInfinity R
    (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R) *
      IsLocalization.Away.invSelf (xCoordinate R) ^ 3) = _
  rw [map_mul,map_pow,ordinaryOverlapToInfinity_algebraMap,ordinaryOverlapToInfinity_inverse_x]

theorem recovered_reciprocal_ordinary_comparison_square :
    (infinityLocalizedInclusion R).comp (recoveredReciprocalBase R) =
      (ordinaryOverlapToInfinity R).comp (reciprocalToOrdinaryBase R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change infinityLocalizedInclusion R (recoveredReciprocalBase R (zCoordinate R)) =
      ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (zCoordinate R))
    rw [recoveredReciprocalBase_z,ordinaryOverlapToInfinity_reciprocal_z]
  · change infinityLocalizedInclusion R (recoveredReciprocalBase R (wCoordinate R)) =
      ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (wCoordinate R))
    rw [recoveredReciprocalBase_w,infinityLocalizedInclusion_recoveredW,
      ordinaryOverlapToInfinity_reciprocal_w]

section IntegralGeometry
variable [IsDomain R]

theorem actual_reciprocalToOrdinaryBase_injective : Function.Injective (reciprocalToOrdinaryBase R) := by
  have he (a : reciprocalCoordinateRing R) :
      (overlapAlgEquiv R).symm
        (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) =
      reciprocalToOrdinaryBase R a := by
    change reciprocalToOrdinary R
      (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) = _
    exact reciprocalToOrdinary_algebraMap R a
  intro a b hab
  apply reciprocalOverlap_algebraMap_injective R
  apply (overlapAlgEquiv R).symm.injective
  simpa only [he] using hab

theorem actual_recoveredReciprocalBase_ordinary_composite_injective :
    Function.Injective ((infinityLocalizedInclusion R).comp (recoveredReciprocalBase R)) := by
  rw [recovered_reciprocal_ordinary_comparison_square]
  exact (ordinaryOverlapToInfinity_injective R).comp
    (actual_reciprocalToOrdinaryBase_injective R)

theorem recoveredReciprocalPatch_injective :
    Function.Injective (recoveredReciprocalPatch R) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (Order13MixedSingleSectionReciprocalPatch.PatchRing R)
    (M := Submonoid.powers (Order13MixedSingleSectionReciprocalPatch.denominator R))
    (recoveredReciprocalPatch R).toRingHom
  intro a ha
  change recoveredReciprocalPatch R
    (algebraMap (reciprocalCoordinateRing R) (Order13MixedSingleSectionReciprocalPatch.PatchRing R) a) = 0 at ha
  rw [recoveredReciprocalPatch_algebraMap] at ha
  have h := congrArg (infinityLocalizedInclusion R) ha
  have hz : a = 0 := actual_recoveredReciprocalBase_ordinary_composite_injective R
    (by simpa only [AlgHom.comp_apply,map_zero] using h)
  rw [hz,map_zero]

def recoveredReciprocalPatchEquiv : Order13MixedSingleSectionReciprocalPatch.PatchRing R ≃ₐ[R]
    infinityLocalization R :=
  AlgEquiv.ofBijective (recoveredReciprocalPatch R )
    ⟨recoveredReciprocalPatch_injective R ,
      recoveredReciprocalPatch_surjective R ⟩

theorem recoveredReciprocalPatchEquiv_tau :
    recoveredReciprocalPatchEquiv R (Order13MixedSingleSectionReciprocalPatch.tau R) = infinityParameter R :=
  recoveredReciprocalPatch_tau R 
theorem recoveredReciprocalPatchEquiv_mu :
    recoveredReciprocalPatchEquiv R (Order13MixedSingleSectionReciprocalPatch.mu R) = infinityP R :=
  recoveredReciprocalPatch_mu R 
theorem recoveredReciprocalPatchEquiv_nu :
    recoveredReciprocalPatchEquiv R (Order13MixedSingleSectionReciprocalPatch.nu R) = infinityQ R :=
  recoveredReciprocalPatch_nu R 

end IntegralGeometry
end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recovered_reciprocal_ordinary_comparison_square
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatchEquiv
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatchEquiv_tau
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatchEquiv_mu
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.recoveredReciprocalPatchEquiv_nu

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: nonzero inverse-chart denominators and faithful maps from
the actual ordinary and reciprocal coordinate rings over integral bases.
Named downstream consumer: the inverse-parameter reciprocal chart isomorphism.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticIntegralChartDomains
open Order13MixedInverseParameterPolynomialIdentities
open Order13MixedSingleSectionPolynomialIdentities (t p q)

variable (R : Type u) [CommRing R] [IsDomain R]

theorem actual_ordinary_q_ne_zero : q R ≠ 0 := by
  intro hq
  have hd := Order13MixedSingleSectionWeightedPolynomialCoordinates.first_q_power_degree R 0
  simp only [pow_zero,mul_one] at hd
  rw [hq,map_zero,Polynomial.natDegree_zero] at hd
  norm_num at hd

def ordinaryParameterDomain  : IsDomain (ordinaryParameterLocalization R) := by
  letI : IsDomain (ordinaryCoordinateRing R) := ordinary_isDomain R
  exact Localization.Away.isDomain (Order13MixedSingleSectionFiniteAlgebra.actual_ordinary_parameter_ne_zero R)

theorem ordinaryParameter_algebraMap_injective  :
    Function.Injective (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)) := by
  letI : IsDomain (ordinaryCoordinateRing R) := ordinary_isDomain R
  exact IsLocalization.injective (ordinaryParameterLocalization R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Order13MixedSingleSectionFiniteAlgebra.actual_ordinary_parameter_ne_zero R))

theorem actual_inverse_a_ne_zero  : a R ≠ 0 := by
  letI := ordinaryParameterDomain R
  have hx : algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) ≠ 0 := by
    exact fun h => Order13MixedSingleSectionFiniteAlgebra.actual_ordinary_x_ne_zero R
      (ordinaryParameter_algebraMap_injective R (by simpa only [map_zero] using h))
  have ht := IsLocalization.Away.mul_invSelf (t R) (S := ordinaryParameterLocalization R)
  have ha : a R = algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) * s R := by
    dsimp [a,p,s]
    rw [map_mul]
    linear_combination algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) *
      IsLocalization.Away.invSelf (t R) * ht
  rw [ha]
  exact mul_ne_zero hx (s_isUnit R).ne_zero

theorem actual_inverse_b_ne_zero  : b R ≠ 0 := by
  letI := ordinaryParameterDomain R
  have hq : algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (q R) ≠ 0 := by
    exact fun h => actual_ordinary_q_ne_zero R
      (ordinaryParameter_algebraMap_injective R (by simpa only [map_zero] using h))
  exact mul_ne_zero hq (pow_ne_zero 2 (s_isUnit R).ne_zero)

theorem actual_inverse_infinity_denominator_ne_zero  :
    inclusion R (infinityPatchElement R) ≠ 0 := by
  letI := ordinaryParameterDomain R
  have hH : inclusion R (infinityRootElement R) ≠ 0 := by
    have h := congrArg (inclusion R) (s_squared_mul_root R)
    simp only [map_mul,map_pow,inclusion_sElement] at h
    change s R ^ 2 * inclusion R (infinityRootElement R) = a R ^ 3 at h
    intro hh
    rw [hh,mul_zero] at h
    exact (pow_ne_zero 3 (actual_inverse_a_ne_zero R)) h.symm
  have hL : inclusion R (infinityLinearElement R) ≠ 0 := by
    have h := congrArg (inclusion R) (a_mul_b_linear R)
    simp only [map_mul,inclusion_sElement] at h
    change a R * b R = s R * inclusion R (infinityLinearElement R) at h
    intro hh
    rw [hh,mul_zero] at h
    exact (mul_ne_zero (actual_inverse_a_ne_zero R) (actual_inverse_b_ne_zero R)) h
  change inclusion R (infinityRootElement R * infinityLinearElement R) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hH hL

theorem ordinaryInfinityMap_injective  :
    Function.Injective (ordinaryInfinityMap R) := by
  letI := ordinaryParameterDomain R
  exact IsLocalization.injective (ordinaryInfinityLocalization R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (actual_inverse_infinity_denominator_ne_zero R))

theorem ordinaryCoordinateMap_injective  :
    Function.Injective (ordinaryCoordinateMap R) :=
  (ordinaryInfinityMap_injective R).comp (ordinaryParameter_algebraMap_injective R)

def ordinaryOverlapToInfinity : OrdinaryOverlapRing R →ₐ[R] ordinaryInfinityLocalization R :=
  IsLocalization.Away.liftAlgHom (xCoordinate R) (f := ordinaryCoordinateMap R) (ordinaryX_isUnit R)

theorem ordinaryOverlapToInfinity_algebraMap (c : ordinaryCoordinateRing R) :
    ordinaryOverlapToInfinity R (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) c) =
      ordinaryCoordinateMap R c := by
  simp [ordinaryOverlapToInfinity,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem ordinaryOverlapToInfinity_injective  :
    Function.Injective (ordinaryOverlapToInfinity R) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (OrdinaryOverlapRing R)
    (M := Submonoid.powers (xCoordinate R)) (ordinaryOverlapToInfinity R).toRingHom
  intro a ha
  change ordinaryOverlapToInfinity R (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) a) = 0 at ha
  rw [ordinaryOverlapToInfinity_algebraMap] at ha
  have hh : a = 0 := ordinaryCoordinateMap_injective R (by simpa only [map_zero] using ha)
  rw [hh,map_zero]

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryCoordinateMap_injective
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryOverlapToInfinity_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse-parameter positive reciprocal chart equivalence over arbitrary integral
coefficient rings, with no inversion of two or thirteen, retaining the recovered reciprocal parameter map.
Named downstream consumer: gluing the second finite chart for single-section FiniteMapData.
No whole-curve complement or full FiniteMapData is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticOverlapEquivalence
variable (R : Type u) [CommRing R] [IsDomain R]

theorem ordinaryOverlapToInfinity_inverse_x :
    ordinaryOverlapToInfinity R (IsLocalization.Away.invSelf (xCoordinate R)) =
      infinityLocalizedInclusion R (infinityRecoveredZ R) := by
  apply (ordinaryX_isUnit R).mul_right_inj.mp
  calc
    _ = ordinaryOverlapToInfinity R
      (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R) *
        IsLocalization.Away.invSelf (xCoordinate R)) := by
      rw [map_mul,ordinaryOverlapToInfinity_algebraMap]
      rfl
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf,map_one]
    _ = _ := (ordinaryX_mul_recoveredZ R).symm

theorem ordinaryOverlapToInfinity_reciprocal_z :
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (zCoordinate R)) =
      infinityLocalizedInclusion R (infinityRecoveredZ R) := by
  rw [reciprocalToOrdinaryBase_z]
  change ordinaryOverlapToInfinity R (IsLocalization.Away.invSelf (xCoordinate R)) = _
  exact ordinaryOverlapToInfinity_inverse_x R

theorem ordinaryOverlapToInfinity_reciprocal_w :
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (wCoordinate R)) =
      ordinaryY R *
        infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  rw [reciprocalToOrdinaryBase_w]
  change ordinaryOverlapToInfinity R
    (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R) *
      IsLocalization.Away.invSelf (xCoordinate R) ^ 3) = _
  rw [map_mul,map_pow,ordinaryOverlapToInfinity_algebraMap,ordinaryOverlapToInfinity_inverse_x]
  rfl

theorem recovered_reciprocal_ordinary_comparison_square :
    (infinityLocalizedInclusion R).comp (recoveredReciprocalBase R) =
      (ordinaryOverlapToInfinity R).comp (reciprocalToOrdinaryBase R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change infinityLocalizedInclusion R (recoveredReciprocalBase R (zCoordinate R)) =
      ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (zCoordinate R))
    rw [recoveredReciprocalBase_z,ordinaryOverlapToInfinity_reciprocal_z]
  · change infinityLocalizedInclusion R (recoveredReciprocalBase R (wCoordinate R)) =
      ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R (wCoordinate R))
    rw [recoveredReciprocalBase_w,infinityLocalizedInclusion_recoveredW,
      ordinaryOverlapToInfinity_reciprocal_w]

section IntegralGeometry

theorem actual_reciprocalToOrdinaryBase_injective : Function.Injective (reciprocalToOrdinaryBase R) := by
  have he (a : reciprocalCoordinateRing R) :
      (overlapAlgEquiv R).symm
        (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) =
      reciprocalToOrdinaryBase R a := by
    change reciprocalToOrdinary R
      (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) = _
    exact reciprocalToOrdinary_algebraMap R a
  intro a b hab
  apply Order13MixedSingleSectionFiniteAlgebra.reciprocalOverlap_algebraMap_injective R
  apply (overlapAlgEquiv R).symm.injective
  simpa only [he] using hab

theorem actual_recoveredReciprocalBase_ordinary_composite_injective :
    Function.Injective ((infinityLocalizedInclusion R).comp (recoveredReciprocalBase R)) := by
  rw [recovered_reciprocal_ordinary_comparison_square]
  exact (ordinaryOverlapToInfinity_injective R).comp
    (actual_reciprocalToOrdinaryBase_injective R)

theorem recoveredReciprocalPatch_injective  :
    Function.Injective (recoveredReciprocalPatch R) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)
    (M := Submonoid.powers (Order13MixedInverseParameterPositiveReciprocalPatch.f R *
      Order13MixedInverseParameterPositiveReciprocalPatch.g R))
    (recoveredReciprocalPatch R).toRingHom
  intro a ha
  change recoveredReciprocalPatch R
    (algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R) a) = 0 at ha
  rw [recoveredReciprocalPatch_algebraMap] at ha
  have h := congrArg (infinityLocalizedInclusion R) ha
  have hz : a = 0 := actual_recoveredReciprocalBase_ordinary_composite_injective R
    (by simpa only [AlgHom.comp_apply,map_zero] using h)
  rw [hz,map_zero]

def recoveredReciprocalPatchEquiv : Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R ≃ₐ[R]
    infinityLocalization R :=
  AlgEquiv.ofBijective (recoveredReciprocalPatch R )
    ⟨recoveredReciprocalPatch_injective R ,
      recoveredReciprocalPatch_surjective R ⟩

theorem recoveredReciprocalPatchEquiv_s :
    recoveredReciprocalPatchEquiv R (Order13MixedInverseParameterPositiveReciprocalPatch.s R) = infinityS R :=
  recoveredReciprocalPatch_s R 
theorem recoveredReciprocalPatchEquiv_a :
    recoveredReciprocalPatchEquiv R (Order13MixedInverseParameterPositiveReciprocalPatch.a R) = infinityA R :=
  recoveredReciprocalPatch_a R 
theorem recoveredReciprocalPatchEquiv_b :
    recoveredReciprocalPatchEquiv R (Order13MixedInverseParameterPositiveReciprocalPatch.b R) = infinityB R :=
  recoveredReciprocalPatch_b R 

end IntegralGeometry
end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recovered_reciprocal_ordinary_comparison_square
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_s
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_a
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_b

end


