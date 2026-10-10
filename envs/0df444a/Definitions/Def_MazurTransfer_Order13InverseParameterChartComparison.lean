-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseParameterChartComparison
-- name    : MazurTransfer_Order13InverseParameterChartComparison
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-10T09:30:55.973743+00:00
-- url     : https://prove2.me/theorems/dd92a203-2c20-46f9-b73a-89c2d4323ca6
-- title:
--   Actual inverse-parameter coordinate and chart comparison constructions
-- statement:
--   Let $R$ be a commutative ring. These reusable constructions use the literal ordinary and reciprocal order-$13$ coordinate rings and their actual coefficient maps. In $A[1/t]$ they define $s=1/t$, $a=p/t^2$, $b=q/t^2$, the actual subalgebra $B=R[S][a,b]$, and its localization maps. With $L=1-2s-2b$ and $H=L-4a^2$, the constructions recover
--   $$x=a/s,\qquad y=s^{-1}-x^3-x^2-1,\qquad Z=2b/L,\qquad W=2/H-1-Z-Z^3.$$
--   Closed helper proofs establish the actual finite-algebra identities, principal-open coverage and localization isomorphisms, with the invertibility, domain and noetherianity hypotheses stated where needed. No maps, bases or comparison results are supplied as axioms. The named downstream consumer is the unchanged inverse-parameter localization-chart theorem and the gluing of its actual finite scheme into the original curve.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned recovered reciprocal-coordinate, unit, universal-property and surjectivity proofs using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained. The unchanged public actual-curve geometric-integrality and flatness/smoothness results supply the coordinate-domain proofs; the actual overlap equivalence and faithful localizations prove injectivity. Complete owned inverse-parameter multiplication, finite-algebra, localization, regular reciprocal-coordinate and faithful comparison proofs; no original-source count increment. This reusable library contains only the complete needed owned proofs and exactly recorded primitive fragments. It excludes all open declarations.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Design boundary: checked literal inverse-parameter coordinate and comparison constructions, including their closed helper proofs. Named downstream consumer: the unchanged actual inverse-parameter localization-chart theorem and finite-chart gluing. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
import Definitions.Def_MazurTransfer_Order13InverseParameterCoordinates

namespace InverseParameterChartComparisonLibrary
/- Retained per-file attribution/header for selected primitive fragments from Order13SingleSectionParameterLocalization.lean. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the injective localized inclusion of the actual parameter
subalgebra, with recovered x,y coordinates satisfying the literal sextic.
Named downstream consumer: the actual D(t) affine-chart isomorphism in the
single-section complement comparison. No full complement is asserted.
-/

/- Retained per-file attribution/header for selected primitive fragments from Order13IntegralInfinityChartFaithfulness.lean. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: faithful localizations and the actual ordinary overlap map
on the third single-section chart over noetherian integral bases with 104
invertible. Named downstream consumer: reciprocal-map injectivity.
No reciprocal-chart isomorphism or curve complement is assumed here.
-/

/- Retained per-file attribution/header for selected primitive fragments from Order13SingleSectionReciprocalChartEquivalence.lean. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual third chart equivalence over noetherian integral
bases with 104 invertible, retaining the recovered reciprocal parameter map.
Named downstream consumer: gluing the single-section affine complement.
No whole-curve complement or full FiniteMapData is assumed here.
-/


section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact integral coordinate identities for the candidate
single-infinity pole function and a rank-three finite algebra presentation.
Named downstream consumer: actual single-section FiniteMapData.
These are coordinate-ring identities only. No pole order, affine-open
identification, freeness or finite scheme morphism is claimed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionFiniteMapIdentities
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

def a : CoordinateRing R := xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1
def t : CoordinateRing R := yCoordinate R + a R
def p : CoordinateRing R := xCoordinate R * t R
def q : CoordinateRing R := xCoordinate R * (p R + 2)

theorem candidate_equation :
    t R ^ 2 - 2 * t R * (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1) -
      4 * xCoordinate R * (xCoordinate R + 1) = 0 := by
  have hy := yCoordinate_sq R
  simp only [sexticPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hy
  dsimp [t, a]
  linear_combination hy

theorem p_squared : p R ^ 2 = t R * q R - 2 * p R := by
  dsimp [p, q]
  ring

theorem twice_p_mul_q :
    2 * p R * q R = t R ^ 3 - 2 * t R ^ 2 - 2 * t R * q R := by
  have h := candidate_equation R
  dsimp [p, q]
  linear_combination -(t R) * h

theorem twice_q_squared :
    2 * q R ^ 2 = (t R ^ 2 - 2 * t R) * p R + (2 * t R - 4) * q R +
      (2 - t R) * (t R ^ 2 - 2 * t R) := by
  have h := candidate_equation R
  dsimp [p, q]
  linear_combination (-(t R) * xCoordinate R + t R - 2) * h

theorem reciprocal_difference_of_squares :
    (wCoordinate R + (1 + zCoordinate R + zCoordinate R ^ 3)) *
      (wCoordinate R - (1 + zCoordinate R + zCoordinate R ^ 3)) =
      4 * zCoordinate R ^ 4 * (1 + zCoordinate R) := by
  have hw := wCoordinate_sq R
  simp only [reciprocalPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hw
  linear_combination hw

theorem reciprocal_second_difference_of_squares :
    (wCoordinate R + (1 + zCoordinate R - zCoordinate R ^ 3)) *
      (wCoordinate R - (1 + zCoordinate R - zCoordinate R ^ 3)) =
      4 * zCoordinate R ^ 3 * (1 + zCoordinate R) ^ 2 := by
  have hw := wCoordinate_sq R
  simp only [reciprocalPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hw
  linear_combination hw

end MazurTransfer.Order13SingleSectionFiniteMapIdentities

end
end

noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionFiniteAlgebra
open Order13SingleSectionFiniteMapIdentities
variable (R : Type u) [CommRing R]
abbrev ordinaryParameterLocalization := Localization.Away (t R)
end MazurTransfer.Order13SingleSectionFiniteAlgebra
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)

abbrev equation : Polynomial R := X ^ 2 - C f

def powerBasis : PowerBasis R (AdjoinRoot (equation R f)) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f (by decide))

theorem powerBasis_dim : (powerBasis R f).dim = 2 := by
  change (X ^ 2 - C f).natDegree = 2
  exact Polynomial.natDegree_X_pow_sub_C

def basis : Basis (Fin 2) R (AdjoinRoot (equation R f)) :=
  (powerBasis R f).basis.reindex (finCongr (powerBasis_dim R f))

theorem basis_zero : basis R f 0 = 1 := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 0).val :=
      (powerBasis R f).basis_eq_pow _
    _ = 1 := by simp

theorem basis_one : basis R f 1 = AdjoinRoot.root (equation R f) := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 1).val :=
      (powerBasis R f).basis_eq_pow _
    _ = (powerBasis R f).gen := by simp
    _ = AdjoinRoot.root (equation R f) := rfl

def coordinates : AdjoinRoot (equation R f) ≃ₗ[R] R × R :=
  (basis R f).equivFun.trans (LinearEquiv.finTwoArrow R R)

theorem coordinates_symm (v : R × R) :
    (coordinates R f).symm v = AdjoinRoot.of (equation R f) v.1 +
      AdjoinRoot.of (equation R f) v.2 * AdjoinRoot.root (equation R f) := by
  rw [coordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem coordinates_of_add_of_mul_root (a b : R) :
    coordinates R f (AdjoinRoot.of (equation R f) a +
      AdjoinRoot.of (equation R f) b * AdjoinRoot.root (equation R f)) = (a, b) := by
  rw [← coordinates_symm R f (a, b), LinearEquiv.apply_symm_apply]

end MazurTransfer.QuadraticCoordinates


end
end
section
noncomputable section
universe u
namespace MazurTransfer.Order13ReciprocalInjectionCurveDomains
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (K : Type u) [CommRing K] [IsDomain K] [IsNoetherianRing K]
    (h104 : IsUnit (104 : K))
include h104

theorem curveScheme_isIntegral : IsIntegral (curveScheme K) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    _root_.MazurTransfer.order13_actual_integral_curve_geometrically_integral K h104
  letI : Flat (curveToBase K) := (_root_.MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).1
  letI : Smooth (curveToBase K) := (_root_.MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth K).2.2 h104
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (curveToBase K)

theorem coordinateRing_isDomain : IsDomain (CoordinateRing K) := by
  letI : Nontrivial (CoordinateRing K) := Function.Injective.nontrivial
    (QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).symm.injective
  letI : IsIntegral (curveScheme K) := curveScheme_isIntegral K h104
  have : IsIntegral (MazurTorsion.XOneThirteenAffineCurve.scheme K) :=
    isIntegral_of_isOpenImmersion (ordinaryChartMap K)
  exact (affine_isIntegral_iff (.of (CoordinateRing K))).mp this

theorem reciprocalRing_isDomain : IsDomain (ReciprocalRing K) := by
  letI : Nontrivial (ReciprocalRing K) := Function.Injective.nontrivial
    (QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm.injective
  letI : IsIntegral (curveScheme K) := curveScheme_isIntegral K h104
  have : IsIntegral (reciprocalScheme K) :=
    isIntegral_of_isOpenImmersion (reciprocalChartMap K)
  exact (affine_isIntegral_iff (.of (ReciprocalRing K))).mp this

end MazurTransfer.Order13ReciprocalInjectionCurveDomains

end

end


noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SingleSectionFiniteMapIdentities
variable (R : Type u) [CommRing R]
section DomainCoordinates
variable [IsDomain R]

theorem ordinary_polynomial_inclusion_injective : Function.Injective (AdjoinRoot.of (affineEquation R)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  change (X ^ 2 - C (sexticPolynomial R)).degree ≠ 0
  rw [Polynomial.degree_X_pow_sub_C (by decide)]
  decide

theorem reciprocal_polynomial_inclusion_injective : Function.Injective (AdjoinRoot.of (reciprocalEquation R)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  change (X ^ 2 - C (reciprocalPolynomial R)).degree ≠ 0
  rw [Polynomial.degree_X_pow_sub_C (by decide)]
  decide

theorem actual_ordinary_x_ne_zero : xCoordinate R ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (affineEquation R) X = AdjoinRoot.of (affineEquation R) 0 := by
    simpa only [xCoordinate,map_zero] using h
  exact Polynomial.X_ne_zero (ordinary_polynomial_inclusion_injective R hx)

theorem actual_ordinary_x_add_one_ne_zero : xCoordinate R + 1 ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (affineEquation R) (X + 1) = AdjoinRoot.of (affineEquation R) 0 := by
    simpa only [xCoordinate,map_add,map_one,map_zero] using h
  have hp := ordinary_polynomial_inclusion_injective R hx
  exact Polynomial.X_add_C_ne_zero (1 : R) hp

theorem actual_reciprocal_z_ne_zero : zCoordinate R ≠ 0 := by
  intro h
  have hx : AdjoinRoot.of (reciprocalEquation R) X = AdjoinRoot.of (reciprocalEquation R) 0 := by
    simpa only [zCoordinate,map_zero] using h
  exact Polynomial.X_ne_zero (reciprocal_polynomial_inclusion_injective R hx)

theorem actual_ordinary_parameter_ne_zero : t R ≠ 0 := by
  have heq : t R = AdjoinRoot.of (affineEquation R) (X ^ 3 + X ^ 2 + 1) +
      AdjoinRoot.of (affineEquation R) 1 * AdjoinRoot.root (affineEquation R) := by
    simp only [t,Order13SingleSectionFiniteMapIdentities.a,xCoordinate,yCoordinate,
      map_add,map_pow,map_one]
    ring
  have hcoords := QuadraticCoordinates.coordinates_of_add_of_mul_root (Polynomial R)
    (sexticPolynomial R) (X ^ 3 + X ^ 2 + 1) 1
  change t R = AdjoinRoot.of (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R))
      (X ^ 3 + X ^ 2 + 1) +
    AdjoinRoot.of (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R)) 1 *
      AdjoinRoot.root (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R)) at heq
  rw [← heq] at hcoords
  intro ht
  rw [ht] at hcoords
  change (QuadraticCoordinates.coordinates (Polynomial R) (sexticPolynomial R))
    (0 : AdjoinRoot (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R))) =
      (X ^ 3 + X ^ 2 + 1,1) at hcoords
  rw [map_zero] at hcoords
  have hh := congrArg Prod.snd hcoords
  exact one_ne_zero hh.symm

end DomainCoordinates
theorem two_isUnit_of_104 (h104 : IsUnit (104 : R)) : IsUnit (2 : R) := by
  have he : (104 : R) = 2 * 52 := by norm_num
  rw [he] at h104
  exact isUnit_of_mul_isUnit_left h104


section
variable [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R))
include h104
theorem reciprocalOverlap_algebraMap_injective :
    Function.Injective (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R)) := by
  letI : IsDomain (ReciprocalRing R) := Order13ReciprocalInjectionCurveDomains.reciprocalRing_isDomain R h104
  exact IsLocalization.injective (ReciprocalOverlapRing R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (actual_reciprocal_z_ne_zero R))


end
end MazurTransfer.Order13SingleSectionFiniteAlgebra
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two actual infinity sections of the literal order-13 curve
for every commutative base ring, constructed from reciprocal coordinates.
Named downstream consumer: integral Picard representability with a section.
No rational-point classification or Picard representability is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralSections
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

private theorem reciprocalEquation_eval (a : R) (ha : a ^ 2 = 1) :
    (reciprocalEquation R).eval₂ (Polynomial.evalRingHom (0 : R)) a = 0 := by
  simp [reciprocalEquation, reciprocalPolynomial, ha, eval₂_pow, eval₂_C]

noncomputable def reciprocalInfinityEvaluation (a : R) (ha : a ^ 2 = 1) :
    ReciprocalRing R →+* R :=
  AdjoinRoot.lift (Polynomial.evalRingHom (0 : R)) a
    (reciprocalEquation_eval R a ha)

theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simp [reciprocalInfinityEvaluation, zCoordinate, AdjoinRoot.lift_of]

theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simp [reciprocalInfinityEvaluation, wCoordinate, AdjoinRoot.lift_root]

theorem reciprocalInfinityEvaluation_comp_algebraMap (a : R) (ha : a ^ 2 = 1) :
    (reciprocalInfinityEvaluation R a ha).comp
      (algebraMap R (ReciprocalRing R)) = RingHom.id R := by
  ext r
  simp [reciprocalInfinityEvaluation, AdjoinRoot.algebraMap_eq',
    AdjoinRoot.lift_of]


end MazurTransfer.Order13IntegralSections
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact multiplication table for inverse-parameter coordinates
in the literal localization of the ordinary chart at t. Named downstream
consumer: the second finite coordinate algebra in single-section FiniteMapData.
No affine identification or finite morphism for the second chart is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterPolynomialIdentities
open MazurTorsion.XOneThirteenAffineCurve
open MazurTransfer.Order13SingleSectionFiniteMapIdentities
open MazurTransfer.Order13SingleSectionFiniteAlgebra
variable (R : Type u) [CommRing R]

def s : ordinaryParameterLocalization R := IsLocalization.Away.invSelf (t R)
def a : ordinaryParameterLocalization R :=
  algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (p R) * s R ^ 2
def b : ordinaryParameterLocalization R :=
  algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (q R) * s R ^ 2

private theorem inverse_table {A : Type u} [CommRing A] (T P Q S : A)
    (hS : T * S = 1) (hP : P ^ 2 = T * Q - 2 * P)
    (hPQ : 2 * P * Q = T ^ 3 - 2 * T ^ 2 - 2 * T * Q)
    (hQ : 2 * Q ^ 2 = (T ^ 2 - 2 * T) * P + (2 * T - 4) * Q +
      (2 - T) * (T ^ 2 - 2 * T)) :
    (P * S ^ 2) ^ 2 = S * (Q * S ^ 2) - 2 * S ^ 2 * (P * S ^ 2) ∧
    2 * (P * S ^ 2) * (Q * S ^ 2) = S - 2 * S ^ 2 - 2 * S * (Q * S ^ 2) ∧
    2 * (Q * S ^ 2) ^ 2 = (1 - 2 * S) * (P * S ^ 2) +
      (2 * S - 4 * S ^ 2) * (Q * S ^ 2) + (4 * S ^ 2 - 4 * S ^ 3 - S) := by
  constructor
  · linear_combination S ^ 4 * hP + S ^ 3 * Q * hS
  constructor
  · linear_combination S ^ 4 * hPQ +
      (S * (T ^ 2 * S ^ 2 + T * S + 1) - 2 * S ^ 2 * (T * S + 1) -
        2 * S ^ 3 * Q) * hS
  · linear_combination S ^ 4 * hQ +
      (P * S ^ 2 * (T * S + 1 - 2 * S) + 2 * Q * S ^ 3 -
        S * (T ^ 2 * S ^ 2 + T * S + 1) + 4 * S ^ 2 * (T * S + 1) -
        4 * S ^ 3) * hS

theorem actual_inverse_parameter_multiplication_table :
    a R ^ 2 = s R * b R - 2 * s R ^ 2 * a R ∧
    2 * a R * b R = s R - 2 * s R ^ 2 - 2 * s R * b R ∧
    2 * b R ^ 2 = (1 - 2 * s R) * a R +
      (2 * s R - 4 * s R ^ 2) * b R + (4 * s R ^ 2 - 4 * s R ^ 3 - s R) := by
  let f := algebraMap (CoordinateRing R) (ordinaryParameterLocalization R)
  have hP := congrArg f (p_squared R)
  have hPQ := congrArg f (twice_p_mul_q R)
  have hQ := congrArg f (twice_q_squared R)
  simp only [map_pow,map_mul,map_sub,map_add,_root_.map_ofNat] at hP hPQ hQ
  exact inverse_table (f (t R)) (f (p R)) (f (q R)) (s R)
    (IsLocalization.Away.mul_invSelf (t R)) hP hPQ hQ

end MazurTransfer.Order13InverseParameterPolynomialIdentities

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse-parameter coordinate subalgebra in A[1/t]
is finite over R[S], S mapping to 1/t, with span 1,p/t²,q/t².
Named downstream consumer: the second finite chart in single-section FiniteMapData.
The curve-open identification and chart coverage are separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial Submodule
open MazurTorsion.XOneThirteenAffineCurve
open MazurTransfer.Order13InverseParameterPolynomialIdentities
open MazurTransfer.Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

noncomputable def parameterMap : Polynomial R →+* ordinaryParameterLocalization R := (aeval (s R)).toRingHom
scoped instance parameterAlgebra : Algebra (Polynomial R) (ordinaryParameterLocalization R) :=
  (parameterMap R).toAlgebra
scoped instance parameterSMul : SMul (Polynomial R) (ordinaryParameterLocalization R) :=
  (parameterAlgebra R).toSMul
scoped instance parameterModule : Module (Polynomial R) (ordinaryParameterLocalization R) :=
  @Algebra.toModule (Polynomial R) (ordinaryParameterLocalization R) _ _ (parameterAlgebra R)

theorem parameter_algebraMap (f : Polynomial R) :
    algebraMap (Polynomial R) (ordinaryParameterLocalization R) f = aeval (s R) f := rfl

def generators : Set (ordinaryParameterLocalization R) := {1, a R, b R}
def spanningModule : Submodule (Polynomial R) (ordinaryParameterLocalization R) :=
  Submodule.span (Polynomial R) (generators R)
noncomputable def candidateAlgebra : Subalgebra (Polynomial R) (ordinaryParameterLocalization R) :=
  Algebra.adjoin (Polynomial R) ({a R, b R} : Set (ordinaryParameterLocalization R))

private theorem one_mem_span : (1 : ordinaryParameterLocalization R) ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem p_mem_span : a R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem q_mem_span : b R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])

private theorem p_mul_p_mem : a R * a R ∈ spanningModule R := by
  rw [← pow_two, (actual_inverse_parameter_multiplication_table R).1]
  have ht : s R * b R = (X : Polynomial R) • b R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have h2 : 2 * s R ^ 2 * a R = (2 * X ^ 2 : Polynomial R) • a R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [ht, h2]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (q_mem_span R))
    ((spanningModule R).smul_mem _ (p_mem_span R))

private theorem cancel_two_membership (h2 : IsUnit (2 : R)) (v : ordinaryParameterLocalization R)
    (hv : (2 : ordinaryParameterLocalization R) * v ∈ spanningModule R) : v ∈ spanningModule R := by
  obtain ⟨unit, hunit⟩ := h2
  let c : Polynomial R := C (↑(unit⁻¹) : R)
  have hc : (2 : Polynomial R) * c = 1 := by
    dsimp [c]
    rw [← C_ofNat, ← C_mul, ← hunit]
    simp
  have ha : (2 : ordinaryParameterLocalization R) * algebraMap (Polynomial R) (ordinaryParameterLocalization R) c = 1 := by
    simpa only [_root_.map_mul, _root_.map_ofNat, _root_.map_one] using
      congrArg (algebraMap (Polynomial R) (ordinaryParameterLocalization R)) hc
  have h : c • ((2 : ordinaryParameterLocalization R) * v) = v := by
    rw [Algebra.smul_def]
    calc
      _ = ((2 : ordinaryParameterLocalization R) * algebraMap (Polynomial R) (ordinaryParameterLocalization R) c) * v := by ring
      _ = v := by rw [ha, one_mul]
  rw [← h]
  exact (spanningModule R).smul_mem c hv

private theorem p_mul_q_mem (h2 : IsUnit (2 : R)) : a R * b R ∈ spanningModule R := by
  apply cancel_two_membership R h2
  rw [← mul_assoc, (actual_inverse_parameter_multiplication_table R).2.1]
  have h1 : s R - 2 * s R ^ 2 = (X - 2 * X ^ 2 : Polynomial R) • (1 : ordinaryParameterLocalization R) := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hq : 2 * s R * b R = (2 * X : Polynomial R) • b R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [h1, hq]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (one_mem_span R))
    ((spanningModule R).smul_mem _ (q_mem_span R))

private theorem q_mul_q_mem (h2 : IsUnit (2 : R)) : b R * b R ∈ spanningModule R := by
  apply cancel_two_membership R h2
  rw [← pow_two, (actual_inverse_parameter_multiplication_table R).2.2]
  have hp : (1 - 2 * s R) * a R = (1 - 2 * X : Polynomial R) • a R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hq : (2 * s R - 4 * s R ^ 2) * b R = (2 * X - 4 * X ^ 2 : Polynomial R) • b R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hc : 4 * s R ^ 2 - 4 * s R ^ 3 - s R =
      (4 * X ^ 2 - 4 * X ^ 3 - X : Polynomial R) • (1 : ordinaryParameterLocalization R) := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [hp, hq, hc]
  exact (spanningModule R).add_mem
    ((spanningModule R).add_mem ((spanningModule R).smul_mem _ (p_mem_span R))
      ((spanningModule R).smul_mem _ (q_mem_span R)))
    ((spanningModule R).smul_mem _ (one_mem_span R))

theorem spanningModule_mul_closed (h2 : IsUnit (2 : R))
    (v w : ordinaryParameterLocalization R) (hv : v ∈ spanningModule R) (hw : w ∈ spanningModule R) :
    v * w ∈ spanningModule R := by
  have hle : spanningModule R * spanningModule R ≤ spanningModule R := by
    change span (Polynomial R) (generators R) * span (Polynomial R) (generators R) ≤ _
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · simpa using one_mem_span R
    · simpa using p_mem_span R
    · simpa using q_mem_span R
    · simpa using p_mem_span R
    · exact p_mul_p_mem R
    · exact p_mul_q_mem R h2
    · simpa using q_mem_span R
    · change b R * a R ∈ spanningModule R
      rw [mul_comm]
      exact p_mul_q_mem R h2
    · exact q_mul_q_mem R h2
  exact hle (Submodule.mul_mem_mul hv hw)

theorem candidateAlgebra_eq_span (h2 : IsUnit (2 : R)) :
    (candidateAlgebra R).toSubmodule = spanningModule R := by
  let S : Subalgebra (Polynomial R) (ordinaryParameterLocalization R) :=
    (spanningModule R).toSubalgebra (one_mem_span R) (spanningModule_mul_closed R h2)
  have hBS : candidateAlgebra R ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rcases hz with rfl | rfl
    · exact p_mem_span R
    · exact q_mem_span R
  apply le_antisymm
  · exact fun _ hz => hBS hz
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (candidateAlgebra R).one_mem
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)

theorem candidateAlgebra_finite (h2 : IsUnit (2 : R)) :
    Module.Finite (Polynomial R) (candidateAlgebra R) := by
  change Module.Finite (Polynomial R) (candidateAlgebra R).toSubmodule
  apply Module.Finite.of_fg
  rw [candidateAlgebra_eq_span R h2]
  exact Submodule.fg_span (by simp [generators])

open AlgebraicGeometry CategoryTheory

def inverseFiniteAffineScheme : Scheme := Spec (.of (candidateAlgebra R))

def inverseFiniteAffineMap : inverseFiniteAffineScheme R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R)))

theorem inverseFiniteAffineMap_isFinite (h2 : IsUnit (2 : R)) :
    IsFinite (inverseFiniteAffineMap R) := by
  letI := candidateAlgebra_finite R h2
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial R) (candidateAlgebra R))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

def ordinaryLocalizedToInverseFinite : Spec (.of (ordinaryParameterLocalization R)) ⟶
    inverseFiniteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom)

theorem ordinaryLocalizedToInverseFinite_parameter :
    ordinaryLocalizedToInverseFinite R ≫ inverseFiniteAffineMap R =
      Spec.map (CommRingCat.ofHom (parameterMap R)) := by
  change Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (candidateAlgebra R).val.commutes f

theorem ordinaryLocalizedToInverseFinite_base :
    ordinaryLocalizedToInverseFinite R ≫ inverseFiniteAffineMap R ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryParameterLocalization R))) := by
  rw [← Category.assoc, ordinaryLocalizedToInverseFinite_parameter, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [parameterMap]

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal inverse-parameter algebra localized at s=1/t
is isomorphic to the actual ordinary t-localization, with the inclusion and
coefficient maps retained. Named downstream consumer: the ordinary chart of
the second finite curve chart in single-section FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13InverseParameterPolynomialIdentities
open Order13SingleSectionFiniteMapIdentities (t p)
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

scoped instance candidateBaseAlgebra : Algebra R (candidateAlgebra R) :=
  ((algebraMap (Polynomial R) (candidateAlgebra R)).comp Polynomial.C).toAlgebra
scoped instance candidateBaseTower : IsScalarTower R (Polynomial R) (candidateAlgebra R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def sElement : candidateAlgebra R := algebraMap (Polynomial R) (candidateAlgebra R) X
def aElement : candidateAlgebra R := ⟨a R, Algebra.subset_adjoin (by simp)⟩
def bElement : candidateAlgebra R := ⟨b R, Algebra.subset_adjoin (by simp)⟩
abbrev parameterLocalization := Localization.Away (sElement R)

def inclusion : candidateAlgebra R →ₐ[R] ordinaryParameterLocalization R where
  __ := (candidateAlgebra R).val.toRingHom
  commutes' r := by change aeval (s R) (C r) = _; exact aeval_C _ _

theorem inclusion_sElement : inclusion R (sElement R) = s R := by
  change aeval (s R) X = s R
  exact aeval_X _

theorem s_isUnit : IsUnit (s R) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R),?_⟩
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf (t R)

def localizedInclusion : parameterLocalization R →ₐ[R] ordinaryParameterLocalization R :=
  IsLocalization.Away.liftAlgHom (sElement R) (f := inclusion R)
    (by rw [inclusion_sElement]; exact s_isUnit R)

theorem localizedInclusion_algebraMap (c : candidateAlgebra R) :
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) c) =
      (c : ordinaryParameterLocalization R) := by
  simp [localizedInclusion, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq,
    inclusion]

theorem localizedInclusion_injective : Function.Injective (localizedInclusion R) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (sElement R))
    (localizedInclusion R).toRingHom).mpr
  intro x y
  change algebraMap (candidateAlgebra R) (parameterLocalization R) x =
    algebraMap (candidateAlgebra R) (parameterLocalization R) y ↔
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) x) =
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) y)
  rw [localizedInclusion_algebraMap,localizedInclusion_algebraMap]
  constructor
  · intro h
    have H := congrArg (localizedInclusion R) h
    simpa only [localizedInclusion_algebraMap] using H
  · intro h
    exact congrArg (algebraMap (candidateAlgebra R) (parameterLocalization R)) (Subtype.ext h)

theorem localizedInclusion_invSelf :
    localizedInclusion R (IsLocalization.Away.invSelf (sElement R)) =
      algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R) := by
  apply (s_isUnit R).mul_right_inj.mp
  calc
    _ = localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R)
      (sElement R) * IsLocalization.Away.invSelf (sElement R)) := by
      rw [map_mul, localizedInclusion_algebraMap]
      change s R * _ = aeval (s R) X * _
      rw [aeval_X]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf,map_one]
    _ = _ := by rw [mul_comm]; exact (IsLocalization.Away.mul_invSelf (t R)).symm

def recoveredX : parameterLocalization R :=
  algebraMap (candidateAlgebra R) (parameterLocalization R) (aElement R) *
    IsLocalization.Away.invSelf (sElement R)
def recoveredY : parameterLocalization R := IsLocalization.Away.invSelf (sElement R) -
  recoveredX R ^ 3 - recoveredX R ^ 2 - 1

theorem localizedInclusion_recoveredX : localizedInclusion R (recoveredX R) =
    algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) := by
  rw [recoveredX,map_mul,localizedInclusion_algebraMap,localizedInclusion_invSelf]
  change a R * algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R) = _
  have ht := IsLocalization.Away.mul_invSelf (t R) (S := ordinaryParameterLocalization R)
  dsimp [a,p,s]
  rw [map_mul]
  calc
    _ = algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) *
      (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R) *
        IsLocalization.Away.invSelf (t R)) ^ 2 := by ring
    _ = _ := by rw [ht]; simp

theorem localizedInclusion_recoveredY : localizedInclusion R (recoveredY R) =
    algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (yCoordinate R) := by
  rw [recoveredY,map_sub,map_sub,map_sub,map_pow,map_pow,map_one,
    localizedInclusion_invSelf,localizedInclusion_recoveredX]
  simp only [t,Order13SingleSectionFiniteMapIdentities.a,map_add,map_pow,map_one]
  ring

theorem recovered_equation : recoveredY R ^ 2 = aeval (recoveredX R) (sexticPolynomial R) := by
  apply localizedInclusion_injective R
  rw [map_pow,localizedInclusion_recoveredY,← aeval_algHom_apply,localizedInclusion_recoveredX]
  let f := IsScalarTower.toAlgHom R (CoordinateRing R) (ordinaryParameterLocalization R)
  change f (yCoordinate R) ^ 2 = aeval (f (xCoordinate R)) (sexticPolynomial R)
  rw [aeval_algHom_apply]
  simpa only [map_pow] using congrArg f (yCoordinate_sq R)

def inverseOnOrdinary : CoordinateRing R →ₐ[R] parameterLocalization R :=
  solutionToAlgHom (parameterLocalization R) ⟨(recoveredX R,recoveredY R),recovered_equation R⟩

theorem inverseOnOrdinary_x : inverseOnOrdinary R (xCoordinate R) = recoveredX R :=
  solutionToAlgHom_x _ _
theorem inverseOnOrdinary_y : inverseOnOrdinary R (yCoordinate R) = recoveredY R :=
  solutionToAlgHom_y _ _
theorem inverseOnOrdinary_t : inverseOnOrdinary R (t R) =
    IsLocalization.Away.invSelf (sElement R) := by
  simp only [t,Order13SingleSectionFiniteMapIdentities.a,map_add,map_pow,map_one,
    inverseOnOrdinary_x,inverseOnOrdinary_y]
  rw [recoveredY]
  ring

def inverseLocalizedInclusion : ordinaryParameterLocalization R →ₐ[R] parameterLocalization R :=
  IsLocalization.Away.liftAlgHom (t R) (f := inverseOnOrdinary R) (by
    rw [inverseOnOrdinary_t]
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap (candidateAlgebra R) (parameterLocalization R) (sElement R),?_⟩
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (sElement R))

theorem inverseLocalizedInclusion_algebraMap (z : CoordinateRing R) :
    inverseLocalizedInclusion R (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) z) =
      inverseOnOrdinary R z := by
  simp [inverseLocalizedInclusion,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem localizedInclusion_comp_inverseOnOrdinary :
    (localizedInclusion R).comp (inverseOnOrdinary R) =
      IsScalarTower.toAlgHom R (CoordinateRing R) (ordinaryParameterLocalization R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change localizedInclusion R (inverseOnOrdinary R (xCoordinate R)) = _
    rw [inverseOnOrdinary_x,localizedInclusion_recoveredX]
    rfl
  · change localizedInclusion R (inverseOnOrdinary R (yCoordinate R)) = _
    rw [inverseOnOrdinary_y,localizedInclusion_recoveredY]
    rfl

theorem localizedInclusion_inverseLocalizedInclusion :
    (localizedInclusion R).comp (inverseLocalizedInclusion R) =
      AlgHom.id R (ordinaryParameterLocalization R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (t R))
  apply RingHom.ext
  intro z
  change localizedInclusion R (inverseLocalizedInclusion R
    (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) z)) = _
  rw [inverseLocalizedInclusion_algebraMap]
  exact DFunLike.congr_fun (localizedInclusion_comp_inverseOnOrdinary R) z

theorem inverseLocalizedInclusion_localizedInclusion :
    (inverseLocalizedInclusion R).comp (localizedInclusion R) =
      AlgHom.id R (parameterLocalization R) := by
  apply AlgHom.ext
  intro z
  apply localizedInclusion_injective R
  exact DFunLike.congr_fun (localizedInclusion_inverseLocalizedInclusion R) (localizedInclusion R z)

def parameterLocalizationEquiv : parameterLocalization R ≃ₐ[R] ordinaryParameterLocalization R :=
  AlgEquiv.ofAlgHom (localizedInclusion R) (inverseLocalizedInclusion R)
    (localizedInclusion_inverseLocalizedInclusion R) (inverseLocalizedInclusion_localizedInclusion R)

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual polynomial identities and a two-principal-open cover
of the inverse finite coordinate algebra. Named downstream consumer: recover
reciprocal coordinates on the positive-infinity chart of FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open AlgebraicGeometry Polynomial
open Order13InverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

def infinityLinearElement : candidateAlgebra R := 1 - 2 * sElement R - 2 * bElement R
def infinityRootElement : candidateAlgebra R := infinityLinearElement R - 4 * aElement R ^ 2
def infinityPatchElement : candidateAlgebra R := infinityRootElement R * infinityLinearElement R

theorem candidate_multiplication_table :
    aElement R ^ 2 = sElement R * bElement R - 2 * sElement R ^ 2 * aElement R ∧
    2 * aElement R * bElement R = sElement R - 2 * sElement R ^ 2 - 2 * sElement R * bElement R ∧
    2 * bElement R ^ 2 = (1 - 2 * sElement R) * aElement R +
      (2 * sElement R - 4 * sElement R ^ 2) * bElement R +
      (4 * sElement R ^ 2 - 4 * sElement R ^ 3 - sElement R) := by
  have h := actual_inverse_parameter_multiplication_table R
  refine ⟨?_,?_,?_⟩ <;> apply Subtype.val_injective
  · change a R ^ 2 = aeval (s R) X * b R - 2 * aeval (s R) X ^ 2 * a R
    simpa only [aeval_X] using h.1
  · change 2 * a R * b R = aeval (s R) X - 2 * aeval (s R) X ^ 2 - 2 * aeval (s R) X * b R
    simpa only [aeval_X] using h.2.1
  · change 2 * b R ^ 2 = (1 - 2 * aeval (s R) X) * a R +
      (2 * aeval (s R) X - 4 * aeval (s R) X ^ 2) * b R +
      (4 * aeval (s R) X ^ 2 - 4 * aeval (s R) X ^ 3 - aeval (s R) X)
    simpa only [aeval_X] using h.2.2

theorem twice_a_mul_b : 2 * aElement R * bElement R = sElement R * infinityLinearElement R := by
  have h := (candidate_multiplication_table R).2.1
  dsimp [infinityLinearElement]
  linear_combination h

theorem twice_b_squared : 2 * bElement R ^ 2 =
    (aElement R + 2 * sElement R ^ 2) * infinityLinearElement R := by
  have h2 := (candidate_multiplication_table R).2.1
  have h3 := (candidate_multiplication_table R).2.2
  dsimp [infinityLinearElement]
  linear_combination h3 + h2

theorem s_squared_mul_root : sElement R ^ 2 * infinityRootElement R = 2 * aElement R ^ 3 := by
  have h1 := (candidate_multiplication_table R).1
  have h2 := (candidate_multiplication_table R).2.1
  dsimp [infinityRootElement,infinityLinearElement]
  linear_combination -(2 * aElement R) * h1 - sElement R * h2

theorem twice_b_squared_mul_root : 2 * bElement R ^ 2 * infinityRootElement R =
    aElement R * infinityLinearElement R ^ 2 := by
  have h1 := twice_b_squared R
  have h2 := s_squared_mul_root R
  dsimp [infinityRootElement] at h2 ⊢
  linear_combination (infinityLinearElement R - 4 * aElement R ^ 2) * h1 +
    2 * infinityLinearElement R * h2

theorem s_mem_prime_forces_a_b (h2 : IsUnit (2 : R))
    (p : PrimeSpectrum (candidateAlgebra R)) (hs : sElement R ∈ p.asIdeal) :
    aElement R ∈ p.asIdeal ∧ bElement R ∈ p.asIdeal := by
  have ha2 : aElement R ^ 2 ∈ p.asIdeal := by
    rw [(candidate_multiplication_table R).1]
    exact p.asIdeal.sub_mem (p.asIdeal.mul_mem_right _ hs)
      (p.asIdeal.mul_mem_right _ (p.asIdeal.mul_mem_left _ (p.asIdeal.pow_mem_of_mem hs 2 (by decide))))
  have ha := p.isPrime.mem_of_pow_mem 2 ha2
  have hb2 : 2 * bElement R ^ 2 ∈ p.asIdeal := by
    rw [twice_b_squared]
    exact p.asIdeal.mul_mem_right _ (p.asIdeal.add_mem ha
      (p.asIdeal.mul_mem_left _ (p.asIdeal.pow_mem_of_mem hs 2 (by decide))))
  have htwo : (2 : candidateAlgebra R) ∉ p.asIdeal := by
    intro ht
    have hu : IsUnit (2 : candidateAlgebra R) := by
      simpa only [_root_.map_ofNat] using h2.map (algebraMap R (candidateAlgebra R))
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem ht hu)
  exact ⟨ha, p.isPrime.mem_of_pow_mem 2 ((p.isPrime.mem_or_mem hb2).resolve_left htwo)⟩

theorem s_mem_prime_forces_patch_nonmem (h2 : IsUnit (2 : R))
    (p : PrimeSpectrum (candidateAlgebra R)) (hs : sElement R ∈ p.asIdeal) :
    infinityPatchElement R ∉ p.asIdeal := by
  obtain ⟨ha,hb⟩ := s_mem_prime_forces_a_b R h2 p hs
  have hc : 2 * sElement R + 2 * bElement R ∈ p.asIdeal :=
    p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hs) (p.asIdeal.mul_mem_left _ hb)
  have hl : infinityLinearElement R ∉ p.asIdeal := by
    intro h
    have h1 := p.asIdeal.add_mem h hc
    have he : infinityLinearElement R + (2 * sElement R + 2 * bElement R) = 1 := by
      dsimp [infinityLinearElement]; ring
    rw [he] at h1
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h1 isUnit_one)
  have hr : infinityRootElement R ∉ p.asIdeal := by
    intro h
    have h1 := p.asIdeal.add_mem h (p.asIdeal.mul_mem_left 4
      (p.asIdeal.pow_mem_of_mem ha 2 (by decide)))
    change infinityLinearElement R - 4 * aElement R ^ 2 + 4 * aElement R ^ 2 ∈ p.asIdeal at h1
    rw [sub_add_cancel] at h1
    exact hl h1
  intro h
  exact (p.isPrime.mem_or_mem h).elim hr hl

theorem inverse_candidate_two_principal_open_cover (h2 : IsUnit (2 : R)) :
    PrimeSpectrum.basicOpen (sElement R) ⊔ PrimeSpectrum.basicOpen (infinityPatchElement R) = ⊤ := by
  apply SetLike.ext
  intro p
  change (sElement R ∉ p.asIdeal ∨ infinityPatchElement R ∉ p.asIdeal) ↔ True
  constructor
  · intro _; trivial
  · intro _
    by_cases hs : sElement R ∈ p.asIdeal
    · exact Or.inr (s_mem_prime_forces_patch_nonmem R h2 p hs)
    · exact Or.inl hs

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual regular inverse-parameter coordinates on a literal
reciprocal principal-open neighborhood of the positive infinity section.
Named downstream consumer: the positive-infinity chart isomorphism of the
second finite chart in single-section FiniteMapData. No isomorphism is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterPositiveReciprocalPatch
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

def f : ReciprocalRing R := wCoordinate R + (1 + zCoordinate R + zCoordinate R ^ 3)
def g : ReciprocalRing R := f R + 2 * zCoordinate R ^ 4
abbrev PatchRing := Localization.Away (f R * g R)
def z : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (zCoordinate R)
def w : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (wCoordinate R)
def F : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (f R)
def G : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (g R)
def r : PatchRing R := G R * IsLocalization.Away.invSelf (f R * g R)

theorem F_mul_r : F R * r R = 1 := by
  rw [r,← mul_assoc]
  change algebraMap (ReciprocalRing R) (PatchRing R) (f R) *
    algebraMap (ReciprocalRing R) (PatchRing R) (g R) * _ = 1
  rw [← map_mul,IsLocalization.Away.mul_invSelf]

theorem r_isUnit : IsUnit (r R) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨F R,by rw [mul_comm];exact F_mul_r R⟩

theorem F_mul_G_isUnit : IsUnit (F R * G R) := by
  change IsUnit (algebraMap (ReciprocalRing R) (PatchRing R) (f R) *
    algebraMap (ReciprocalRing R) (PatchRing R) (g R))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (f R * g R)

theorem G_isUnit : IsUnit (G R) := isUnit_of_mul_isUnit_right (F_mul_G_isUnit R)

theorem F_equation : F R ^ 2 - 2 * (1 + z R + z R ^ 3) * F R -
    4 * z R ^ 4 * (1 + z R) = 0 := by
  have h := congrArg (algebraMap (ReciprocalRing R) (PatchRing R))
    (Order13SingleSectionFiniteMapIdentities.reciprocal_difference_of_squares R)
  simp only [map_mul,map_add,map_sub,map_pow,map_one,_root_.map_ofNat] at h
  dsimp [F,f,z]
  simp only [map_add,map_pow,map_one]
  linear_combination h

theorem inverse_profile : 1 = 2 * (1 + z R + z R ^ 3) * r R +
    4 * z R ^ 4 * (1 + z R) * r R ^ 2 := by
  have hF := F_equation R
  have hFr := F_mul_r R
  linear_combination r R ^ 2 * hF -
    (F R * r R + 1 - 2 * (1 + z R + z R ^ 3) * r R) * hFr

def s : PatchRing R := z R ^ 3 * r R
def a : PatchRing R := z R ^ 2 * r R
def b : PatchRing R := z R * r R + 2 * z R ^ 5 * r R ^ 2

theorem root_profile : 1 - 2 * s R - 2 * b R - 4 * a R ^ 2 = 2 * r R := by
  have h := inverse_profile R
  dsimp [s,a,b]
  linear_combination h

theorem linear_profile : 1 - 2 * s R - 2 * b R = 2 * r R ^ 2 * G R := by
  have h := root_profile R
  have hFr := F_mul_r R
  have hG : G R = F R + 2 * z R ^ 4 := by
    simp only [G,g,map_add,map_mul,map_pow,_root_.map_ofNat]
    rfl
  rw [hG]
  dsimp [a] at h
  linear_combination h - 2 * r R * hFr

theorem root_times_linear_isUnit (h2 : IsUnit (2 : R)) :
    IsUnit ((1 - 2 * s R - 2 * b R - 4 * a R ^ 2) * (1 - 2 * s R - 2 * b R)) := by
  rw [root_profile,linear_profile]
  have hu : IsUnit (2 : PatchRing R) := by
    simpa only [_root_.map_ofNat] using h2.map (algebraMap R (PatchRing R))
  exact (hu.mul (r_isUnit R)).mul ((hu.mul ((r_isUnit R).pow 2)).mul (G_isUnit R))

theorem inverse_parameter_multiplication_table :
    a R ^ 2 = s R * b R - 2 * s R ^ 2 * a R ∧
    2 * a R * b R = s R - 2 * s R ^ 2 - 2 * s R * b R ∧
    2 * b R ^ 2 = (1 - 2 * s R) * a R + (2 * s R - 4 * s R ^ 2) * b R +
      (4 * s R ^ 2 - 4 * s R ^ 3 - s R) := by
  have hab : 2 * a R * b R = s R - 2 * s R ^ 2 - 2 * s R * b R := by
    have h := inverse_profile R
    dsimp [s,a,b]
    linear_combination -(z R ^ 3 * r R) * h
  have hb : 2 * b R ^ 2 = (a R + 2 * s R ^ 2) * (1 - 2 * s R - 2 * b R) := by
    have h := root_profile R
    have he : 1 - 2 * s R - 2 * b R = 2 * r R + 4 * a R ^ 2 := by linear_combination h
    rw [he]
    dsimp [s,a,b]
    ring
  refine ⟨?_,hab,?_⟩
  · dsimp [s,a,b];ring
  · linear_combination hb - hab

theorem positive_infinity_denominator :
    Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp) (f R * g R) = 4 := by
  simp [f,g,Order13IntegralSections.reciprocalInfinityEvaluation_z,
    Order13IntegralSections.reciprocalInfinityEvaluation_w]
  ring

theorem negative_infinity_denominator :
    Order13IntegralSections.reciprocalInfinityEvaluation R (-1) (by simp) (f R * g R) = 0 := by
  simp [f,g,Order13IntegralSections.reciprocalInfinityEvaluation_z,
    Order13IntegralSections.reciprocalInfinityEvaluation_w]

end MazurTransfer.Order13InverseParameterPositiveReciprocalPatch

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: recover literal reciprocal z,w on the positive-infinity
localization of the actual inverse finite algebra and construct its actual
reciprocal-patch map. Named downstream consumer: the second chart comparison
for single-section FiniteMapData. Bijectivity is a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

abbrev infinityLocalization := Localization.Away (infinityPatchElement R)
def infinityS : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (sElement R)
def infinityA : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (aElement R)
def infinityB : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (bElement R)
def infinityH : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R)
def infinityL : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R)
def infinityHInverse : infinityLocalization R := infinityL R * IsLocalization.Away.invSelf (infinityPatchElement R)
def infinityLInverse : infinityLocalization R := infinityH R * IsLocalization.Away.invSelf (infinityPatchElement R)

theorem infinityH_mul_inverse : infinityH R * infinityHInverse R = 1 := by
  rw [infinityHInverse,← mul_assoc]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) * _ = 1
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf (infinityPatchElement R)

theorem infinityL_mul_inverse : infinityL R * infinityLInverse R = 1 := by
  rw [infinityLInverse,← mul_assoc,mul_comm (infinityL R) (infinityH R)]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) * _ = 1
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf (infinityPatchElement R)

theorem infinityH_isUnit : IsUnit (infinityH R) :=
  isUnit_iff_exists_inv.mpr ⟨infinityHInverse R,infinityH_mul_inverse R⟩
theorem infinityL_isUnit : IsUnit (infinityL R) :=
  isUnit_iff_exists_inv.mpr ⟨infinityLInverse R,infinityL_mul_inverse R⟩

theorem infinity_H_eq_L_sub : infinityH R = infinityL R - 4 * infinityA R ^ 2 := by
  simp only [infinityH,infinityRootElement,map_sub,map_mul,map_pow,_root_.map_ofNat,infinityL,infinityA]

theorem infinity_L_profile : infinityL R = 1 - 2 * infinityS R - 2 * infinityB R := by
  simp only [infinityL,infinityLinearElement,map_sub,map_mul,map_one,_root_.map_ofNat,infinityS,infinityB]

theorem infinity_twice_A_B : 2 * infinityA R * infinityB R = infinityS R * infinityL R := by
  simpa only [map_mul,_root_.map_ofNat,infinityA,infinityB,infinityS,infinityL] using
    congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) (twice_a_mul_b R)

theorem infinity_twice_B_squared_H : 2 * infinityB R ^ 2 * infinityH R = infinityA R * infinityL R ^ 2 := by
  simpa only [map_mul,map_pow,_root_.map_ofNat,infinityA,infinityB,infinityH,infinityL] using
    congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) (twice_b_squared_mul_root R)

def infinityRecoveredZ : infinityLocalization R := 2 * infinityB R * infinityLInverse R
def infinityRecoveredF : infinityLocalization R := 2 * infinityHInverse R
def infinityRecoveredW : infinityLocalization R := infinityRecoveredF R -
  (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3)

theorem recoveredZ_mul_L : infinityRecoveredZ R * infinityL R = 2 * infinityB R := by
  have h := infinityL_mul_inverse R
  dsimp [infinityRecoveredZ]
  linear_combination (2 * infinityB R) * h

theorem H_mul_recoveredF : infinityH R * infinityRecoveredF R = 2 := by
  rw [infinityRecoveredF]
  linear_combination 2 * infinityH_mul_inverse R

theorem recoveredZ_mul_A : infinityRecoveredZ R * infinityA R = infinityS R := by
  apply (infinityL_isUnit R).mul_right_inj.mp
  have hz := recoveredZ_mul_L R
  have hab := infinity_twice_A_B R
  linear_combination infinityA R * hz + hab

theorem recoveredZ_squared_H : infinityRecoveredZ R ^ 2 * infinityH R = 2 * infinityA R := by
  apply ((infinityL_isUnit R).pow 2).mul_right_inj.mp
  have hz := recoveredZ_mul_L R
  have h := infinity_twice_B_squared_H R
  linear_combination 2 * h +
    infinityH R * (infinityRecoveredZ R * infinityL R + 2 * infinityB R) * hz

theorem recoveredZ_cubed_H : infinityRecoveredZ R ^ 3 * infinityH R = 2 * infinityS R := by
  have h2 := recoveredZ_squared_H R
  have ha := recoveredZ_mul_A R
  linear_combination infinityRecoveredZ R * h2 + 2 * ha

theorem recoveredZ_fourth_H_squared : infinityRecoveredZ R ^ 4 * infinityH R ^ 2 = 4 * infinityA R ^ 2 := by
  have h := recoveredZ_squared_H R
  linear_combination (infinityRecoveredZ R ^ 2 * infinityH R + 2 * infinityA R) * h

theorem recovered_inverse_profile :
    (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityH R +
      infinityRecoveredZ R ^ 4 * (1 + infinityRecoveredZ R) * infinityH R ^ 2 = 1 := by
  have hz := recoveredZ_mul_L R
  have h3 := recoveredZ_cubed_H R
  have h4 := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  have hl := infinity_L_profile R
  linear_combination hz + h3 + (1 + infinityRecoveredZ R) * h4 +
    (1 + infinityRecoveredZ R) * hh + hl

theorem recoveredF_equation : infinityRecoveredF R ^ 2 -
    2 * (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityRecoveredF R -
      4 * infinityRecoveredZ R ^ 4 * (1 + infinityRecoveredZ R) = 0 := by
  apply ((infinityH_isUnit R).pow 2).mul_right_inj.mp
  have hf := H_mul_recoveredF R
  have hp := recovered_inverse_profile R
  linear_combination (infinityH R * infinityRecoveredF R + 2 -
    2 * (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityH R) * hf - 4 * hp

theorem recovered_reciprocal_equation : infinityRecoveredW R ^ 2 =
    aeval (infinityRecoveredZ R) (reciprocalPolynomial R) := by
  have h := recoveredF_equation R
  dsimp [infinityRecoveredW]
  simp only [reciprocalPolynomial,map_add,map_mul,map_pow,_root_.map_ofNat,map_one,aeval_X]
  linear_combination h

def recoveredReciprocalBase : ReciprocalRing R →ₐ[R] infinityLocalization R :=
  AdjoinRoot.liftAlgHom (reciprocalEquation R) (aeval (infinityRecoveredZ R))
    (infinityRecoveredW R) (by
      simpa [reciprocalEquation,aeval_def] using sub_eq_zero.mpr (recovered_reciprocal_equation R))

theorem recoveredReciprocalBase_z : recoveredReciprocalBase R (zCoordinate R) = infinityRecoveredZ R := by
  simp [recoveredReciprocalBase,zCoordinate]
theorem recoveredReciprocalBase_w : recoveredReciprocalBase R (wCoordinate R) = infinityRecoveredW R := by
  simp [recoveredReciprocalBase,wCoordinate]

theorem recoveredReciprocalBase_f :
    recoveredReciprocalBase R (Order13InverseParameterPositiveReciprocalPatch.f R) = infinityRecoveredF R := by
  simp only [Order13InverseParameterPositiveReciprocalPatch.f,map_add,map_pow,map_one,
    recoveredReciprocalBase_w,recoveredReciprocalBase_z,infinityRecoveredW]
  ring

theorem recoveredReciprocalBase_g_H_squared :
    recoveredReciprocalBase R (Order13InverseParameterPositiveReciprocalPatch.g R) * infinityH R ^ 2 =
      2 * infinityL R := by
  rw [Order13InverseParameterPositiveReciprocalPatch.g,map_add,map_mul,_root_.map_ofNat,
    map_pow,recoveredReciprocalBase_f,recoveredReciprocalBase_z]
  have hf := H_mul_recoveredF R
  have hz := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  linear_combination infinityH R * hf + 2 * hz + 2 * hh

theorem recoveredReciprocalBase_denominator_isUnit (h2 : IsUnit (2 : R)) :
    IsUnit (recoveredReciprocalBase R
      (Order13InverseParameterPositiveReciprocalPatch.f R * Order13InverseParameterPositiveReciprocalPatch.g R)) := by
  have hu : IsUnit (2 : infinityLocalization R) := by
    simpa only [_root_.map_ofNat] using h2.map (algebraMap R (infinityLocalization R))
  have hf : IsUnit (infinityRecoveredF R) := by
    have hh : IsUnit (infinityH R * infinityRecoveredF R) := by rw [H_mul_recoveredF];exact hu
    exact isUnit_of_mul_isUnit_right hh
  have hg : IsUnit (recoveredReciprocalBase R (Order13InverseParameterPositiveReciprocalPatch.g R)) := by
    have hh : IsUnit (recoveredReciprocalBase R (Order13InverseParameterPositiveReciprocalPatch.g R) * infinityH R ^ 2) := by
      rw [recoveredReciprocalBase_g_H_squared]
      exact hu.mul (infinityL_isUnit R)
    exact isUnit_of_mul_isUnit_left hh
  rw [map_mul,recoveredReciprocalBase_f]
  exact hf.mul hg

def recoveredReciprocalPatch (h2 : IsUnit (2 : R)) :
    Order13InverseParameterPositiveReciprocalPatch.PatchRing R →ₐ[R] infinityLocalization R :=
  IsLocalization.Away.liftAlgHom
    (Order13InverseParameterPositiveReciprocalPatch.f R * Order13InverseParameterPositiveReciprocalPatch.g R)
    (f := recoveredReciprocalBase R) (recoveredReciprocalBase_denominator_isUnit R h2)

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact regular inverse-parameter images under the actual
positive reciprocal-patch map into the inverse finite coordinate algebra.
Named downstream consumer: surjectivity and the second-chart isomorphism
for single-section FiniteMapData. Injectivity remains separate.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InverseParameterPositiveReciprocalPatch
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_algebraMap (h2 : IsUnit (2 : R)) (q : ReciprocalRing R) :
    recoveredReciprocalPatch R h2 (algebraMap (ReciprocalRing R) (PatchRing R) q) =
      recoveredReciprocalBase R q := by
  simp [recoveredReciprocalPatch,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem recoveredReciprocalPatch_z (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2 (z R) = infinityRecoveredZ R :=
  (recoveredReciprocalPatch_algebraMap R h2 _).trans (recoveredReciprocalBase_z R)
theorem recoveredReciprocalPatch_F (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2 (F R) = infinityRecoveredF R :=
  (recoveredReciprocalPatch_algebraMap R h2 _).trans (recoveredReciprocalBase_f R)

theorem twice_recoveredReciprocalPatch_r (h2 : IsUnit (2 : R)) :
    2 * recoveredReciprocalPatch R h2 (r R) = infinityH R := by
  have hu : IsUnit (infinityRecoveredF R) := by
    have h := (isUnit_of_mul_isUnit_left (F_mul_G_isUnit R)).map (recoveredReciprocalPatch R h2)
    rwa [recoveredReciprocalPatch_F] at h
  apply hu.mul_right_inj.mp
  have h := congrArg (recoveredReciprocalPatch R h2) (F_mul_r R)
  rw [map_mul,map_one,recoveredReciprocalPatch_F] at h
  linear_combination 2 * h - H_mul_recoveredF R

theorem recoveredReciprocalPatch_s (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2 (s R) = infinityS R := by
  have hu : IsUnit (2 : infinityLocalization R) := by
    simpa only [_root_.map_ofNat] using h2.map (algebraMap R (infinityLocalization R))
  apply hu.mul_right_inj.mp
  rw [s,map_mul,map_pow,recoveredReciprocalPatch_z]
  have hr := twice_recoveredReciprocalPatch_r R h2
  have hz := recoveredZ_cubed_H R
  linear_combination infinityRecoveredZ R ^ 3 * hr + hz

theorem recoveredReciprocalPatch_a (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2 (a R) = infinityA R := by
  have hu : IsUnit (2 : infinityLocalization R) := by
    simpa only [_root_.map_ofNat] using h2.map (algebraMap R (infinityLocalization R))
  apply hu.mul_right_inj.mp
  rw [a,map_mul,map_pow,recoveredReciprocalPatch_z]
  have hr := twice_recoveredReciprocalPatch_r R h2
  have hz := recoveredZ_squared_H R
  linear_combination infinityRecoveredZ R ^ 2 * hr + hz

theorem recoveredReciprocalPatch_b (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2 (b R) = infinityB R := by
  have hu : IsUnit (2 : infinityLocalization R) := by
    simpa only [_root_.map_ofNat] using h2.map (algebraMap R (infinityLocalization R))
  apply hu.mul_right_inj.mp
  rw [b,map_add,map_mul,map_mul,map_mul,_root_.map_ofNat,map_pow,map_pow,recoveredReciprocalPatch_z]
  have hr := twice_recoveredReciprocalPatch_r R h2
  have hz := recoveredZ_mul_L R
  have h4 := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  linear_combination infinityRecoveredZ R * hr +
    infinityRecoveredZ R ^ 5 * (2 * recoveredReciprocalPatch R h2 (r R) + infinityH R) * hr +
      hz + infinityRecoveredZ R * hh + infinityRecoveredZ R * h4

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjectivity of the actual recovered reciprocal-patch map.
Named downstream consumer: the inverse-parameter positive-infinity chart isomorphism.
No injectivity or curve-complement identification is assumed or asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_polynomial_scalars (h2 : IsUnit (2 : R)) (F : Polynomial R) :
    recoveredReciprocalPatch R h2 (aeval (Order13InverseParameterPositiveReciprocalPatch.s R) F) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (algebraMap (Polynomial R) (candidateAlgebra R) F) := by
  have h : (recoveredReciprocalPatch R h2).comp (aeval (Order13InverseParameterPositiveReciprocalPatch.s R)) =
      (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R)).comp
        (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) := by
    apply Polynomial.algHom_ext
    change recoveredReciprocalPatch R h2 (aeval (Order13InverseParameterPositiveReciprocalPatch.s R) X) =
      infinityS R
    rw [aeval_X,recoveredReciprocalPatch_s]
  exact DFunLike.congr_fun h F

theorem recoveredReciprocalPatch_contains_candidate (h2 : IsUnit (2 : R)) (b : candidateAlgebra R) :
    ∃ c : Order13InverseParameterPositiveReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R h2 c = algebraMap (candidateAlgebra R) (infinityLocalization R) b := by
  rcases b with ⟨b,hb⟩
  refine Algebra.adjoin_induction (R := Polynomial R)
    (p := fun x hx => ∃ c : Order13InverseParameterPositiveReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R h2 c =
        algebraMap (candidateAlgebra R) (infinityLocalization R) ⟨x,hx⟩) ?_ ?_ ?_ ?_ hb
  · intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Order13InverseParameterPositiveReciprocalPatch.a R,recoveredReciprocalPatch_a R h2⟩
    · exact ⟨Order13InverseParameterPositiveReciprocalPatch.b R,recoveredReciprocalPatch_b R h2⟩
  · intro F
    exact ⟨aeval (Order13InverseParameterPositiveReciprocalPatch.s R) F,
      recoveredReciprocalPatch_polynomial_scalars R h2 F⟩
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

theorem recoveredReciprocalPatch_infinityPatchElement (h2 : IsUnit (2 : R)) :
    recoveredReciprocalPatch R h2
      ((1 - 2 * Order13InverseParameterPositiveReciprocalPatch.s R -
        2 * Order13InverseParameterPositiveReciprocalPatch.b R -
        4 * Order13InverseParameterPositiveReciprocalPatch.a R ^ 2) *
        (1 - 2 * Order13InverseParameterPositiveReciprocalPatch.s R -
          2 * Order13InverseParameterPositiveReciprocalPatch.b R)) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) := by
  simp only [map_mul,map_sub,map_one,_root_.map_ofNat,map_pow,
    recoveredReciprocalPatch_s,recoveredReciprocalPatch_a,recoveredReciprocalPatch_b]
  change (1 - 2 * infinityS R - 2 * infinityB R - 4 * infinityA R ^ 2) *
    (1 - 2 * infinityS R - 2 * infinityB R) = _
  rw [← infinity_L_profile,← infinity_H_eq_L_sub]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) = _
  rw [← map_mul]
  rfl

theorem recoveredReciprocalPatch_surjective (h2 : IsUnit (2 : R)) :
    Function.Surjective (recoveredReciprocalPatch R h2) := by
  let v : Order13InverseParameterPositiveReciprocalPatch.PatchRing R :=
    ((1 - 2 * Order13InverseParameterPositiveReciprocalPatch.s R -
        2 * Order13InverseParameterPositiveReciprocalPatch.b R -
        4 * Order13InverseParameterPositiveReciprocalPatch.a R ^ 2) *
        (1 - 2 * Order13InverseParameterPositiveReciprocalPatch.s R -
          2 * Order13InverseParameterPositiveReciprocalPatch.b R))
  have hv : IsUnit v := Order13InverseParameterPositiveReciprocalPatch.root_times_linear_isUnit R h2
  let vi : Order13InverseParameterPositiveReciprocalPatch.PatchRing R := ↑(hv.unit⁻¹)
  have hiv : recoveredReciprocalPatch R h2 vi *
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) = 1 := by
    calc
      _ = recoveredReciprocalPatch R h2 (vi * v) := by
        rw [map_mul,recoveredReciprocalPatch_infinityPatchElement]
      _ = 1 := by
        have h : vi * v = 1 := by rw [← hv.unit_spec];exact Units.inv_mul hv.unit
        rw [h,map_one]
  intro a
  obtain ⟨b,s,hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (infinityPatchElement R)) a
  obtain ⟨n,hn⟩ := (Submonoid.mem_powers_iff (s : candidateAlgebra R) (infinityPatchElement R)).mp s.property
  obtain ⟨c,hc⟩ := recoveredReciprocalPatch_contains_candidate R h2 b
  refine ⟨c * vi ^ n,?_⟩
  rw [← hs]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [map_mul,map_pow,hc,← hn,map_pow]
  calc
    _ = algebraMap (candidateAlgebra R) (infinityLocalization R) b *
      (recoveredReciprocalPatch R h2 vi *
        algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R)) ^ n := by ring
    _ = _ := by rw [hiv,one_pow,mul_one]

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the inverse positive-infinity chart maps into the literal
ordinary t-localization further localized at its actual H*L denominator;
its recovered coordinates agree with z=1/x and w=y/x³.
Named downstream consumer: faithful reciprocal-chart comparison and gluing.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InverseParameterPolynomialIdentities
open Order13SingleSectionFiniteMapIdentities (t p q)
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

abbrev ordinaryInfinityLocalization := Localization.Away (inclusion R (infinityPatchElement R))
def ordinaryInfinityMap : ordinaryParameterLocalization R →ₐ[R] ordinaryInfinityLocalization R :=
  IsScalarTower.toAlgHom R (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)
def ordinaryCoordinateMap : CoordinateRing R →ₐ[R] ordinaryInfinityLocalization R :=
  (ordinaryInfinityMap R).comp (IsScalarTower.toAlgHom R (CoordinateRing R) (ordinaryParameterLocalization R))
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
  change ordinaryInfinityMap R (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R)) *
    ordinaryInfinityMap R (s R) = 1
  rw [← map_mul]
  change ordinaryInfinityMap R (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R) *
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
    2 * ordinaryX R * infinityLocalizedInclusion R (infinityB R) := by
  apply (ordinaryS_isUnit R).mul_right_inj.mp
  have h := congrArg (infinityLocalizedInclusion R) (infinity_twice_A_B R)
  rw [map_mul,map_mul,map_mul,_root_.map_ofNat,infinityLocalizedInclusion_A,
    infinityLocalizedInclusion_S] at h
  linear_combination -h

theorem infinityLocalizedInclusion_H : infinityLocalizedInclusion R (infinityH R) =
    2 * ordinaryX R ^ 3 * ordinaryS R := by
  apply ((ordinaryS_isUnit R).pow 2).mul_right_inj.mp
  have h := congrArg ((infinityLocalizedInclusion R).comp
    (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R))) (s_squared_mul_root R)
  simp only [AlgHom.comp_apply,map_mul,map_pow,_root_.map_ofNat] at h
  change infinityLocalizedInclusion R (infinityS R) ^ 2 * infinityLocalizedInclusion R (infinityH R) =
    2 * infinityLocalizedInclusion R (infinityA R) ^ 3 at h
  rw [infinityLocalizedInclusion_S,infinityLocalizedInclusion_A] at h
  linear_combination h

theorem ordinaryX_isUnit : IsUnit (ordinaryX R) := by
  have h := (infinityL_isUnit R).map (infinityLocalizedInclusion R)
  rw [infinityLocalizedInclusion_L] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)

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
  rw [map_mul,_root_.map_ofNat] at hf
  rw [infinityLocalizedInclusion_H] at hf ⊢
  have hx := ordinaryX_mul_recoveredZ R
  have ht := ordinaryT_mul_S R
  linear_combination hf - 2 * ht -
    2 * ordinaryT R * ordinaryS R *
      ((ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R)) ^ 2 +
        ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1) * hx

theorem infinityLocalizedInclusion_recoveredW :
    infinityLocalizedInclusion R (infinityRecoveredW R) = ordinaryY R *
      infinityLocalizedInclusion R (infinityRecoveredZ R) ^ 3 := by
  rw [infinityRecoveredW,map_sub,map_add,map_add,map_one,map_pow,
    infinityLocalizedInclusion_recoveredF]
  have ht : ordinaryT R = ordinaryY R + ordinaryX R ^ 3 + ordinaryX R ^ 2 + 1 := by
    simp only [ordinaryT,t,Order13SingleSectionFiniteMapIdentities.a,map_add,map_pow,map_one,
      ordinaryX,ordinaryY]
    ring
  have hx := ordinaryX_mul_recoveredZ R
  rw [ht]
  linear_combination
    ((ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R)) ^ 2 +
      ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1 +
      infinityLocalizedInclusion R (infinityRecoveredZ R) *
        (ordinaryX R * infinityLocalizedInclusion R (infinityRecoveredZ R) + 1)) * hx

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: nonzero inverse-chart denominators and faithful maps from
the actual ordinary and reciprocal coordinate rings over integral bases.
Named downstream consumer: the inverse-parameter reciprocal chart isomorphism.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InverseParameterPolynomialIdentities
open Order13SingleSectionFiniteMapIdentities (t p q)
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem actual_ordinary_q_ne_zero : q R ≠ 0 := by
  have he : q R = AdjoinRoot.of (affineEquation R) (X ^ 5 + X ^ 4 + X ^ 2 + 2 * X) +
      AdjoinRoot.of (affineEquation R) (X ^ 2) * AdjoinRoot.root (affineEquation R) := by
    simp only [q,p,t,Order13SingleSectionFiniteMapIdentities.a,xCoordinate,yCoordinate,
      map_add,map_mul,map_pow,map_one,_root_.map_ofNat]
    ring
  have hc := QuadraticCoordinates.coordinates_of_add_of_mul_root (Polynomial R)
    (sexticPolynomial R) (X ^ 5 + X ^ 4 + X ^ 2 + 2 * X) (X ^ 2)
  change q R = AdjoinRoot.of (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R))
    (X ^ 5 + X ^ 4 + X ^ 2 + 2 * X) +
      AdjoinRoot.of (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R)) (X ^ 2) *
        AdjoinRoot.root (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R)) at he
  rw [← he] at hc
  intro hq
  rw [hq] at hc
  change (QuadraticCoordinates.coordinates (Polynomial R) (sexticPolynomial R))
    (0 : AdjoinRoot (QuadraticCoordinates.equation (Polynomial R) (sexticPolynomial R))) =
      (X ^ 5 + X ^ 4 + X ^ 2 + 2 * X,X ^ 2) at hc
  rw [map_zero] at hc
  exact (pow_ne_zero 2 (Polynomial.X_ne_zero (R := R))) (congrArg Prod.snd hc).symm

def ordinaryParameterDomain (h104 : IsUnit (104 : R)) : IsDomain (ordinaryParameterLocalization R) := by
  letI : IsDomain (CoordinateRing R) := Order13ReciprocalInjectionCurveDomains.coordinateRing_isDomain R h104
  exact Localization.Away.isDomain (Order13SingleSectionFiniteAlgebra.actual_ordinary_parameter_ne_zero R)

theorem ordinaryParameter_algebraMap_injective (h104 : IsUnit (104 : R)) :
    Function.Injective (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R)) := by
  letI : IsDomain (CoordinateRing R) := Order13ReciprocalInjectionCurveDomains.coordinateRing_isDomain R h104
  exact IsLocalization.injective (ordinaryParameterLocalization R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Order13SingleSectionFiniteAlgebra.actual_ordinary_parameter_ne_zero R))

theorem actual_inverse_a_ne_zero (h104 : IsUnit (104 : R)) : a R ≠ 0 := by
  letI := ordinaryParameterDomain R h104
  have hx : algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) ≠ 0 := by
    exact fun h => Order13SingleSectionFiniteAlgebra.actual_ordinary_x_ne_zero R
      (ordinaryParameter_algebraMap_injective R h104 (by simpa only [map_zero] using h))
  have ht := IsLocalization.Away.mul_invSelf (t R) (S := ordinaryParameterLocalization R)
  have ha : a R = algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) * s R := by
    dsimp [a,p,s]
    rw [map_mul]
    linear_combination algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) *
      IsLocalization.Away.invSelf (t R) * ht
  rw [ha]
  exact mul_ne_zero hx (s_isUnit R).ne_zero

theorem actual_inverse_b_ne_zero (h104 : IsUnit (104 : R)) : b R ≠ 0 := by
  letI := ordinaryParameterDomain R h104
  have hq : algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (q R) ≠ 0 := by
    exact fun h => actual_ordinary_q_ne_zero R
      (ordinaryParameter_algebraMap_injective R h104 (by simpa only [map_zero] using h))
  exact mul_ne_zero hq (pow_ne_zero 2 (s_isUnit R).ne_zero)

theorem actual_inverse_infinity_denominator_ne_zero (h104 : IsUnit (104 : R)) :
    inclusion R (infinityPatchElement R) ≠ 0 := by
  letI := ordinaryParameterDomain R h104
  have h2 : IsUnit (2 : ordinaryParameterLocalization R) := by
    simpa only [_root_.map_ofNat] using
      (Order13SingleSectionFiniteAlgebra.two_isUnit_of_104 R h104).map
        (algebraMap R (ordinaryParameterLocalization R))
  have hH : inclusion R (infinityRootElement R) ≠ 0 := by
    have h := congrArg (inclusion R) (s_squared_mul_root R)
    simp only [map_mul,map_pow,_root_.map_ofNat,inclusion_sElement] at h
    change s R ^ 2 * inclusion R (infinityRootElement R) = 2 * a R ^ 3 at h
    intro hh
    rw [hh,mul_zero] at h
    exact (mul_ne_zero h2.ne_zero (pow_ne_zero 3 (actual_inverse_a_ne_zero R h104))) h.symm
  have hL : inclusion R (infinityLinearElement R) ≠ 0 := by
    have h := congrArg (inclusion R) (twice_a_mul_b R)
    simp only [map_mul,_root_.map_ofNat,inclusion_sElement] at h
    change 2 * a R * b R = s R * inclusion R (infinityLinearElement R) at h
    intro hh
    rw [hh,mul_zero] at h
    exact (mul_ne_zero (mul_ne_zero h2.ne_zero (actual_inverse_a_ne_zero R h104))
      (actual_inverse_b_ne_zero R h104)) h
  change inclusion R (infinityRootElement R * infinityLinearElement R) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hH hL

theorem ordinaryInfinityMap_injective (h104 : IsUnit (104 : R)) :
    Function.Injective (ordinaryInfinityMap R) := by
  letI := ordinaryParameterDomain R h104
  exact IsLocalization.injective (ordinaryInfinityLocalization R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (actual_inverse_infinity_denominator_ne_zero R h104))

theorem ordinaryCoordinateMap_injective (h104 : IsUnit (104 : R)) :
    Function.Injective (ordinaryCoordinateMap R) :=
  (ordinaryInfinityMap_injective R h104).comp (ordinaryParameter_algebraMap_injective R h104)

def ordinaryOverlapToInfinity : OrdinaryOverlapRing R →ₐ[R] ordinaryInfinityLocalization R :=
  IsLocalization.Away.liftAlgHom (xCoordinate R) (f := ordinaryCoordinateMap R) (ordinaryX_isUnit R)

theorem ordinaryOverlapToInfinity_algebraMap (c : CoordinateRing R) :
    ordinaryOverlapToInfinity R (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) c) =
      ordinaryCoordinateMap R c := by
  simp [ordinaryOverlapToInfinity,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem ordinaryOverlapToInfinity_injective (h104 : IsUnit (104 : R)) :
    Function.Injective (ordinaryOverlapToInfinity R) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (OrdinaryOverlapRing R)
    (M := Submonoid.powers (xCoordinate R)) (ordinaryOverlapToInfinity R).toRingHom
  intro a ha
  change ordinaryOverlapToInfinity R (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) a) = 0 at ha
  rw [ordinaryOverlapToInfinity_algebraMap] at ha
  have hh : a = 0 := ordinaryCoordinateMap_injective R h104 (by simpa only [map_zero] using ha)
  rw [hh,map_zero]

end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse-parameter positive reciprocal chart equivalence over noetherian integral
bases with 104 invertible, retaining the recovered reciprocal parameter map.
Named downstream consumer: gluing the second finite chart for single-section FiniteMapData.
No whole-curve complement or full FiniteMapData is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem ordinaryOverlapToInfinity_inverse_x :
    ordinaryOverlapToInfinity R (IsLocalization.Away.invSelf (xCoordinate R)) =
      infinityLocalizedInclusion R (infinityRecoveredZ R) := by
  apply (ordinaryX_isUnit R).mul_right_inj.mp
  calc
    _ = ordinaryOverlapToInfinity R
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R) *
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
    (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R) *
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

omit [IsDomain R] [IsNoetherianRing R] in
theorem two_isUnit_of_104 (h104 : IsUnit (104 : R)) : IsUnit (2 : R) := by
  have he : (104 : R) = 2 * 52 := by norm_num
  rw [he] at h104
  exact isUnit_of_mul_isUnit_left h104

section IntegralGeometry
variable (h104 : IsUnit (104 : R))
include h104

theorem actual_reciprocalToOrdinaryBase_injective : Function.Injective (reciprocalToOrdinaryBase R) := by
  have he (a : ReciprocalRing R) :
      (overlapAlgEquiv R).symm
        (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) a) =
      reciprocalToOrdinaryBase R a := by
    change reciprocalToOrdinary R
      (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) a) = _
    exact reciprocalToOrdinary_algebraMap R a
  intro a b hab
  apply Order13SingleSectionFiniteAlgebra.reciprocalOverlap_algebraMap_injective R h104
  apply (overlapAlgEquiv R).symm.injective
  simpa only [he] using hab

theorem actual_recoveredReciprocalBase_ordinary_composite_injective :
    Function.Injective ((infinityLocalizedInclusion R).comp (recoveredReciprocalBase R)) := by
  rw [recovered_reciprocal_ordinary_comparison_square]
  exact (ordinaryOverlapToInfinity_injective R h104).comp
    (actual_reciprocalToOrdinaryBase_injective R h104)

theorem recoveredReciprocalPatch_injective (h2 : IsUnit (2 : R)) :
    Function.Injective (recoveredReciprocalPatch R h2) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)
    (M := Submonoid.powers (Order13InverseParameterPositiveReciprocalPatch.f R *
      Order13InverseParameterPositiveReciprocalPatch.g R))
    (recoveredReciprocalPatch R h2).toRingHom
  intro a ha
  change recoveredReciprocalPatch R h2
    (algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R) a) = 0 at ha
  rw [recoveredReciprocalPatch_algebraMap] at ha
  have h := congrArg (infinityLocalizedInclusion R) ha
  have hz : a = 0 := actual_recoveredReciprocalBase_ordinary_composite_injective R h104
    (by simpa only [AlgHom.comp_apply,map_zero] using h)
  rw [hz,map_zero]

def recoveredReciprocalPatchEquiv : Order13InverseParameterPositiveReciprocalPatch.PatchRing R ≃ₐ[R]
    infinityLocalization R :=
  AlgEquiv.ofBijective (recoveredReciprocalPatch R (two_isUnit_of_104 R h104))
    ⟨recoveredReciprocalPatch_injective R h104 (two_isUnit_of_104 R h104),
      recoveredReciprocalPatch_surjective R (two_isUnit_of_104 R h104)⟩

theorem recoveredReciprocalPatchEquiv_s :
    recoveredReciprocalPatchEquiv R h104 (Order13InverseParameterPositiveReciprocalPatch.s R) = infinityS R :=
  recoveredReciprocalPatch_s R (two_isUnit_of_104 R h104)
theorem recoveredReciprocalPatchEquiv_a :
    recoveredReciprocalPatchEquiv R h104 (Order13InverseParameterPositiveReciprocalPatch.a R) = infinityA R :=
  recoveredReciprocalPatch_a R (two_isUnit_of_104 R h104)
theorem recoveredReciprocalPatchEquiv_b :
    recoveredReciprocalPatchEquiv R h104 (Order13InverseParameterPositiveReciprocalPatch.b R) = infinityB R :=
  recoveredReciprocalPatch_b R (two_isUnit_of_104 R h104)

end IntegralGeometry
end MazurTransfer.Order13InverseParameterFiniteAlgebra

end
end

section
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13InverseParameterFiniteAlgebra
theorem inverseChartWitnesses.{u} (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    ∃ sB aB bB : MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R,
    (sB : MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R) =
      MazurTransfer.Order13InverseParameterPolynomialIdentities.s R ∧
    (aB : MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R) =
      MazurTransfer.Order13InverseParameterPolynomialIdentities.a R ∧
    (bB : MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R) =
      MazurTransfer.Order13InverseParameterPolynomialIdentities.b R ∧
    Module.Finite (Polynomial R) (MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R) ∧
    (PrimeSpectrum.basicOpen sB ⊔ PrimeSpectrum.basicOpen
      ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)) = ⊤) ∧
    ∃ κ : Localization.Away sB ≃ₐ[R]
        MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R,
      (∀ v : MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R,
        κ (algebraMap (MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R)
          (Localization.Away sB) v) = (v : MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R)) ∧
      ∃ χ : MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.PatchRing R ≃ₐ[R]
          Localization.Away ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)),
        χ (MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.s R) =
          algebraMap (MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R) _ sB ∧
        χ (MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.a R) =
          algebraMap (MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R) _ aB ∧
        χ (MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.b R) =
          algebraMap (MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra R) _ bB
 := by
  let h2 := MazurTransfer.Order13InverseParameterFiniteAlgebra.two_isUnit_of_104 R h104
  refine ⟨MazurTransfer.Order13InverseParameterFiniteAlgebra.sElement R, MazurTransfer.Order13InverseParameterFiniteAlgebra.aElement R,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.bElement R, ?_, rfl, rfl,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra_finite R h2,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.inverse_candidate_two_principal_open_cover R h2,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.parameterLocalizationEquiv R, ?_,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv R h104,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_s R h104,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_a R h104,
    MazurTransfer.Order13InverseParameterFiniteAlgebra.recoveredReciprocalPatchEquiv_b R h104⟩
  · change aeval (MazurTransfer.Order13InverseParameterPolynomialIdentities.s R) X = _
    exact aeval_X _
  · intro v
    exact MazurTransfer.Order13InverseParameterFiniteAlgebra.localizedInclusion_algebraMap R v


end

end InverseParameterChartComparisonLibrary

#print axioms InverseParameterChartComparisonLibrary.inverseChartWitnesses


