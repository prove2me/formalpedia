-- Prove2me | Definitions.Def_MazurN13_L2
-- name    : MazurN13_L2
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-09T04:11:55.338005+00:00
-- url     : https://prove2.me/theorems/6dc494f3-88d1-4d4a-925c-3974dd224f97
-- title:
--   Mazur order 13 (Huang FLT port): definitions, layer 2
-- statement:
--   Layer 2 of 12 of the definitions used by a machine-checked Lean proof of the case $N=13$ of Mazur's torsion theorem (no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$). It collects the definitions, structures, instances and small structural lemmas of Xiang Huang's development whose dependencies are available at this layer; larger lemmas they rely on are separate platform theorems, imported here as already-proved results. Layer $k$ imports layer $k-1$.
--
--   Port notes: only API-drift fixes (transparency options, renamed lemmas); local notations expanded and `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof

import Mathlib
import Definitions.Def_MazurN13_L1
import Theorems.Thm_MazurProof_N13AbelChartBase_specialBaseDivisor_not_canonical
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_hPoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_mumfordIdeal_mul_conj_integral
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13Infinity_coordinateToAlgebraic_injective
import Theorems.Thm_MazurProof_N13Infinity_ratToLaurent_comp_algebraMap
import Theorems.Thm_MazurProof_N13Infinity_ySeries_sq
import Theorems.Thm_MazurProof_N13IntegralGraphJacobian_scaled_jacobian_bezout
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussianIDual_sq
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation
import Theorems.Thm_MazurProof_N13LocalDlogTwo_residueCubic_natDegree
import Theorems.Thm_MazurProof_N13Mumford_f_monic
import Theorems.Thm_MazurProof_N13SpecialGraphDivisor_degreeTwo_splits
import Theorems.Thm_MazurProof_N13SpecialQuotientBasis_specialData_u_natDegree
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_dvd_curveError
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_dvd_derivativeInverse_mul_sub_one
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_derivative_eval_negOne_isUnit
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_u_eval_negOne_mem
import Theorems.Thm_MazurProof_SexticMumford_IntegralOrientedRep_ideal_ne_bot
import Theorems.Thm_MazurProof_SexticMumford_contentGenerator_ne_zero
import Theorems.Thm_MazurProof_SexticMumford_curvePoly_natDegree
import Theorems.Thm_MazurProof_SexticMumford_exists_integralRep_of_raw
import Theorems.Thm_MazurProof_SexticMumford_mumfordIdeal_mul_conj_integral
import Theorems.Thm_MazurProof_SexticMumford_ySubClass_ne_zero
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_goodYInSextic_root
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_sexticYInGood_root
import Theorems.Thm_MazurProof_SexticMumford_neg_y_relation
import Theorems.Thm_MazurProof_SexticMumford_mumford_root_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- Equality in the generalized affine coordinate ring is coefficientwise
with respect to the basis `1, Y` over `R[X]`. -/
theorem eq_iff_coeff [Nontrivial R]
    (z w : CoordinateRing (R := R)) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]
noncomputable def mumfordQuotientEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))
/-- The graph quotient equivalence sends a quotient class to its graph
evaluation. -/
@[simp] theorem mumfordQuotientEquiv_apply_mk
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]
/-- The graph quotient equivalence respects the coefficient algebra. -/
noncomputable def mumfordQuotientAlgEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[R]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set R[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))
@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford) (z : CoordinateRing) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]
/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[K]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
/-- Completion of the square as a ring homomorphism from the good model to
the sextic model. -/
def toSextic :
    GoodRing (K := K) →+* SexticRing (K := K) :=
  AdjoinRoot.lift (sexticXHom (K := K))
    (goodYInSextic (K := K))
    (goodYInSextic_root (K := K))
/-- The inverse change of variables. -/
def toGood :
    SexticRing (K := K) →+* GoodRing (K := K) :=
  AdjoinRoot.lift (goodXHom (K := K))
    (sexticYInGood (K := K))
    (sexticYInGood_root (K := K))
@[simp] theorem toSextic_xClass (p : K[X]) :
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p := by
  change
    toSextic (K := K)
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := K)) p) =
      sexticXHom (K := K) p
  exact AdjoinRoot.lift_of (goodYInSextic_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange =====
section
/-!
# Base change of the N13 integral coordinate ring to `ℚ₂`

Coefficient extension from `ℤ₂` to `ℚ₂` induces a map between the two
generalized-hyperelliptic coordinate rings.  It carries an integral Mumford
graph ideal exactly onto the graph ideal obtained by coefficient extension.
Composing with completion of the square therefore sends the integral graph
directly to the standard sextic Mumford graph over `ℚ₂`.
-/
open Polynomial
namespace MazurProof.N13TwoAdicCoordinateBaseChange
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicCoordinateBaseChange.instFactPrimeOfNatNat_fLT
/-- Coefficient extension preserves the `1`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeff0_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeff0
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeff0 z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp
/-- Coefficient extension preserves the `Y`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeffY_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeffY
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeffY z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp
/-- Base change from the integral good model to its generic fibre loses no
functions.  This is the rank-two basis argument, not a localization
calculation in coordinates. -/
theorem extendCoordinate_injective :
    Function.Injective extendCoordinate := by
  intro z w h
  apply
    (N13GeneralizedMumfordIntegral.eq_iff_coeff z w).2
  constructor
  · apply mapPoly_injective
    simpa only [coeff0_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeff0 h
  · apply mapPoly_injective
    simpa only [coeffY_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeffY h
/-- The full integral-to-sextic coordinate map over `ℚ₂`. -/
def integralToSextic :
    IntegralRing →+*
      N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂) :=
  (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂)).comp
    extendCoordinate
end
end MazurProof.N13TwoAdicCoordinateBaseChange
end

end

-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-! ## The formal positive square root -/
/-! ## An algebraic model of the function field -/
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
theorem curvePolyRat_eval_ySeries :
    (curvePolyRat K).eval₂ (ratToLaurent K) (ySeries K) = 0 := by
  rw [curvePolyRat, Polynomial.eval₂_map,
    ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹)) (ySeries K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeries_sq]
  exact sub_self _
def algebraicToLaurent :
    AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (ratToLaurent K) (ySeries K)
    (curvePolyRat_eval_ySeries K)
theorem algebraicToLaurent_injective :
    Function.Injective (algebraicToLaurent K) :=
  (algebraicToLaurent K).injective
def coordinateToLaurent :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurent K).comp (coordinateToAlgebraic K)
theorem coordinateToLaurent_injective :
    Function.Injective (coordinateToLaurent K) :=
  (algebraicToLaurent_injective K).comp
    (coordinateToAlgebraic_injective K)
def functionFieldToLaurent :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurent_injective K)
def infinityOrderHom :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (laurentOrder K).comp (Units.map (functionFieldToLaurent K))
def positiveInfinityOrder : SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHom K
end
end MazurProof.N13Infinity
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-! ## Hyperelliptic conjugation and the quadratic norm -/
def conjugate : CoordinateRing M →+* CoordinateRing M :=
  AdjoinRoot.lift (AdjoinRoot.of (curvePoly M)) (-(yClass M))
    (neg_y_relation M)
@[simp] theorem conjugate_xClass (p : K[X]) :
    conjugate M (xClass M p) = xClass M p := by
  change conjugate M (AdjoinRoot.of (curvePoly M) p) =
    AdjoinRoot.of (curvePoly M) p
  exact AdjoinRoot.lift_of (neg_y_relation M)
@[simp] theorem conjugate_yClass :
    conjugate M (yClass M) = -(yClass M) := by
  exact AdjoinRoot.lift_root (neg_y_relation M)
theorem conjugate_involutive : Function.Involutive (conjugate M) := by
  have hcomp : (conjugate M).comp (conjugate M) =
      RingHom.id (CoordinateRing M) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro k
        change conjugate M (conjugate M (xClass M (C k))) = xClass M (C k)
        rw [conjugate_xClass, conjugate_xClass]
      · change conjugate M (conjugate M (xClass M X)) = xClass M X
        rw [conjugate_xClass, conjugate_xClass]
    · change conjugate M (conjugate M (yClass M)) = yClass M
      rw [conjugate_yClass, map_neg, conjugate_yClass, neg_neg]
  intro z
  exact DFunLike.congr_fun hcomp z
def norm (z : CoordinateRing M) : CoordinateRing M :=
  z * conjugate M z
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
def mumfordEval (D : SemiMumford M) :
    CoordinateRing M →+* MumfordResidue M D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation M D)
@[simp] theorem mumfordEval_xClass (D : SemiMumford M) (p : K[X]) :
    mumfordEval M D (xClass M p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval M D (AdjoinRoot.of (curvePoly M) p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation M D)
theorem mumfordEval_surjective (D : SemiMumford M) :
    Function.Surjective (mumfordEval M D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass M p, mumfordEval_xClass M D p⟩
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordUnit =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordUnit =====
section
/-!
# Explicit invertibility of Mumford ideals on a smooth sextic

For a semi-Mumford pair `(u,v)`, squarefreeness of the sextic gives
`(u, 2v, (f-v²)/u) = 1`.  Consequently `(u,Y-v) (u,Y+v) = (u)`,
which packages the Mumford ideal as a unit fractional ideal.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]
def mumfordIdealUnit (D : SemiMumford M) : InvFrac M :=
  Units.mkOfMulEqOne
    (mumfordIdeal M D.u D.v :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
    ((mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        (FunctionField M) (xClass_ne_zero M D.u_monic.ne_zero))
@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford M) :
    (mumfordIdealUnit M D :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      mumfordIdeal M D.u D.v := rfl
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticOrientedPic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticOrientedPic =====
section
/-!
# The concrete oriented Picard group of a smooth sextic

The affine coordinate ring omits the two points at infinity.  An
`InfinityOrder` supplies the order at the chosen point before quotienting by
principal fractional ideals.  This file packages balanced Mumford data into
that oriented quotient for an arbitrary smooth monic sextic model.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
/-- The oriented invertible fractional ideal represented by balanced Mumford
data. -/
def mumfordRaw (D : Mumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D.toSemi,
    Multiplicative.ofAdd ((D.nInf : ℤ) - 1))
/-- The oriented Picard class of a balanced Mumford representative. -/
def classOf (D : Mumford M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      (mumfordRaw M D)
theorem classOf_eq_iff (D₁ D₂ : Mumford M) :
    classOf M O D₁ = classOf M O D₂ ↔
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁.toSemi *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
            mumfordIdealUnit M D₂.toSemi ∧
        Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * O.ordPlus α =
            Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₁) =
      QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    refine ⟨α, ?_, ?_⟩
    · exact congrArg Prod.fst hmul
    · exact congrArg Prod.snd hmul
  · rintro ⟨α, hIdeal, hInf⟩
    refine ⟨principalOriented M O α,
      MonoidHom.mem_range.mpr ⟨α, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf
theorem mumfordIdealUnit_zero :
    mumfordIdealUnit M (zero M).toSemi = 1 := by
  apply Units.ext
  change (mumfordIdeal M 1 0 :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl
@[simp] theorem classOf_zero : classOf M O (zero M) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range
        (mumfordRaw M (zero M))) = 0
  have hraw : mumfordRaw M (zero M) = 1 := by
    apply Prod.ext
    · exact mumfordIdealUnit_zero M
    · simp [mumfordRaw]
  rw [hraw, map_one]
  rfl
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
namespace IntegralOrientedRep
end IntegralOrientedRep
/-- Every oriented Picard class has an integral invertible-ideal
representative.  No Dedekind-domain or class-number hypothesis is used. -/
theorem exists_integralRepresentative (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M, R.picClass M O = c := by
  change
    ∃ R : IntegralOrientedRep M,
      Additive.toMul (R.picClass M O) = Additive.toMul c
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (principalOriented M O).range
      (Additive.toMul c)
  obtain ⟨R, hR⟩ :=
    exists_integralRep_of_raw M O x.1 x.2
  exact ⟨R, hR.symm.trans hx⟩
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralModelContraction.instFactPrimeOfNatNat_fLT
abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
/-- Canonical contraction of a generic-fibre ideal to the integral model. -/
def contractIdeal
    (J : Ideal RationalRing) :
    Ideal IntegralRing :=
  J.under IntegralRing
end
end MazurProof.N13IntegralModelContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/
open Polynomial
namespace MazurProof.N13CanonicalContractionQuotient
noncomputable section
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
end
end MazurProof.N13CanonicalContractionQuotient
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness =====
section
/-!
# Vertical saturation gives flat N13 quotients

The canonical contraction of a generic ideal is saturated with respect to
every nonzero two-adic scalar.  Consequently its affine quotient has no
two-adic torsion.  Since the two-adic integers form a Dedekind domain, the
quotient is flat even before finiteness has been established.

This separates the easy vertical part of the two-fibre argument from the
genuine no-escape/finiteness step.
-/
namespace MazurProof.N13QuotientVerticalFlatness
noncomputable section
universe uR uA
variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]
attribute [local instance] MazurProof.N13QuotientVerticalFlatness.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
end
end MazurProof.N13QuotientVerticalFlatness
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialQuotientBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialQuotientBasis =====
section
/-!
# The literal basis of the fixed N13 special quotient

The selected special divisor has graph ideal `(X²+X,Y)`.  Evaluation on
that graph identifies its affine quotient with
`𝔽₂[X]/(X²+X)`.  The canonical monic power basis on the latter transports
back to the literal quotient basis `{1,x}`.

This file is only the fixed special-fibre endpoint.  It does not assert
that the contraction of an arbitrary generic Picard representative reduces
to this ideal.
-/
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
/-- The monic quotient `k[X]/(u)` has its canonical power basis. -/
def residueBasis :
    Basis (Fin 2) k (AdjoinRoot specialData.u) :=
  (AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
    (finCongr (by
      change specialData.u.natDegree = 2
      exact specialData_u_natDegree))
/-- The graph-quotient equivalence respects the coefficient field. -/
def quotientAlgEquiv :
    (A ⧸ specialIdeal) ≃ₐ[k]
      N13GoodCoordinateRingTwo.MumfordResidue specialData :=
  by
    simpa only [A, k, specialIdeal] using
      N13GoodCoordinateRingTwo.mumfordQuotientAlgEquiv specialData
end
end MazurProof.N13SpecialQuotientBasis
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis =====
section
-- ===== FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis =====
section
/-!
# The concrete two-fibre basis for an N13 contraction

Assume only the remaining representative-level statement that the canonical
contraction reduces to the fixed special graph ideal.  The generic and special
quotient frames are then both literally `{1,x}`.  The two-fibre no-escape
theorem therefore makes the same pair an integral basis, without any prior
finiteness assumption.
-/
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.baseSpecialAlgebra
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.baseSpecialQuotientTower
universe uR uK uB uG uι
end
end MazurProof.N13TwoFiberConcreteBasis
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralFractionalHull =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralFractionalHull =====
section
/-!
# Divisorial hulls on the N13 integral model

The N13 generic affine ring is the vertical localization of its integral
good-model ring.  This file proves that the common function field is also the
fraction field of the integral model and that vertical extension commutes with
inverse fractional ideals.

The reverse inclusion is the substantive point: a fractional ideal over the
Noetherian integral model has finitely many generators, so one vertical scalar
clears all denominators of their products with a generic inverse section.
Consequently the divisorial double inverse of a contracted invertible generic
ideal has exactly the original generic fibre.  No affine generator or
principality assumption is used.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralFractionalHull
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.instFactPrimeOfNatNat_fLT
def integralToRational : IntegralRing →+* RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  integralToRational.toAlgebra
abbrev IntegralFractionalIdeal : Type :=
  FractionalIdeal IntegralRing⁰ FunctionField
end
end MazurProof.N13IntegralFractionalHull
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphContraction =====
section
/-!
# Exact contraction of integral N13 graph ideals

Coefficient extension and contraction already fix a smooth integral
generalized Mumford graph ideal.  Completion of the square is a coordinate
ring equivalence, so it cancels formally from a further extension and
contraction.  Hence the standard sextic graph contracts to the original
integral graph exactly.

This is a representative-level equality.  It does not construct an
integral graph from a generic Picard class.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphContraction
noncomputable section
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
end
end MazurProof.N13IntegralGraphContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisor
noncomputable section
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT
theorem exists_rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    ∃ z : Sym2 K, z.toMultiset = D.u.roots := by
  have hcard : D.u.roots.card = 2 := by
    rw [← (degreeTwo_splits D hdeg).natDegree_eq_card_roots]
    exact hdeg
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨s(a, b), ?_⟩
  change ({a, b} : Multiset K) = D.u.roots
  exact hab.symm
noncomputable def rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    Sym2 K :=
  Classical.choose (exists_rootPair D hdeg)
theorem rootPair_toMultiset
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    (rootPair D hdeg).toMultiset = D.u.roots := by
  exact Classical.choose_spec (exists_rootPair D hdeg)
theorem mem_rootPair_iff_isRoot
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) (a : K) :
    a ∈ rootPair D hdeg ↔ D.u.IsRoot a := by
  rw [← Sym2.mem_toMultiset, rootPair_toMultiset,
    Polynomial.mem_roots D.u_monic.ne_zero]
noncomputable def rootPoint
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (a : K) (ha : a ∈ rootPair D hdeg) :
    N13AbelFiberTwoModel.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      curveEquationAtRoot D ((mem_rootPair_iff_isRoot D hdeg a).mp ha)⟩
noncomputable def graphDivisor
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  Sym2.pmap (rootPoint D hdeg) (rootPair D hdeg)
    (fun _ ha => ha)
/-- Abel equality with the selected nonspecial divisor already forces
literal equality of effective divisors.  The only other degree-two Abel
fibre is the canonical pencil, and the selected base divisor is not in it. -/
theorem graphDivisor_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  rcases
      (G.eq_iff
        (graphDivisor D hdeg)
        N13AbelChartBase.specialBaseDivisor).mp habel with
    h | ⟨_, hbase⟩
  · exact h
  · exact
      (N13AbelChartBase.specialBaseDivisor_not_canonical hbase).elim
/-- The same rigidity statement in the canonical nineteen-element
set-valued Abel quotient. -/
theorem graphDivisor_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor :=
  graphDivisor_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel
end
end MazurProof.N13SpecialGraphDivisor
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
/-!
# Integral Mumford data on the nonspecial N13 two-adic Abel chart

A point in the residue disk of `(0,0)` and a point in the residue disk of
`(-1,0)` have distinct `x`-coordinates by a unit.  Lagrange interpolation
therefore gives an integral graph polynomial through the two points.

The product of the two linear factors divides the curve residual.  The same
interpolation argument, applied to the inverses of the two vertical
derivatives, gives the smoothness Bezout identity.  Thus every such pair
defines smooth generalized Mumford data over `ℤ₂`, without a search through
congruence classes.
-/
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
namespace DiskPair
variable (P : DiskPair)
def w : R₂[X] :=
  Classical.choose P.u_dvd_curveError
theorem curve_eq :
    P.v ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly * P.v -
      N13GeneralizedMumfordIntegral.rhsPoly =
        P.u * P.w :=
  Classical.choose_spec P.u_dvd_curveError
def bezoutQuotient : R₂[X] :=
  Classical.choose P.u_dvd_derivativeInverse_mul_sub_one
theorem bezoutQuotient_spec :
    P.derivativeInverse * P.verticalDerivative - 1 =
      P.u * P.bezoutQuotient :=
  Classical.choose_spec P.u_dvd_derivativeInverse_mul_sub_one
/-- The two-disk divisor supplies smooth integral generalized Mumford data. -/
def smoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := P.u
  v := P.v
  w := P.w
  u_monic := P.u_monic
  curve_eq := P.curve_eq
  bezout := by
    refine
      ⟨-P.bezoutQuotient, P.derivativeInverse, 0, ?_⟩
    rw [show
      2 * P.v +
          N13GeneralizedMumfordIntegral.hPoly =
        P.verticalDerivative by rfl]
    have h := P.bezoutQuotient_spec
    have hb :
        P.derivativeInverse * P.verticalDerivative =
          P.u * P.bezoutQuotient + 1 :=
      sub_eq_iff_eq_add.mp h
    rw [hb]
    ring
@[simp] theorem smoothMumford_u :
    P.smoothMumford.u = P.u := rfl
@[simp] theorem smoothMumford_v :
    P.smoothMumford.v = P.v := rfl
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityAPI =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityAPI =====
section
/-!
# Evaluation API for the positive infinity embedding of the N13 sextic
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem functionFieldToLaurent_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurent K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurent K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurent_injective K) z
@[simp] theorem coordinateToLaurent_xClass (p : K[X]) :
    coordinateToLaurent K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((parameter K)⁻¹) := by
  change algebraicToLaurent K
      (coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [coordinateToAlgebraic_xClass]
  unfold algebraicToLaurent
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeries K)]
  exact DFunLike.congr_fun (ratToLaurent_comp_algebraMap K) p
end
end MazurProof.N13Infinity
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityMinus =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityMinus =====
section
/-!
# The negative infinity of the N13 genus-two curve

The second branch at infinity is obtained by sending `Y` to the negative of
the positive Laurent expansion.  It gives the opposite orientation datum for
the two-infinity sextic model.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem ySeriesMinus_sq :
    ySeriesMinus K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := by
  rw [ySeriesMinus, neg_sq, N13Infinity.ySeries_sq]
theorem curvePolyRat_eval_ySeriesMinus :
    (N13Infinity.curvePolyRat K).eval₂ (N13Infinity.ratToLaurent K)
      (ySeriesMinus K) = 0 := by
  rw [N13Infinity.curvePolyRat, Polynomial.eval₂_map,
    N13Infinity.ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹)) (ySeriesMinus K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeriesMinus_sq]
  exact sub_self _
def algebraicToLaurentMinus :
    N13Infinity.AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (N13Infinity.ratToLaurent K) (ySeriesMinus K)
    (curvePolyRat_eval_ySeriesMinus K)
@[simp] theorem algebraicToLaurentMinus_root :
    algebraicToLaurentMinus K
      (AdjoinRoot.root (N13Infinity.curvePolyRat K)) = ySeriesMinus K := by
  exact AdjoinRoot.lift_root (curvePolyRat_eval_ySeriesMinus K)
theorem algebraicToLaurentMinus_injective :
    Function.Injective (algebraicToLaurentMinus K) :=
  (algebraicToLaurentMinus K).injective
def coordinateToLaurentMinus :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurentMinus K).comp (N13Infinity.coordinateToAlgebraic K)
theorem coordinateToLaurentMinus_injective :
    Function.Injective (coordinateToLaurentMinus K) :=
  (algebraicToLaurentMinus_injective K).comp
    (N13Infinity.coordinateToAlgebraic_injective K)
@[simp] theorem coordinateToLaurentMinus_yClass :
    coordinateToLaurentMinus K
      (SexticMumford.yClass (N13Mumford.model K)) = ySeriesMinus K := by
  change algebraicToLaurentMinus K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact algebraicToLaurentMinus_root K
def functionFieldToLaurentMinus :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurentMinus_injective K)
def infinityOrderHomMinus :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (N13Infinity.laurentOrder K).comp
    (Units.map (functionFieldToLaurentMinus K))
def negativeInfinityOrder :
    SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHomMinus K
end
end MazurProof.N13InfinityMinus
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityMinusAPI =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityMinusAPI =====
section
/-!
# Evaluation API for the negative infinity embedding of the N13 sextic
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurentMinus_xClass (p : K[X]) :
    coordinateToLaurentMinus K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((N13Infinity.parameter K)⁻¹) := by
  change algebraicToLaurentMinus K
      (N13Infinity.coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [N13Infinity.coordinateToAlgebraic_xClass]
  unfold algebraicToLaurentMinus
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeriesMinus K)]
  exact DFunLike.congr_fun (N13Infinity.ratToLaurent_comp_algebraMap K) p
end
end MazurProof.N13InfinityMinus
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
end
end MazurProof.N13Infinity
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
end
end MazurProof.N13InfinityMinus
end

end

-- ===== FLT.Assumptions.MazurProof.SexticFunctionConjugation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticFunctionConjugation =====
section
/-!
# Hyperelliptic conjugation on the sextic function field

The affine involution `Y ↦ -Y` extends functorially from the coordinate ring
to the fraction field.  Packaging it as a ring equivalence makes conjugation
of units and fractional ideals available without choosing numerators and
denominators.
-/
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
def conjugateEquiv (M : Model K) :
    CoordinateRing M ≃+* CoordinateRing M where
  toFun := conjugate M
  invFun := conjugate M
  left_inv := conjugate_involutive M
  right_inv := conjugate_involutive M
  map_mul' := map_mul (conjugate M)
  map_add' := map_add (conjugate M)
@[simp] theorem conjugateEquiv_apply (M : Model K)
    (z : CoordinateRing M) :
    conjugateEquiv M z = conjugate M z := rfl
def functionConjugateEquiv (M : Model K) :
    FunctionField M ≃+* FunctionField M :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField M)
    (L := FunctionField M) (conjugateEquiv M)
def conjugateFunctionUnit (M : Model K) :
    (FunctionField M)ˣ →* (FunctionField M)ˣ :=
  Units.map (functionConjugateEquiv M).toRingHom
@[simp] theorem conjugateFunctionUnit_val (M : Model K)
    (z : (FunctionField M)ˣ) :
    (conjugateFunctionUnit M z : FunctionField M) =
      functionConjugateEquiv M (z : FunctionField M) := rfl
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation =====
section
/-!
# Conjugation of Mumford ideals

Hyperelliptic conjugation sends `(u, Y-v)` to `(u, Y+v)`.  The following lifts
that elementary generator identity to integral and fractional ideals.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
def conjugateFractionalIdealEquiv (M : Model K) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) ≃+*
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) :=
  FractionalIdeal.ringEquivOfRingEquiv
    (FunctionField M) (FunctionField M) (conjugateEquiv M)
def conjugateInvFrac (M : Model K) : InvFrac M →* InvFrac M :=
  Units.map (conjugateFractionalIdealEquiv M).toRingHom
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordGroup =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordGroup =====
section
/-!
# The Mumford group law from oriented Picard normal forms

Given unique balanced Mumford representatives of the oriented Picard classes,
transport the ambient abelian group structure to those representatives.
-/
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
class NormalFormData (O : outParam (InfinityOrder M)) : Prop where
  existsUnique : ∀ c : ConcretePic M O,
    ∃! D : Mumford M, classOf M O D = c
def normalize [NormalFormData M O] (c : ConcretePic M O) : Mumford M :=
  Classical.choose (NormalFormData.existsUnique c)
@[simp]
theorem classOf_normalize [NormalFormData M O] (c : ConcretePic M O) :
    classOf M O (normalize M O c) = c :=
  (Classical.choose_spec (NormalFormData.existsUnique c)).1
theorem normalize_eq_of_class [NormalFormData M O]
    (c : ConcretePic M O) (D : Mumford M) (hD : classOf M O D = c) :
    normalize M O c = D := by
  exact ((Classical.choose_spec (NormalFormData.existsUnique c)).2 D hD).symm
def normalFormEquiv [NormalFormData M O] : Mumford M ≃ ConcretePic M O where
  toFun := classOf M O
  invFun := normalize M O
  left_inv D := by
    exact normalize_eq_of_class M O (classOf M O D) D rfl
  right_inv := classOf_normalize M O
/-- The group law is inherited from the oriented Picard group.  The
orientation in `NormalFormData` is an output parameter, so this instance is
selected only after the oriented normal-form data have been fixed. -/
noncomputable instance instAddCommGroupMumford [NormalFormData M O] :
    AddCommGroup (Mumford M) :=
  Equiv.addCommGroup (normalFormEquiv M O)
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart =====
section
/-!
# Primitive content of an integral sextic ideal

Every integral ideal in the quadratic coordinate ring has a polynomial
content: the common principal ideal generated by all of its `Y`
coefficients.  Dividing by that content is implemented as a colon ideal.
This gives a primitive integral ideal structurally, without enumeration or
Riemann--Roch.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-! ## The coefficient-content ideal -/
/-! ## Division by content as a colon ideal -/
/-- The integral colon ideal `{z | d z ∈ J}`. -/
def primitivePart
    (J : Ideal (CoordinateRing M)) (d : K[X]) :
    Ideal (CoordinateRing M) where
  carrier := {z | xClass M d * z ∈ J}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    simpa [mul_add] using J.add_mem hz hw
  smul_mem' := by
    intro a z hz
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left a hz
/-! ## Fractional invertibility -/
/-! ## Oriented primitive representatives -/
namespace IntegralOrientedRep
variable (O : InfinityOrder M)
def contentUnit (R : IntegralOrientedRep M) :
    (FunctionField M)ˣ :=
  contentFunctionUnit M (contentGenerator M R.ideal)
    (contentGenerator_ne_zero M R.ideal (R.ideal_ne_bot M))
end IntegralOrientedRep
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordCantorReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordCantorReduction =====
section
/-!
# One-step Cantor reduction for a monic sextic

This file isolates the structural algebra used by a well-founded Cantor
reduction.  It contains no enumeration and no Riemann--Roch input.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
/-! ## Changing the graph polynomial modulo `u` -/
/-! ## The Cantor product identity -/
/-! ## Degree descent -/
/-- A factor in `f - V² = u w` cannot vanish. -/
theorem cantorFactor_ne_zero
    (u V w : K[X]) (hcurve : M.f - V ^ 2 = u * w) :
    w ≠ 0 := by
  intro hw
  have hsub : M.f - V ^ 2 = 0 := by
    simpa [hw] using hcurve
  have hsq : V ^ 2 = M.f := (sub_eq_zero.mp hsub).symm
  have hVunit : IsUnit V := by
    apply M.squarefree V
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hVunit.pow 2
  exact M.not_isUnit hfunit
/-- Above genus two, the quotient in a Cantor step has strictly smaller
degree than the old monic denominator. -/
theorem cantorFactor_natDegree_lt
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    w.natDegree < D.u.natDegree := by
  have hw : w ≠ 0 := cantorFactor_ne_zero M D.u D.v w hcurve
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree : D.v.natDegree < D.u.natDegree := by
    by_cases hv : D.v = 0
    · rw [hv]
      simp
      omega
    · exact natDegree_lt_natDegree hv hvDegree
  have hnum :
      (M.f - D.v ^ 2).natDegree ≤
        max 6 (2 * D.v.natDegree) := by
    calc
      (M.f - D.v ^ 2).natDegree ≤
          max M.f.natDegree (D.v ^ 2).natDegree :=
        natDegree_sub_le _ _
      _ = max 6 (2 * D.v.natDegree) := by
        rw [M.natDegree, natDegree_pow]
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - D.v ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  have hbound :
      max 6 (2 * D.v.natDegree) <
        2 * D.u.natDegree := by
    rw [Nat.max_lt]
    omega
  omega
/-- In the cubic boundary case one replaces `v` by `v + u`.  The leading
terms of `f` and `(v+u)²` then cancel, so the quotient has degree at most
two. -/
theorem cubicCantorFactor
    (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve :
      M.f - (D.v + D.u) ^ 2 = D.u * w) :
    w ≠ 0 ∧ w.natDegree ≤ 2 := by
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hVMonic : (D.v + D.u).Monic :=
    D.u_monic.add_of_right hvDegree
  have hVNatDegree : (D.v + D.u).natDegree = 3 := by
    rw [natDegree_add_eq_right_of_degree_lt hvDegree, hdeg]
  have hf : IsMonicOfDegree M.f 6 :=
    ⟨M.natDegree, M.monic⟩
  have hV : IsMonicOfDegree (D.v + D.u) 3 :=
    ⟨hVNatDegree, hVMonic⟩
  have hV2 : IsMonicOfDegree ((D.v + D.u) ^ 2) 6 := by
    simpa using hV.pow 2
  have hnum :
      (M.f - (D.v + D.u) ^ 2).natDegree < 6 :=
    hf.natDegree_sub_lt (by norm_num) hV2
  have hw : w ≠ 0 :=
    cantorFactor_ne_zero M D.u (D.v + D.u) w hcurve
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - (D.v + D.u) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  constructor
  · exact hw
  · omega
/-! ## The normalized next semirepresentative -/
theorem normalize_dvd_sub_mod
    (p q : K[X]) :
    _root_.normalize q ∣ p - p % _root_.normalize q := by
  refine ⟨p / _root_.normalize q, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p (_root_.normalize q)
  calc
    p - p % _root_.normalize q =
        (p % _root_.normalize q + _root_.normalize q * (p / _root_.normalize q)) -
          p % _root_.normalize q := by
      rw [hdiv]
    _ = _root_.normalize q * (p / _root_.normalize q) := by ring
/-- Normalize the quotient and reduce the complementary graph polynomial.
This is the inverse affine class; the actual Cantor successor is its
hyperelliptic conjugate below. -/
def cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w)
    (hw : w ≠ 0) :
    SemiMumford M where
  u := _root_.normalize w
  v := V % _root_.normalize w
  nInf := n
  u_monic := monic_normalize hw
  v_reduced := by
    apply (mod_eq_self_iff (monic_normalize hw).ne_zero).mpr
    exact degree_mod_lt _ (monic_normalize hw).ne_zero
  curve_dvd := by
    have hnW : _root_.normalize w ∣ w :=
      (associated_normalize w).symm.dvd
    have hnBase : _root_.normalize w ∣ M.f - V ^ 2 := by
      obtain ⟨c, hc⟩ := hnW
      refine ⟨D.u * c, ?_⟩
      calc
        M.f - V ^ 2 = D.u * w := hcurve
        _ = D.u * (_root_.normalize w * c) :=
          congrArg (fun z : K[X] ↦ D.u * z) hc
        _ = _root_.normalize w * (D.u * c) := by ring
    have hnGraph :
        _root_.normalize w ∣ V - V % _root_.normalize w :=
      normalize_dvd_sub_mod V w
    obtain ⟨a, ha⟩ := hnBase
    obtain ⟨b, hb⟩ := hnGraph
    refine ⟨a + b * (V + V % _root_.normalize w), ?_⟩
    calc
      M.f - (V % _root_.normalize w) ^ 2 =
          (M.f - V ^ 2) +
            (V - V % _root_.normalize w) *
              (V + V % _root_.normalize w) := by ring
      _ = _root_.normalize w * a +
            (_root_.normalize w * b) *
              (V + V % _root_.normalize w) := by rw [ha, hb]
      _ = _root_.normalize w *
            (a + b * (V + V % _root_.normalize w)) := by ring
@[simp] theorem cantorComplementSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).u = _root_.normalize w := rfl
@[simp] theorem cantorComplementSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).v =
      V % _root_.normalize w := rfl
@[simp] theorem cantorComplementSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).nInf = n := rfl
/-! ## Conjugating the complement -/
/-- The affine Cantor successor is the conjugate of the complement.  Its
graph polynomial is `(-V) mod _root_.normalize w`, up to the definitional
linearity of polynomial remainder. -/
def cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  conjugateSemiMumford M
    (cantorComplementSemi M D V w n hcurve hw)
@[simp] theorem cantorConjugateSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).u =
      _root_.normalize w := rfl
@[simp] theorem cantorConjugateSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      -(V % _root_.normalize w) := rfl
@[simp] theorem cantorConjugateSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).nInf = n := rfl
/-! ## Principal functions in one oriented step -/
def ySubFunctionUnit (V : K[X]) : (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (ySubClass M V))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (ySubClass_ne_zero M V))
@[simp] theorem coe_ySubFunctionUnit (V : K[X]) :
    (ySubFunctionUnit M V : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (ySubClass M V) := rfl
/-- The principal correction taking the conjugate complement back to the
original affine ideal class: `(Y-V) / _root_.normalize(w)`. -/
def cantorCorrectionUnit
    (V w : K[X]) (hw : w ≠ 0) :
    (FunctionField M)ˣ :=
  ySubFunctionUnit M V *
    (xClassFunctionUnit M (_root_.normalize w)
      (monic_normalize hw).ne_zero)⁻¹
/-! ## Exact oriented update -/
/-- The raw oriented class attached to an integral semirepresentative.  The
`-1` agrees exactly with `mumfordRaw` on balanced representatives. -/
def semiMumfordRaw (D : SemiMumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D,
    Multiplicative.ofAdd (D.nInf - 1))
def semiMumfordClass (O : InfinityOrder M) (D : SemiMumford M) :
    OrientedPic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range
      (semiMumfordRaw M D)
theorem semiMumfordClass_eq_iff
    (O : InfinityOrder M) (D₁ D₂ : SemiMumford M) :
    semiMumfordClass M O D₁ = semiMumfordClass M O D₂ ↔
      ∃ alpha : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁ *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M)
                alpha =
            mumfordIdealUnit M D₂ ∧
        Multiplicative.ofAdd (D₁.nInf - 1) *
              O.ordPlus alpha =
            Multiplicative.ofAdd (D₂.nInf - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₁) =
    QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨alpha, congrArg Prod.fst hmul, congrArg Prod.snd hmul⟩
  · rintro ⟨alpha, hIdeal, hInf⟩
    refine ⟨principalOriented M O alpha,
      MonoidHom.mem_range.mpr ⟨alpha, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf
@[simp] theorem semiMumfordClass_toSemi
    (O : InfinityOrder M) (D : Mumford M) :
    semiMumfordClass M O D.toSemi = classOf M O D := rfl
/-- The unique integer correction forced by the order of the principal
function `(Y-V)/_root_.normalize(w)` at the chosen positive infinity. -/
def cantorNextNInf
    (O : InfinityOrder M) (D : SemiMumford M)
    (V w : K[X]) (hw : w ≠ 0) : ℤ :=
  D.nInf -
    Multiplicative.toAdd
      (O.ordPlus (cantorCorrectionUnit M V w hw))
/-- One structurally complete Cantor step, including the sign of the next
graph polynomial and the exact oriented-infinity correction. -/
def cantorNextSemi
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  cantorConjugateSemi M D V w
    (cantorNextNInf M O D V w hw) hcurve hw
@[simp] theorem cantorNextSemi_u
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u = _root_.normalize w := rfl
@[simp] theorem cantorNextSemi_nInf
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).nInf =
      D.nInf -
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) := rfl
theorem natDegree_normalize_eq
    (p : K[X]) :
    (_root_.normalize p).natDegree = p.natDegree := by
  exact natDegree_eq_natDegree degree_normalize
@[simp] theorem cantorNextSemi_natDegree
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u.natDegree =
      w.natDegree := by
  rw [cantorNextSemi_u, natDegree_normalize_eq]
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction =====
section
/-!
# Structural reduction of oriented sextic ideals

This file joins the two algebraic seams:

* polynomial-content division produces a primitive integral ideal;
* primitive integral ideals have semi-Mumford graph form.

It then packages the well-founded affine-degree step.  Infinity balancing
is deliberately a separate phase.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
/-! ## A canonical affine-degree step -/
theorem degreeLift_curve_dvd (D : SemiMumford M) :
    D.u ∣ M.f - (degreeLift M D) ^ 2 := by
  unfold degreeLift
  split_ifs
  · obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨w - 2 * D.v - D.u, ?_⟩
    calc
      M.f - (D.v + D.u) ^ 2 =
          (M.f - D.v ^ 2) -
            2 * D.u * D.v - D.u ^ 2 := by ring
      _ = D.u * w - 2 * D.u * D.v - D.u ^ 2 := by
            rw [hw]
      _ = D.u * (w - 2 * D.v - D.u) := by ring
  · exact D.curve_dvd
def degreeStepFactor (D : SemiMumford M) : K[X] :=
  Classical.choose (degreeLift_curve_dvd M D)
theorem degreeStepFactor_spec (D : SemiMumford M) :
    M.f - (degreeLift M D) ^ 2 =
      D.u * degreeStepFactor M D :=
  Classical.choose_spec (degreeLift_curve_dvd M D)
theorem degreeStepFactor_ne_zero (D : SemiMumford M) :
    degreeStepFactor M D ≠ 0 :=
  cantorFactor_ne_zero M D.u (degreeLift M D)
    (degreeStepFactor M D) (degreeStepFactor_spec M D)
def degreeStep
    (D : SemiMumford M) :
    SemiMumford M :=
  cantorNextSemi M O D (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)
theorem degreeStep_lt
    (D : SemiMumford M) (hlarge : 2 < D.u.natDegree) :
    (degreeStep M O D).u.natDegree < D.u.natDegree := by
  unfold degreeStep
  rw [cantorNextSemi_natDegree]
  by_cases hthree : D.u.natDegree = 3
  · have hspec :
        M.f - (D.v + D.u) ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    have hle :=
      (cubicCantorFactor M D (degreeStepFactor M D) hthree
        hspec).2
    omega
  · have hspec :
        M.f - D.v ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    apply cantorFactor_natDegree_lt M D
      (degreeStepFactor M D) hspec
    omega
def reduceDegree (D : SemiMumford M) : LowDegreeSemi M :=
  if hsmall : D.u.natDegree ≤ 2 then
    ⟨D, hsmall⟩
  else
    reduceDegree (degreeStep M O D)
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
/-!
# Structural infinity balancing for the true `X₁(13)` sextic

The polynomial used here is exactly

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Its positive-infinity cubic part is

`s = X³ + 2X² + X - 1`,

with the exact low-degree identity `f - s² = 4X(X+1)`.  This file builds
the two adapted Cantor lifts needed to balance the integer at infinity.
There is no divisor enumeration or Riemann--Roch input.
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13MumfordInfinityBalance
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
variable (D : N13Mumford.SemiMumford K)
/-! ## The two adapted lifts -/
theorem plusFactor_ne_zero :
    plusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (plusLift D) (plusFactor D) (plusFactor_spec D)
theorem minusFactor_ne_zero :
    minusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (minusLift D) (minusFactor D) (minusFactor_spec D)
/-! ## Degree bounds -/
theorem plusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (plusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (plusFactor D).natDegree =
        (N13Mumford.f K - (plusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (plusFactor_ne_zero D), ← plusFactor_spec D]
  have hnum := plusNumerator_natDegree_le D hdeg
  omega
theorem minusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (minusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (minusFactor D).natDegree =
        (N13Mumford.f K - (minusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (minusFactor_ne_zero D), ← minusFactor_spec D]
  have hnum := minusNumerator_natDegree_le D hdeg
  omega
/-! ## Leading terms at the two infinities -/
theorem plusYSub_minus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).coeff
        (-3 : ℤ) = -2 := by
  rw [ySubClass, map_sub,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass]
  change
    (N13InfinityMinus.ySeriesMinus K -
      N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = -2
  rw [N13InfinityMinus.ySeriesMinus_eq_neg,
    HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalPlusLift_coeff_neg_three D hdeg]
  norm_num
/-! ## Exact orders of the principal Cantor corrections -/
theorem plusNormNumerator_ne_zero :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 ≠ 0 := by
  rw [plusNormNumerator_eq D]
  exact neg_ne_zero.mpr
    (mul_ne_zero D.u_monic.ne_zero (plusFactor_ne_zero D))
theorem plusNormNumerator_natDegree :
    (N13BranchNorm.normNumerator K (-(plusLift D)) 1).natDegree =
      D.u.natDegree + (plusFactor D).natDegree := by
  rw [plusNormNumerator_eq D, natDegree_neg,
    natDegree_mul D.u_monic.ne_zero (plusFactor_ne_zero D)]
theorem ordPlus_ySubFunctionUnit
    (V : K[X]) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (ySubFunctionUnit (N13Mumford.model K) V)) =
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) V)).order := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (ySubClass (N13Mumford.model K) V))).order = _
  rw [N13Infinity.functionFieldToLaurent_algebraMap]
theorem ordPlus_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (xClassFunctionUnit (N13Mumford.model K) p hp)) =
      -(p.natDegree : ℤ) := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (xClass (N13Mumford.model K) p))).order =
      -(p.natDegree : ℤ)
  rw [N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass]
  exact N13BranchNorm.evalPoly_order K p hp
/-! ## The two class-preserving balancing steps -/
def plusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)
def minusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)
@[simp] theorem plusStep_natDegree :
    (plusStep D).u.natDegree = (plusFactor D).natDegree := by
  rw [plusStep, cantorNextSemi_natDegree]
@[simp] theorem minusStep_natDegree :
    (minusStep D).u.natDegree = (minusFactor D).natDegree := by
  rw [minusStep, cantorNextSemi_natDegree]
def plusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := plusStep E.toSemi
  degree_le_two := by
    rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two E.toSemi E.degree_le_two
def minusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := minusStep E.toSemi
  degree_le_two := by
    rw [minusStep_natDegree]
    exact minusFactor_natDegree_le_two E.toSemi E.degree_le_two
/-! ## A well-founded measure for the two balance walls -/
/-! ## Structural infinity balancing -/
end
end MazurProof.N13MumfordInfinityBalance
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic =====
section
/-!
# The N13 two-adic Abel chart inside the oriented Picard group

Every pair in the two distinguished residue disks gives smooth integral
generalized Mumford data.  After extending coefficients and completing the
square, the resulting standard sextic semirepresentative already has degree
two and infinity balance zero.  It is therefore a balanced Mumford
representative over `ℚ₂`.

Unique balanced normal forms make the resulting map to the oriented Picard
group injective.  Translating by the distinguished base pair gives the
faithful chart centred at the identity.  Thus the remaining geometric input
for the formal-kernel argument is existence of representatives in this
chart, not their uniqueness.
-/
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartPic
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
namespace DiskPair
variable (P : DiskPair)
theorem sexticSemi_u_natDegree :
    (N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0).u.natDegree = 2 := by
  rw [N13TwoAdicMumfordTransport.sexticSemi_u,
    N13TwoAdicAbelChartData.DiskPair.smoothMumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply,
    P.u_monic.natDegree_map]
  exact P.u_natDegree
/-- The standard sextic representative of a two-disk divisor is already
balanced: its affine degree is two and its infinity multiplicity is zero. -/
def mumford :
    N13Mumford.Mumford Q₂ := by
  let D :=
    N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0
  exact
    { u := D.u
      v := D.v
      nInf := 0
      u_monic := D.u_monic
      deg_u := by
        rw [P.sexticSemi_u_natDegree]
      v_reduced := D.v_reduced
      curve_dvd := D.curve_dvd
      infinity_bound := by
        rw [P.sexticSemi_u_natDegree] }
@[simp] theorem mumford_u :
    P.mumford.u =
      N13TwoAdicMumfordTransport.mapPoly P.u := rfl
@[simp] theorem mumford_v :
    P.mumford.v =
      (N13TwoAdicMumfordTransport.sexticSemi
        P.smoothMumford 0).v := rfl
@[simp] theorem mumford_nInf :
    P.mumford.nInf = 0 := rfl
/-- The oriented Picard class of the two-disk divisor. -/
def pic : Pic :=
  SexticMumford.classOf
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    P.mumford
/-- Translate the chart so that the distinguished divisor is the identity. -/
def centeredPic : DiskPair → Pic :=
  fun P => P.pic -
    pic N13TwoAdicAbelChartData.basePair
@[simp] theorem centeredPic_basePair :
    centeredPic N13TwoAdicAbelChartData.basePair = 0 := by
  simp [centeredPic]
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartPic
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoAdicAbelChartRecover
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT
abbrev Pic : Type :=
  N13TwoAdicAbelChartPic.Pic
namespace NearBaseMumford
variable (D : NearBaseMumford)
/-- Every two-disk divisor gives near-base integral data. -/
def ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    NearBaseMumford where
  toSmoothMumford₂ := P.smoothMumford
  reduce_u := P.reducePoly_u
  reduce_v := P.reducePoly_v
@[simp] theorem ofDiskPair_u
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).u = P.u := rfl
@[simp] theorem ofDiskPair_v
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).v = P.v := rfl
/-- The root of `u` in the residue disk of `-1`. -/
theorem exists_root_negOneDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x + 1 ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic (-1) D.u_eval_negOne_mem
      (D.derivative_eval_negOne_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx
def x₁ : R₂ :=
  Classical.choose D.exists_root_negOneDisk
theorem x₁_spec :
    D.u.eval D.x₁ = 0 ∧ D.x₁ + 1 ∈ maximal :=
  Classical.choose_spec D.exists_root_negOneDisk
/-- The disk pair cut out by the two Hensel factors of `u`. -/
def diskPair :
    N13TwoAdicAbelChartData.DiskPair where
  x₀ := D.x₀
  x₁ := D.x₁
  x₀_mem := D.x₀_spec.2
  x₁_add_one_mem := D.x₁_spec.2
@[simp] theorem diskPair_x₀ :
    D.diskPair.x₀ = D.x₀ := rfl
@[simp] theorem diskPair_x₁ :
    D.diskPair.x₁ = D.x₁ := rfl
theorem diskPair_u_natDegree :
    D.diskPair.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C D.diskPair.x₀).ne_zero
      (monic_X_sub_C D.diskPair.x₁).ne_zero]
  simp
/-- Generalized Mumford graph ideals only depend on `v` modulo `u`. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v w : R₂[X]) (hvw : u ∣ v - w) :
    N13GeneralizedMumfordIntegral.mumfordIdeal u v =
      N13GeneralizedMumfordIntegral.mumfordIdeal u w := by
  obtain ⟨q, hq⟩ := hvw
  have hmultiple :
      N13GeneralizedMumfordIntegral.xClass (v - w) =
        N13GeneralizedMumfordIntegral.xClass u *
          N13GeneralizedMumfordIntegral.xClass q := by
    rw [hq, N13GeneralizedMumfordIntegral.xClass_mul]
  have hyw :
      N13GeneralizedMumfordIntegral.ySubClass w =
        N13GeneralizedMumfordIntegral.ySubClass v +
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    simp [N13GeneralizedMumfordIntegral.ySubClass]
  have hyv :
      N13GeneralizedMumfordIntegral.ySubClass v =
        N13GeneralizedMumfordIntegral.ySubClass w -
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    rw [hyw]
    ring
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w
    · rw [hyv, hmultiple]
      exact Ideal.sub_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u w)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u w)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v
    · rw [hyw, hmultiple]
      exact Ideal.add_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u v)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v))
/-- The oriented two-adic Picard class carried by a near-base integral
graph. -/
def pic : Pic :=
  SexticMumford.semiMumfordClass
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    (N13TwoAdicMumfordTransport.sexticSemi
      D.toSmoothMumford₂ 0)
/-- Centre the integral graph class at the selected base divisor. -/
def centeredPic : Pic :=
  D.pic -
    N13TwoAdicAbelChartPic.DiskPair.pic
      N13TwoAdicAbelChartData.basePair
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end

end

-- ===== FLT.Assumptions.MazurProof.N13AbelCompatibleGraphRecover =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelCompatibleGraphRecover =====
section
/-!
# Recovering an N13 disk pair from an Abel-compatible integral graph

A special-fibre Abel equality identifies the reduced quadratic graph with
the selected divisor.  Its graph polynomial is therefore zero modulo the
reduced quadratic, but need not itself reduce coefficientwise to zero.

This file removes that harmless choice of representative.  Replacing `v`
by its monic remainder modulo `u`, and changing `w` by the resulting exact
algebraic formula, preserves the generalized Mumford equation, smoothness,
and graph ideal.  The normalized graph then satisfies the literal hypotheses
of the two-adic Hensel recovery theorem.
-/
open Polynomial
namespace MazurProof.N13AbelCompatibleGraphRecover
noncomputable section
attribute [local instance] MazurProof.N13AbelCompatibleGraphRecover.instFactPrimeOfNatNat_fLT
/-- Monic-remainder normalization preserves both the generalized curve
equation and its smoothness Bezout identity. -/
def normalizeSmoothMumford
    (D : SmoothMumford₂) : SmoothMumford₂ where
  u := D.u
  v := normalizedV D
  w := normalizedW D
  u_monic := D.u_monic
  curve_eq := by
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (D.v - D.u * graphQuotient D) ^ 2 +
            N13GeneralizedMumfordIntegral.hPoly *
              (D.v - D.u * graphQuotient D) -
          N13GeneralizedMumfordIntegral.rhsPoly =
          (D.v ^ 2 +
                N13GeneralizedMumfordIntegral.hPoly * D.v -
              N13GeneralizedMumfordIntegral.rhsPoly) -
            D.u * graphQuotient D *
              (2 * D.v +
                N13GeneralizedMumfordIntegral.hPoly) +
            D.u ^ 2 * graphQuotient D ^ 2 := by ring
      _ =
          D.u *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly) +
              D.u * graphQuotient D ^ 2) := by
        rw [D.curve_eq]
        ring
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine
      ⟨a + 2 * b * graphQuotient D +
          c * graphQuotient D ^ 2,
        b + c * graphQuotient D, c, ?_⟩
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (a + 2 * b * graphQuotient D +
              c * graphQuotient D ^ 2) * D.u +
            (b + c * graphQuotient D) *
              (2 * (D.v - D.u * graphQuotient D) +
                N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
              D.u * graphQuotient D ^ 2) =
          a * D.u +
              b *
                (2 * D.v +
                  N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
            c * D.w := by ring
      _ = 1 := habc
@[simp] theorem normalizeSmoothMumford_u
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).u = D.u := rfl
@[simp] theorem normalizeSmoothMumford_v
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).v = normalizedV D := rfl
end
end MazurProof.N13AbelCompatibleGraphRecover
end

end

-- ===== FLT.Assumptions.MazurProof.N13GenericQuotientLocalization =====
section
-- ===== FLT.Assumptions.MazurProof.N13GenericQuotientLocalization =====
section
/-!
# The generic fibre of a canonical N13 contraction

The quotient by a canonical vertical contraction becomes the original
Mumford quotient after inverting the nonzero two-adic scalars.  Consequently,
a contracted quadratic Mumford quotient has rank two over the two-adic
integers.  No preferred integral basis is used.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13GenericQuotientLocalization
noncomputable section
attribute [local instance] MazurProof.N13GenericQuotientLocalization.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
end
end MazurProof.N13GenericQuotientLocalization
end

end

-- ===== FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore =====
section
/-!
# Graph ideals on a generalized quadratic curve

Let `A` be an algebra generated by a horizontal coordinate map
`R[X] → A` and an ordinate `y` satisfying

`y² + h(x)y = rhs(x)`.

For a polynomial graph `y = v(x)` whose residual curve equation is
`v² + hv - rhs = uw`, the graph ideal and its hyperelliptic conjugate
multiply to the principal ideal `(u)`, provided the displayed generalized
Jacobian admits a Bézout identity.  The proof is purely ring-theoretic and
works over an arbitrary commutative base ring.
-/
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
set_option maxHeartbeats 4000000 in
/-- Polynomial graph data on `y² + hy = rhs`. -/
structure SemiGraph (h rhs : R[X]) where
  u : R[X]
  v : R[X]
  w : R[X]
  curve_eq : v ^ 2 + h * v - rhs = u * w
/-- Hyperelliptic conjugation on graph ordinates. -/
def conjugateV (h v : R[X]) : R[X] :=
  -h - v
def ySubClass
    (xClass : R[X] →+* A) (yClass : A) (v : R[X]) : A :=
  yClass - xClass v
def graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    Ideal A :=
  Ideal.span {xClass u, ySubClass xClass yClass v}
end
end MazurProof.GeneralizedGraphIdealCore
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
/-!
# Integral N13 graph ideals and the affine Jacobian

This file instantiates the generic graph-Jacobian dual frame for the good
integral N13 equation.  A short resultant certificate proves that the two
relative Jacobian rows generate one globally, so every integral Mumford
graph ideal is invertible.  No fixed special graph or point classification
is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralGraphJacobian.instFactPrimeOfNatNat_fLT
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
open N13GeneralizedMumfordIntegral
/-- The two relative Jacobian rows generate the unit ideal globally over
the integral N13 model. -/
theorem exists_jacobian_bezout :
    ∃ a b : IntegralRing,
      a * jacobianX + b * jacobianY = 1 := by
  let u : IntegralRingˣ :=
    thirteen_isUnit.unit
  refine
    ⟨(u⁻¹ : IntegralRingˣ) * bezoutA,
      (u⁻¹ : IntegralRingˣ) * bezoutB, ?_⟩
  calc
    (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutA) * jacobianX +
          (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutB) * jacobianY =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (bezoutA * jacobianX +
            bezoutB * jacobianY) := by ring
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) * 13 := by
      rw [scaled_jacobian_bezout]
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (u : IntegralRing) := by
      rw [thirteen_isUnit.unit_spec]
    _ = 1 := by simp
/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/
abbrev GraphData : Type :=
  GeneralizedGraphIdealCore.SemiGraph
    (hPoly (R := R₂)) (rhsPoly (R := R₂))
end
end MazurProof.N13IntegralGraphJacobian
end

end

-- ===== FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery =====
section
-- ===== FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery =====
section
open Module
open Polynomial
/-!
# Vertical graph recovery from a `{1,y}` basis

A rank-two quotient basis `{1,y}` recovers a monic quadratic relation
`m(y)` and a linear equation `x=a+cy`.  Substituting the latter into the
integral curve equation shows that the vertical curve polynomial factors
as `m*w`.
-/
namespace MazurProof.N13RankTwoVerticalGraphRecovery
noncomputable section
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
structure VerticalGraph where
  m : R₂[X]
  a : R₂
  c : R₂
  w : R₂[X]
  m_monic : m.Monic
  curve_eq :
    verticalCurve (C a + C c * X) = m * w
namespace VerticalGraph
def s (E : VerticalGraph) : R₂[X] :=
  C E.a + C E.c * X
def ideal (E : VerticalGraph) : Ideal IntegralRing :=
  Ideal.span
    ({aeval N13ConcreteGraphRecovery.integralY E.m,
      N13CanonicalContractionQuotient.integralX -
        aeval N13ConcreteGraphRecovery.integralY E.s} :
      Set IntegralRing)
end VerticalGraph
end
end MazurProof.N13RankTwoVerticalGraphRecovery
end

end

-- ===== FLT.Assumptions.MazurProof.N13VerticalGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13VerticalGraphJacobian =====
section
open Polynomial
open scoped nonZeroDivisors
/-!
# The vertical graph Jacobian frame for the N13 integral model

A rank-two contraction with basis `{1, y}` is a vertical graph `x = s(y)`.
Dividing the curve equation by `x - s(y)` supplies the complementary factor.
Together with the differentiated vertical relation, these two factors express both
Jacobian rows in the graph frame. The global Jacobian Bezout identity then makes
the recovered graph ideal invertible.
-/
namespace MazurProof.N13VerticalGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13VerticalGraphJacobian.instFactPrimeOfNatNat_fLT
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev VerticalGraph : Type :=
  N13RankTwoVerticalGraphRecovery.VerticalGraph
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
open N13GeneralizedMumfordIntegral
open N13RankTwoVerticalGraphRecovery
def sValue (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.s
def U (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.m
def G (E : VerticalGraph) : IntegralRing :=
  N13CanonicalContractionQuotient.integralX - sValue E
def W (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.w
def complementPoly (E : VerticalGraph) : IntegralRing[X] :=
  curveInX /ₘ (X - C (sValue E))
def H (E : VerticalGraph) : IntegralRing :=
  (complementPoly E).eval
    N13CanonicalContractionQuotient.integralX
def Hx (E : VerticalGraph) : IntegralRing :=
  (derivative (complementPoly E)).eval
    N13CanonicalContractionQuotient.integralX
end
end MazurProof.N13VerticalGraphJacobian
end

end

-- ===== FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible =====
section
open Module
open Polynomial
open scoped nonZeroDivisors
/-!
# Invertibility of finite quadratic N13 contractions

A finite quadratic contraction admits a literal integral basis `{1,x}` or
`{1,y}`.  The first basis recovers a horizontal integral semigraph; the
second recovers a vertical graph.  The two structural Jacobian frames prove
invertibility in the respective cases.
-/
namespace MazurProof.N13FiniteContractIdealInvertible
noncomputable section
attribute [local instance] MazurProof.N13FiniteContractIdealInvertible.instFactPrimeOfNatNat_fLT
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
end
end MazurProof.N13FiniteContractIdealInvertible
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalArithmetic
noncomputable section
/-- The conjugate Gaussian cubic. -/
def gConj : GI[X] :=
  X ^ 3 + C (2 + 2 * i) * X ^ 2 +
    C (-1 + 2 * i) * X - 1
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

-- ===== FLT.Assumptions.MazurProof.PowerBasisDiscriminant =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.PowerBasisDiscriminant =====
section
/-!
# Structural discriminant identities for power bases

This file supplies two small bridges missing from Mathlib's public API:

* the norm of `q(θ)` is the resultant of the minimal polynomial of `θ`
  with `q`;
* the trace discriminant of a power basis is the polynomial discriminant
  of its minimal polynomial.

The norm proof reindexes the canonical product over embeddings by the
canonical multiset of roots.  It does not choose or enumerate roots and it
does not expand a multiplication matrix.
-/
open Polynomial
open scoped Polynomial BigOperators
namespace MazurProof.PowerBasisDiscriminant
noncomputable section
/-- Polynomial discriminant commutes with a coefficient map for a
positive-degree monic polynomial. -/
theorem discr_map_of_monic_of_degree_pos
    {R S : Type*}
    [CommRing R] [Field S]
    (φ : R →+* S)
    {f : R[X]}
    (hf : f.Monic)
    (hdeg : 0 < f.degree) :
    (f.map φ).discr = φ f.discr := by
  have hdeg' : 0 < (f.map φ).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      hf.natDegree_map φ,
      Polynomial.natDegree_pos_iff_degree_pos]
    exact hdeg
  have hbase := Polynomial.resultant_deriv hdeg
  have hmap := congrArg φ hbase
  have htarget := Polynomial.resultant_deriv hdeg'
  rw [Polynomial.derivative_map, hf.natDegree_map φ] at htarget
  rw [← Polynomial.resultant_map_map
      (f := f)
      (g := f.derivative)
      (m := f.natDegree)
      (n := f.natDegree - 1)
      φ] at hmap
  have heq :
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        (f.map φ).discr =
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        φ f.discr := by
    simpa [hf.leadingCoeff, (hf.map φ).leadingCoeff]
      using htarget.symm.trans hmap
  exact mul_left_cancel₀
    (pow_ne_zero _
      (neg_ne_zero.mpr one_ne_zero : (-1 : S) ≠ 0))
    heq
end
end MazurProof.PowerBasisDiscriminant
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
/-!
# The Gaussian fraction field as a quadratic number field

The fraction field of `ℤ[i]` has the structural rational basis `(1,i)`.
The only localization point to check is that inverting nonzero ordinary
integers already inverts every nonzero Gaussian integer: `z` divides its
nonzero integer norm `z * star z`.

No embeddings or Gaussian elements are enumerated.
-/
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
/-- Every Gaussian integer is integral over `ℤ`, structurally from its
decomposition `a + i b`. -/
instance gaussianIntIntegral :
    Algebra.IsIntegral ℤ GI where
  isIntegral := by
    rintro ⟨a, b⟩
    rw [Zsqrtd.decompose]
    exact
      (isIntegral_intCast a).add
        (i_integral.mul (isIntegral_intCast b))
/-! ## The integral basis `(1,i)` -/
/-! ## Cofinality of ordinary integer denominators -/
/-- Every nonzero Gaussian denominator divides a nonzero ordinary integer:
choose its norm. -/
theorem nonZeroGaussian_dvd_intDenom
    (z : GI) (hz : z ∈ nonZeroDivisors GI) :
    ∃ m ∈ intDenoms, z ∣ m := by
  have hz0 : z ≠ 0 :=
    nonZeroDivisors.ne_zero hz
  have hnorm0 : Zsqrtd.norm z ≠ 0 := by
    simpa using hz0
  refine ⟨(Zsqrtd.norm z : GI), ?_, ?_⟩
  · have hm : Zsqrtd.norm z ∈ nonZeroDivisors ℤ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hnorm0
    simpa [intDenoms] using
      (Algebra.mem_algebraMapSubmonoid_of_mem
        (S := GI)
        (⟨Zsqrtd.norm z, hm⟩ : nonZeroDivisors ℤ))
  · exact ⟨star z, Zsqrtd.norm_eq_mul_conj z⟩
/-- The Gaussian fraction field is also the localization obtained by
inverting only the nonzero ordinary integers. -/
instance intDenomLocalization :
    IsLocalization intDenoms K := by
  refine
    (IsLocalization.iff_of_le_of_exists_dvd
      (S := K)
      (M := intDenoms)
      (nonZeroDivisors GI)
      intDenoms_le_nonZeroDivisors
      ?_).2 inferInstance
  intro z hz
  exact nonZeroGaussian_dvd_intDenom z hz
/-! ## The localized rational basis -/
/-- The rational basis `(1,i)` of `Frac(ℤ[i])`. -/
def gaussianBasis : Basis (Fin 2) ℚ K :=
  Basis.localizationLocalization
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis
@[simp] theorem gaussianBasis_zero :
    gaussianBasis (0 : Fin 2) = 1 := by
  simp [gaussianBasis]
@[simp] theorem gaussianBasis_one :
    gaussianBasis (1 : Fin 2) = iK := by
  simp [gaussianBasis, iK]
instance gaussianFiniteDimensional :
    FiniteDimensional ℚ K :=
  Module.Finite.of_basis gaussianBasis
instance gaussianNumberField : NumberField K where
  to_charZero := inferInstance
  to_finiteDimensional := gaussianFiniteDimensional
/-! ## Power basis, minimal polynomial, and discriminant -/
@[simp] theorem trace_one_gaussian :
    Algebra.trace ℚ K (1 : K) = 2 := by
  simpa using
    (Algebra.trace_algebraMap_of_basis gaussianBasis (1 : ℚ))
@[simp] theorem trace_neg_one_gaussian :
    Algebra.trace ℚ K (-1 : K) = -2 := by
  simp
/-- The algebra norm in the integral basis `(1,i)` is the usual Gaussian
norm.  The proof is the symbolic determinant of multiplication by
`a + bi`, not a computation on Gaussian elements. -/
theorem algebraNorm_eq_gaussianNorm (z : GI) :
    Algebra.norm ℤ z = Zsqrtd.norm z := by
  rw [Algebra.norm_eq_matrix_det gaussianIntBasis,
    Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    gaussianIntBasis_zero, gaussianIntBasis_one,
    gaussianIntBasis_repr_apply, i]
  change z.re * z.re + z.im * z.im = Zsqrtd.norm z
  simp [Zsqrtd.norm]
@[simp] theorem algebraNorm_pi :
    Algebra.norm ℤ pi = 13 := by
  rw [algebraNorm_eq_gaussianNorm, pi_norm]
@[simp] theorem algebraNorm_pi_sq :
    Algebra.norm ℤ (pi ^ 2) = 13 ^ 2 := by
  rw [map_pow, algebraNorm_pi]
end
end MazurProof.N13GaussianFractionField
end

end

-- ===== FLT.Assumptions.MazurProof.FakeSquareClass =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.FakeSquareClass =====
section
/-!
# The fake square-class target

This file defines
`Lˣ / ((Lˣ)^2 * image(Kˣ))`
for a homomorphism of commutative rings `K →+* L`.

The product of the two subgroups is written as their supremum: `Lˣ` is
commutative, so this is the subgroup generated by squares and rational scalars.
-/
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- The map on unit groups induced by a ring homomorphism `K →+* L`. -/
def scalarUnitsMap (e : K →+* L) : Kˣ →* Lˣ := Units.map e.toMonoidHom
/-- Squares together with the scalar subgroup of `Lˣ`. -/
def fakeSquareClassSubgroup (e : K →+* L) : Subgroup Lˣ :=
  Subgroup.square Lˣ ⊔ (⊤ : Subgroup Kˣ).map (scalarUnitsMap e)
/-- The usual fake square-class target. -/
abbrev Target (e : K →+* L) : Type _ :=
  Lˣ ⧸ fakeSquareClassSubgroup e
instance (e : K →+* L) : CommGroup (Target e) := inferInstance
end MazurProof.FakeSquareClass
end

end

-- ===== FLT.Assumptions.MazurProof.N13SexticSquareclass =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticSquareclass =====
section
/-!
# The rational-scalar survivor in the N13 fake square-class target

The apparent second local survivor in the weak two-descent is not a second
geometric class.  In the sextic algebra it differs from `13` by an explicit
square.  The proof first compresses the five power-basis expressions to two
degree-five polynomials `B` and `C`; it never expands the final product to
degree thirty-three.
-/
open Polynomial
namespace MazurProof.N13SexticSquareclass
noncomputable section
/-- Twice a generator of the ramification-three prime above 13. -/
def A : ℚ[X] := -X ^ 3 - 2 * X ^ 2 - X + 3
/-- Twice a generator of the residue-degree-three prime above 13. -/
def Q : ℚ[X] :=
  -6 * X ^ 5 - 21 * X ^ 4 - 27 * X ^ 3 - 3 * X ^ 2 - 12 * X - 5
/-- `ζ e₁ a = B / 2` in `ℚ[T]/(f)`. -/
def B : ℚ[X] := 3 * X ^ 5 + 10 * X ^ 4 + 11 * X ^ 3 - 3 * X ^ 2 + 4 * X + 6
/-- `e₂ a q = -C` in `ℚ[T]/(f)`. -/
def C : ℚ[X] := 5 * X ^ 5 + 18 * X ^ 4 + 23 * X ^ 3 - X + 4
def primeA : SexticAlgebra := halfOfPoly A
def primeQ : SexticAlgebra := halfOfPoly Q
def survivor : SexticAlgebra :=
  e2 * primeA * primeQ
def squareFactor : SexticAlgebra :=
  zeta * e1 * primeA
end
end MazurProof.N13SexticSquareclass
end

end

-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
/-!
# Irreducibility of the N13 sextic

The sextic defining the fake two-descent algebra is irreducible over `ℚ`.
We prove this structurally by reduction modulo three.  An irreducible
degree-`d` factor over `𝔽₃` divides `X ^ (3 ^ d) - X`, by applying finite-field
Frobenius in its adjoin-root field.  Three short Bézout identities exclude
degrees one through three, which is the full Rabin test for a sextic.  No
finite-field polynomials are enumerated.
-/
open Polynomial
namespace MazurProof.N13SexticIrreducible
noncomputable section
/-- An explicit, opt-in `Fact` for clients that need the field structure on
the sextic algebra.  Use `letI := sexticIrreducibleFact`; it is deliberately
not a global instance. -/
@[reducible] def sexticIrreducibleFact :
    Fact (Irreducible N13SexticSquareclass.f) :=
  ⟨squareclass_f_irreducible⟩
/-- The field structure on the sextic algebra, exported without installing a
global instance. -/
@[reducible] noncomputable def sexticAlgebraField :
    Field N13SexticSquareclass.SexticAlgebra := by
  letI := sexticIrreducibleFact
  infer_instance
end
end MazurProof.N13SexticIrreducible
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFieldEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFieldEquiv =====
section
/-!
# Equivalence of the sextic and Gaussian-cubic N13 fields

The root `α` of the translated Gaussian cubic gives

`θ = α + 9`.

This file proves that sending the sextic generator to this element is an
isomorphism from the original degree-six algebra to the Gaussian cubic
number field.  Equal absolute dimensions make the injective field map
surjective; no inverse polynomial is searched for.

The intrinsic order-four element of the sextic field maps to the Gaussian
unit `i`.  Consequently the short formulas for the descent generators show
directly that all of them are algebraic integers in the structural absolute
ring of integers.
-/
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField
/-! ## Integrality of the structural generators -/
end
end MazurProof.N13GaussianFieldEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerValue =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerValue =====
section
/-!
# The N13 Mumford fake-Kummer value

Let `θ` be the sextic root.  The branch specialization

`ℚ[X,Y]/(Y²-f(X)) → ℚ(θ),  X ↦ θ,  Y ↦ 0`

turns the quadratic norm of an affine function into a square.  For a
balanced Mumford representative `(u,v,n∞)`, its raw fake-Kummer value is
the unit `u(θ)`, modulo squares and rational scalars.

Irreducibility of the sextic is used only to install the field structure
locally and hence turn the nonzero element `u(θ)` into a unit.  This file
does not yet assert that the value is independent of the chosen Mumford
representative; that is the next principal-ideal relation theorem.
-/
open Polynomial
namespace MazurProof.N13MumfordKummerValue
noncomputable section
open SexticMumford
local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField
theorem thetaBranch_root :
    (curvePoly M).eval₂ (AdjoinRoot.mk f) (0 : L) = 0 := by
  simp only [curvePoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    OfNat.ofNat]
  rw [show M.f = f by rfl, AdjoinRoot.mk_self]
  change (0 : L) ^ 2 - 0 = 0
  norm_num
/-- Specialization to the branch `X=θ`, `Y=0`. -/
def thetaBranch : N13Mumford.CoordinateRing ℚ →+* L :=
  AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root
@[simp] theorem thetaBranch_xClass (p : ℚ[X]) :
    thetaBranch (xClass M p) = AdjoinRoot.mk f p := by
  change
    AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root
        (AdjoinRoot.of (curvePoly M) p) =
      AdjoinRoot.mk f p
  rw [AdjoinRoot.lift_of]
/-- Evaluation `u(θ)` for a balanced Mumford representative. -/
def uTheta (D : N13Mumford.Mumford ℚ) : L :=
  thetaBranch (xClass M D.u)
@[simp] theorem uTheta_eq_mk (D : N13Mumford.Mumford ℚ) :
    uTheta D = AdjoinRoot.mk f D.u := by
  simp [uTheta]
theorem uTheta_ne_zero (D : N13Mumford.Mumford ℚ) :
    uTheta D ≠ 0 := by
  rw [uTheta_eq_mk]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (N13Mumford.f_monic ℚ) D.u_monic.ne_zero
  change D.u.natDegree < (N13Mumford.f ℚ).natDegree
  rw [N13Mumford.f_natDegree]
  have hdeg : D.u.natDegree ≤ 2 := D.deg_u
  omega
/-- The nonzero field element `u(θ)`, packaged as a unit. -/
def uThetaUnit (D : N13Mumford.Mumford ℚ) : Lˣ :=
  Units.mk0 (uTheta D) (uTheta_ne_zero D)
@[simp] theorem uThetaUnit_val (D : N13Mumford.Mumford ℚ) :
    (uThetaUnit D : L) = uTheta D := rfl
abbrev FakeTarget : Type :=
  Additive (FakeSquareClass.Target (algebraMap ℚ L))
/-- The raw fake-Kummer value of a balanced Mumford representative. -/
def mumfordFakeClass (D : N13Mumford.Mumford ℚ) : FakeTarget :=
  Additive.ofMul
    (((uThetaUnit D : Lˣ)) :
      FakeSquareClass.Target (algebraMap ℚ L))
@[simp] theorem uTheta_zero :
    uTheta (SexticMumford.zero M) = 1 := by
  simp [uTheta]
@[simp] theorem uThetaUnit_zero :
    uThetaUnit (SexticMumford.zero M) = 1 := by
  apply Units.ext
  exact uTheta_zero
@[simp] theorem mumfordFakeClass_zero :
    mumfordFakeClass (SexticMumford.zero M) = 0 := by
  change
    Additive.ofMul
        (((uThetaUnit (SexticMumford.zero M) : Lˣ)) :
          FakeSquareClass.Target (algebraMap ℚ L)) =
      0
  rw [uThetaUnit_zero]
  rfl
end
end MazurProof.N13MumfordKummerValue
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerRelation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerRelation =====
section
/-!
# Principal relations and the N13 Mumford fake-Kummer value

The value `u(θ)` must not depend on a balanced Mumford representative.  The
reason is ideal-theoretic, not a case split on the degree of `u`.

If

`I₁ (α) = I₂`,

then multiplying this relation by its hyperelliptic conjugate gives

`(u₁) (α * ᾱ) = (u₂)`.

The ratio of the two generators is therefore a unit of the affine coordinate
ring.  It is fixed by hyperelliptic conjugation, hence is a nonzero rational
scalar.  Integral numerator and conumerator witnesses then give

`u₁(θ) u₂(θ) = q z(θ)^2`.

Thus the two values have the same class modulo squares and rational scalars.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13MumfordKummerRelation
noncomputable section
open SexticMumford
local instance sexticAlgebraField :
    Field N13MumfordKummerValue.L :=
  N13SexticIrreducible.sexticAlgebraField
end
end MazurProof.N13MumfordKummerRelation
end

end

-- ===== FLT.Assumptions.MazurProof.N13LowDegreeKummerHom =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LowDegreeKummerHom =====
section
/-!
# The N13 fake-Kummer homomorphism from low-degree semirepresentatives

The fake Kummer value depends on the affine Mumford ideal and the polynomial
`u`, but not on the separate infinity-balance inequalities.  The structural
Cantor reduction already gives every oriented Picard class a semirepresentative
with `deg u ≤ 2`.

We therefore attach to such a semirepresentative an auxiliary balanced
Mumford datum with the same `(u,v)` and infinity coordinate zero.  This datum
is used only to reuse the existing `u(θ)` and principal-relation theorems; its
oriented class is not substituted for the original semirepresentative's
class.  Principal relations are extracted from the original oriented
classes, where their actual integer infinity coordinates are retained.

This removes infinity balancing from the dependency chain of the N13
fake-Kummer homomorphism.
-/
namespace MazurProof.N13LowDegreeKummerHom
noncomputable section
open SexticMumford
abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ
abbrev G : Type :=
  SexticMumford.ConcretePic M O
abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget
/-- Forget the original infinity coordinate only for evaluation of `u(θ)`.
The affine ideal and all its proofs are unchanged. -/
def asMumford (D : LowRep) : N13Mumford.Mumford ℚ where
  u := D.toSemi.u
  v := D.toSemi.v
  nInf := 0
  u_monic := D.toSemi.u_monic
  deg_u := D.degree_le_two
  v_reduced := D.toSemi.v_reduced
  curve_dvd := D.toSemi.curve_dvd
  infinity_bound := by
    simpa using D.degree_le_two
@[simp] theorem asMumford_u (D : LowRep) :
    (asMumford D).u = D.toSemi.u := rfl
@[simp] theorem asMumford_v (D : LowRep) :
    (asMumford D).v = D.toSemi.v := rfl
@[simp] theorem asMumford_nInf (D : LowRep) :
    (asMumford D).nInf = 0 := rfl
theorem mumfordIdealUnit_asMumford (D : LowRep) :
    mumfordIdealUnit M (asMumford D).toSemi =
      mumfordIdealUnit M D.toSemi := by
  apply Units.ext
  rfl
/-- The oriented class uses the original integer infinity coordinate. -/
def lowClass (D : LowRep) : G :=
  semiMumfordClass M O D.toSemi
/-- The raw fake value uses only the shared affine data `(u,v)`. -/
def lowFakeClass (D : LowRep) : Target :=
  N13MumfordKummerValue.mumfordFakeClass (asMumford D)
@[simp] theorem lowClass_zero :
    lowClass zeroLow = 0 := by
  change
    semiMumfordClass M O (SexticMumford.zero M).toSemi = 0
  rw [semiMumfordClass_toSemi, classOf_zero]
@[simp] theorem lowFakeClass_zero :
    lowFakeClass zeroLow = 0 := by
  change
    N13MumfordKummerValue.mumfordFakeClass
        (asMumford zeroLow) =
      0
  change
    Additive.ofMul
        ((((N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) :
            N13MumfordKummerValue.Lˣ))) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      0
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) = 1 := by
    apply Units.ext
    change
      N13MumfordKummerValue.uTheta (asMumford zeroLow) = 1
    simp [N13MumfordKummerValue.uTheta_eq_mk,
      asMumford, zeroLow]
  rw [hu]
  rfl
end
end MazurProof.N13LowDegreeKummerHom
end

end

-- ===== FLT.Assumptions.MazurProof.EvenSexticNormPair =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.EvenSexticNormPair =====
section
/-!
# Full norm-pair and fake targets for an even sextic

For an even sextic, the full two-descent target remembers a pair
`(α,s)` satisfying `N(α)=s²`.  It is quotiented by

* `(β²,N(β))`, and
* `(q,q³)` for ground-field scalars.

Forgetting the second coordinate gives the usual fake square-class target.
This file develops that target algebra for abstract commutative groups.  The
only sextic-specific input is that the norm of a scalar is its sixth power.
No Picard group or Kummer exactness theorem is used here.
-/
namespace MazurProof.EvenSexticNormPair
noncomputable section
variable {A B : Type*} [CommGroup A] [CommGroup B]
/-- Pairs `(α,s)` satisfying the norm-square equation. -/
def normPairSubgroup (N : A →* B) : Subgroup (A × B) where
  carrier := {p | N p.1 = p.2 ^ 2}
  one_mem' := by
    change N 1 = (1 : B) ^ 2
    simp
  mul_mem' := by
    rintro ⟨a, s⟩ ⟨b, t⟩ ha hb
    change N (a * b) = (s * t) ^ 2
    rw [map_mul, ha, hb, mul_pow]
  inv_mem' := by
    rintro ⟨a, s⟩ ha
    change N a⁻¹ = s⁻¹ ^ 2
    rw [map_inv, ha, inv_pow]
abbrev NormPair (N : A →* B) :=
  ↥(normPairSubgroup N)
/-- Projection of a norm pair to its first coordinate. -/
def fstHom (N : A →* B) : NormPair N →* A :=
  (MonoidHom.fst A B).comp (normPairSubgroup N).subtype
@[simp] theorem fstHom_apply (N : A →* B) (p : NormPair N) :
    fstHom N p = p.1.1 :=
  rfl
/-- Projection of a norm pair to its chosen norm root. -/
def sndHom (N : A →* B) : NormPair N →* B :=
  (MonoidHom.snd A B).comp (normPairSubgroup N).subtype
@[simp] theorem sndHom_apply (N : A →* B) (p : NormPair N) :
    sndHom N p = p.1.2 :=
  rfl
/-- The square/norm gauge element `(β²,N(β))`. -/
def chi (N : A →* B) : A →* NormPair N where
  toFun β :=
    ⟨(β ^ 2, N β), by
      change N (β ^ 2) = (N β) ^ 2
      rw [map_pow]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' β γ := by
    apply Subtype.ext
    ext <;> simp [mul_pow]
@[simp] theorem chi_fst (N : A →* B) (β : A) :
    fstHom N (chi N β) = β ^ 2 :=
  rfl
@[simp] theorem chi_snd (N : A →* B) (β : A) :
    (chi N β : A × B).2 = N β :=
  rfl
/-- The scalar gauge element `(q,q³)`.  The hypothesis is the degree-six
norm formula for scalars. -/
def iota (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    B →* NormPair N where
  toFun q :=
    ⟨(e q, q ^ 3), by
      change N (e q) = (q ^ 3) ^ 2
      rw [norm_scalar]
      group⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    ext <;> simp [mul_pow]
@[simp] theorem iota_fst
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    fstHom N (iota N e norm_scalar q) = e q :=
  rfl
@[simp] theorem iota_snd
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    (iota N e norm_scalar q : A × B).2 = q ^ 3 :=
  rfl
/-- Squares and scalars in the first-coordinate fake target. -/
def fakeGauge (e : B →* A) : Subgroup A :=
  Subgroup.square A ⊔ (⊤ : Subgroup B).map e
abbrev FakeTarget (e : B →* A) :=
  A ⧸ fakeGauge e
/-- The two gauge families in the full norm-pair target. -/
def fullGauge
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    Subgroup (NormPair N) :=
  (chi N).range ⊔ (iota N e norm_scalar).range
abbrev FullTarget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :=
  NormPair N ⧸ fullGauge N e norm_scalar
/-- Forget the norm-root coordinate before quotienting the full target. -/
def forgetRaw (N : A →* B) (e : B →* A) :
    NormPair N →* FakeTarget e :=
  (QuotientGroup.mk' (fakeGauge e)).comp (fstHom N)
@[simp] theorem forgetRaw_apply
    (N : A →* B) (e : B →* A) (p : NormPair N) :
    forgetRaw N e p =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl
theorem fullGauge_le_forgetRaw_ker
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    fullGauge N e norm_scalar ≤ (forgetRaw N e).ker := by
  rw [fullGauge, sup_le_iff]
  constructor
  · rintro _ ⟨β, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_left
    change β ^ 2 ∈ Subgroup.square A
    exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
  · rintro _ ⟨q, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem e trivial
/-- Forgetting the second coordinate descends from the full target to the
fake target. -/
def forget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    FullTarget N e norm_scalar →* FakeTarget e :=
  QuotientGroup.lift
    (fullGauge N e norm_scalar)
    (forgetRaw N e)
    (fullGauge_le_forgetRaw_ker N e norm_scalar)
@[simp] theorem forget_mk
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar) p) =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl
/-- A norm pair with first coordinate one and square-one second coordinate.
Over the rational units there are only the choices `+1` and `-1`. -/
def signPair (N : A →* B) (ε : B) (hε : ε ^ 2 = 1) :
    NormPair N :=
  ⟨(1, ε), by
    change N 1 = ε ^ 2
    simpa using hε.symm⟩
/-! ## The kernel of forgetting the norm root -/
/-- Remove a square gauge and a scalar gauge from a norm pair. -/
def normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    NormPair N :=
  p / (chi N β * iota N e norm_scalar q)
end
end MazurProof.EvenSexticNormPair
end

end

-- ===== FLT.Assumptions.MazurProof.N13FullNormPair =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FullNormPair =====
section
/-!
# The full norm-pair target for N13

This file specializes the abstract even-sextic target to the sextic field
`L = ℚ[θ]`.  Its full target remembers `(α,s)` with `N(α)=s²`, before
forgetting `s` to obtain the existing fake square-class target.

The kernel of forgetting has at most the identity and the sign class
represented by `(1,-1)`.  This is target algebra only: it does not assert
the hard principal-genus theorem for the Picard Kummer map.
-/
namespace MazurProof.N13FullNormPair
noncomputable section
open N13SexticSquareclass
local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField
/-- The norm on units of the N13 sextic field. -/
def normUnits : Lˣ →* ℚˣ :=
  Units.map (Algebra.norm ℚ)
/-- Rational scalar units inside the sextic field. -/
def scalarUnits : ℚˣ →* Lˣ :=
  FakeSquareClass.scalarUnitsMap (algebraMap ℚ L)
theorem finrank_L :
    Module.finrank ℚ L = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))
/-- A rational scalar has sextic norm `q⁶`. -/
@[simp] theorem normUnits_scalarUnits (q : ℚˣ) :
    normUnits (scalarUnits q) = q ^ 6 := by
  apply Units.ext
  change
    Algebra.norm ℚ (algebraMap ℚ L (q : ℚ)) =
      (q : ℚ) ^ 6
  simpa [finrank_L] using
    (Algebra.norm_algebraMap (R := ℚ) (S := L) (q : ℚ))
abbrev NormPair : Type :=
  EvenSexticNormPair.NormPair normUnits
abbrev FullTarget : Type :=
  EvenSexticNormPair.FullTarget
    normUnits scalarUnits normUnits_scalarUnits
abbrev FakeTarget : Type :=
  FakeSquareClass.Target (algebraMap ℚ L)
/-- Forget the chosen rational square root of the norm. -/
abbrev forget : FullTarget →* FakeTarget :=
  EvenSexticNormPair.forget
    normUnits scalarUnits normUnits_scalarUnits
/-- The possible extra sign class in the full target. -/
abbrev signClass : FullTarget :=
  QuotientGroup.mk'
      (EvenSexticNormPair.fullGauge
        normUnits scalarUnits normUnits_scalarUnits)
    (EvenSexticNormPair.signPair normUnits (-1) minusOne_sq)
end
end MazurProof.N13FullNormPair
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare =====
section
/-!
# The good-locus square ideal of a normalized N13 Kummer value

Primitive normalization removes the arbitrary content of a rational
Mumford polynomial, but it does not make the other polynomial in the
Mumford pair integral.  We clear those remaining denominators
*homogeneously*: if

`f - v² = u w`

and `U = c u` is the primitive integral normalization, then a single
nonzero integer `d` can be chosen together with integral `V,W` so that

`d² f - V² = U W`.

After evaluating at the integral branch point and inverting the derivative
of `d² f`, the branch ideal `(U(θ),V(θ))` squares to `(U(θ))`.  This is the
principal ideal of the previously constructed `normalizedKummerInteger`.
Thus every denominator and bad-reduction prime is isolated in one
canonical localization; no prime factorization or valuation enumeration is
used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
abbrev O := integralClosure ℤ L
/-! ## The principal-ideal endpoint -/
end
end MazurProof.N13GlobalKummerIdealSquare
end

end

-- ===== FLT.DedekindDomain.AdicValuation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.DedekindDomain.AdicValuation =====
section
/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/
/-!

# Adic Completions

If `A` is a valued ring with field of fractions `K` there are two different
complete rings containing `A` one might define, the first is
`𝒪_v = {x ∈ K_v | v x ≤ 1}` (defined in Lean as `adicCompletionIntegers K v`)
and the second is the `v-adic` completion of `A`. In the case when `A` is a
Dedekind domain these definitions give isomorphic topological `A`-algebras.
This file makes some progress towards this.

## Main theorems/defs

* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers` : The closure of
    `A` in `K_v` is `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField` : The canonical
  isomorphism `A ⧸ v ≅ 𝓞ᵥ / v`.
* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_prodIntegers` : If `s` is
    a set of primes of `A`, then the closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_of_prodAlgebraMap` : If `s` is a finite set
    of primes of `A`, then `K` is dense in `∏_{v ∈ s} K_v`.
* We show (as an unnamed instance) `IsDiscreteValuationRing (𝒪[v.adicCompletion K])`
-/
section
namespace IsDedekindDomain.HeightOneSpectrum
section Multiplicative
open scoped WithZero
end Multiplicative
variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDedekindDomain A] (v : HeightOneSpectrum A)
open scoped WithZero
-- could go in mathlib
/-- The maximal ideal of the integers of the completion of `v`. -/
noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)
lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _
lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl
instance instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩
-- shortcut instances for next def: needed after mathlib #34045
-- dirty hack because of v4.29
namespace adicCompletion
-- IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
open scoped algebraMap in
theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (- 1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]
variable {K} in
theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]
-- shortcut instance for next theorem: needed after mathlib #34045
theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd,
      WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K := ⟨π ^ (-m) * x.val, (mem_adicCompletionIntegers _ K v).mpr (le_of_eq hpow)⟩
  refine ⟨m.toNat, (ValuationSubring.isUnit_of_valued_eq_one a hpow).unit, Subtype.ext ?_⟩
  change x.val = (π : v.adicCompletion K) ^ m.toNat * ((π : v.adicCompletion K) ^ (-m) * x.val)
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by simp [uniformizer_ne_zero hπ]
  rw [← mul_assoc, ← zpow_natCast, m.toNat_of_nonneg hm₀, ← zpow_add₀ hπ0, add_neg_cancel,
    zpow_zero, one_mul]
open scoped algebraMap in
theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn
instance instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_fLT : Ring.DimensionLEOne (v.adicCompletionIntegers K) where
  maximalOfPrime {𝔭} h𝔭_ne_bot h𝔭_prime := by
    let ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭_ne_bot
    let ⟨π, hπ⟩ := exists_uniformizer K v
    obtain ⟨n, ⟨u, rfl⟩⟩ := eq_pow_uniformizer_mul_unit K v hx.2 hπ
    simp only [Units.isUnit, Ideal.mul_unit_mem_iff_mem, ne_eq, mul_eq_zero, pow_eq_zero_iff',
      Units.ne_zero, or_false, not_and, Decidable.not_not] at hx
    by_cases hn : n = 0
    · simp only [hn, pow_zero, ← 𝔭.eq_top_iff_one, implies_true, and_true] at hx
      exact h𝔭_prime.ne_top hx |>.elim
    · rw [h𝔭_prime.pow_mem_iff_mem n (by omega), ← 𝔭.span_singleton_le_iff_mem,
        ← maximalIdeal_eq_span_uniformizer K v hπ] at hx
      exact IsLocalRing.maximalIdeal_le h𝔭_prime.ne_top hx.1
open scoped algebraMap in
instance instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_fLT : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  apply IsPrincipalIdealRing.of_prime
  intro P hP
  by_cases hP_bot : P = ⊥
  · exact hP_bot ▸ bot_isPrincipal
  · let ⟨π, hπ⟩ := exists_uniformizer K v
    use π
    rw [IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_bot)]
    exact maximalIdeal_eq_span_uniformizer K v hπ
instance instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_fLT : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h
open scoped Valued in
instance instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_fLT : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
end adicCompletion
end IsDedekindDomain.HeightOneSpectrum
end
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
/-!
# The simple-root branch of the N13 denominator-prime argument

At a height-one prime away from the different, a primitive quadratic
Mumford polynomial has only two possible behaviours at the integral branch
point.  In the simple-root case, Hensel lifting gives an actual nearby root.
The value of the quadratic at the branch point is then the root difference
times a unit.  The same root difference is a square up to a unit by the
Mumford equation and the unit secant slope of the smooth sextic.

This file packages that structural argument over an arbitrary Henselian
pair.  In particular, the denominator-clearing scale is absorbed into the
square root in the fraction field; no denominator prime is enumerated.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
/-- A quadratic written by its three coefficients. -/
def quadratic
    {R : Type*} [Semiring R] (a b c : R) : R[X] :=
  C a * X ^ 2 + C b * X + C c
/-- The polynomial secant based at `x`: division by `X - x`. -/
def secantAt
    {R : Type*} [CommRing R] (p : R[X]) (x : R) : R[X] :=
  p /ₘ (X - C x)
end
end MazurProof.N13GoodPrimeSimpleRoot
end

end

-- ===== FLT.Assumptions.MazurProof.TowerDiscriminant =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.TowerDiscriminant =====
section
/-!
# Discriminants of tower bases

For a tower `R → S → T`, the discriminant of the product basis is

`disc(b ⋅ c) = disc(b) ^ rank(c) * norm(disc(c))`.

The proof factors the trace matrix into a block-diagonal base trace matrix
and the left-multiplication representation of the relative trace matrix.
It is independent of any particular number field.
-/
open Matrix Module
open scoped Matrix
namespace MazurProof.TowerDiscriminant
noncomputable section
universe uR uS uT uι uκ
variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T]
variable [IsScalarTower R S T]
variable {ι : Type uι} {κ : Type uκ}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]
/-- A constant block-diagonal matrix has one determinant factor per block.
The sole reindexing changes `κ × ι`, used by `Matrix.comp`, to `ι × κ`,
used by `Matrix.blockDiagonal`. -/
theorem det_comp_diagonal_const
    (A : Matrix ι ι R) :
    (Matrix.comp κ κ ι ι R
      (Matrix.diagonal fun _ : κ => A)).det =
      A.det ^ Fintype.card κ := by
  classical
  let M : Matrix (κ × ι) (κ × ι) R :=
    Matrix.comp κ κ ι ι R
      (Matrix.diagonal fun _ : κ => A)
  let e : κ × ι ≃ ι × κ := Equiv.prodComm κ ι
  change M.det = A.det ^ Fintype.card κ
  have hM :
      Matrix.reindex e e M =
        Matrix.blockDiagonal (fun _ : κ => A) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l <;>
      simp [M, e, Matrix.reindex_apply, Matrix.comp_apply,
        Matrix.blockDiagonal_apply, hkl]
  calc
    M.det = (Matrix.reindex e e M).det :=
      (Matrix.det_reindex_self e M).symm
    _ = (Matrix.blockDiagonal (fun _ : κ => A)).det := by
      rw [hM]
    _ = A.det ^ Fintype.card κ := by
      rw [Matrix.det_blockDiagonal]
      simp
/-- Exact trace-matrix factorization for the `κ × ι` ordering of a tower
basis. -/
theorem traceMatrix_smulTower'_eq
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.traceMatrix R (b.smulTower' c) =
      Matrix.comp κ κ ι ι R
          (Matrix.diagonal
            (fun _ : κ => Algebra.traceMatrix R b)) *
        Matrix.comp κ κ ι ι R
          ((Algebra.traceMatrix S c).map
            (Algebra.leftMulMatrix b)) := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  change
    Algebra.trace R T
        ((b.smulTower' c) (k, i) *
          (b.smulTower' c) (l, j)) = _
  rw [Basis.smulTower'_apply, Basis.smulTower'_apply]
  rw [← Algebra.trace_trace_of_basis b c]

  have hprod :
      (b i • c k) * (b j • c l) =
        (b i * b j) • (c k * c l) := by
    simp only [Algebra.smul_def, map_mul]
    ring

  have hrel :
      Algebra.trace S T ((b i • c k) * (b j • c l)) =
        (b i * b j) * Algebra.trace S T (c k * c l) := by
    calc
      Algebra.trace S T ((b i • c k) * (b j • c l)) =
          Algebra.trace S T ((b i * b j) • (c k * c l)) := by
            rw [hprod]
      _ = (b i * b j) • Algebra.trace S T (c k * c l) :=
        (Algebra.trace S T).map_smul
          (b i * b j) (c k * c l)
      _ = (b i * b j) * Algebra.trace S T (c k * c l) := by
        simp

  rw [hrel]
  simp only [Matrix.mul_apply, Matrix.comp_apply,
    Matrix.map_apply, Matrix.diagonal_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  rw [Fintype.sum_eq_single k]
  · simp only [if_pos]
    have hmul := congrFun
      (Algebra.traceMatrix_of_basis_mulVec b
        (Algebra.trace S T (c k * c l) * b j)) i
    simpa [Matrix.mulVec, dotProduct,
      Algebra.leftMulMatrix_eq_repr_mul,
      Basis.equivFun_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_assoc, mul_comm,
      mul_left_comm] using hmul.symm
  · intro k' hk'
    simp [hk'.symm]
/-- Tower-discriminant formula in the `κ × ι` ordering used internally by
the block matrices. -/
theorem discr_smulTower'
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.discr R (b.smulTower' c) =
      Algebra.discr R b ^ Fintype.card κ *
        Algebra.norm R (Algebra.discr S c) := by
  classical
  change
    (Algebra.traceMatrix R (b.smulTower' c)).det =
      (Algebra.traceMatrix R b).det ^ Fintype.card κ *
        Algebra.norm R (Algebra.traceMatrix S c).det
  rw [traceMatrix_smulTower'_eq b c, Matrix.det_mul,
    det_comp_diagonal_const]
  have hdet :
      (Matrix.comp κ κ ι ι R
        ((Algebra.traceMatrix S c).map
          (Algebra.leftMulMatrix b))).det =
        (Algebra.leftMulMatrix b
          (Algebra.traceMatrix S c).det).det := by
    simpa using
      (Matrix.det_det
        (M := Algebra.traceMatrix S c)
        (Algebra.leftMulMatrix b).toRingHom).symm
  rw [hdet, ← Algebra.norm_eq_matrix_det b
    (Algebra.traceMatrix S c).det]
/-- Discriminant of the standard `ι × κ` tower basis. -/
theorem discr_smulTower
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.discr R (b.smulTower c) =
      Algebra.discr R b ^ Fintype.card κ *
        Algebra.norm R (Algebra.discr S c) := by
  classical
  calc
    Algebra.discr R (b.smulTower c) =
        Algebra.discr R (b.smulTower' c) := by
      symm
      simpa [Basis.smulTower'] using
        (Algebra.discr_reindex R
          (b.smulTower c) (Equiv.prodComm ι κ))
    _ = Algebra.discr R b ^ Fintype.card κ *
          Algebra.norm R (Algebra.discr S c) :=
      discr_smulTower' b c
end
end MazurProof.TowerDiscriminant
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity =====
section
/-!
# Simple-root parity for normalized N13 Kummer values

This file maps the primitive global Mumford polynomial and its homogeneous
curve relation into the integer ring of a height-one completion.  Away from
the different, the sextic secant is a unit.  Hence whenever the quadratic
Mumford polynomial has a simple root modulo the prime, its normalized
Kummer value has even multiplicity.

The denominator-clearing scale is not inverted in the integer ring.  It is
absorbed into the square root only after passing to the completion field,
so no denominator prime is excluded.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
abbrev O : Type :=
  N13GlobalKummerIdealSquare.O
end
end MazurProof.N13GlobalKummerSimpleRootParity
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot =====
section
/-!
# The quadratic-algebra double-root principle

The leading-unit double-root branch is controlled by the rank-two algebra
cut out by the Mumford quadratic.  Its distinguished root makes the
quadratic value a norm.  At a double root, the trace and norm of the
correction term are both small, so the smooth-curve secant remains a unit.
Taking norms in the Mumford relation then writes the original quadratic
value as a unit times a square.

This argument is uniform in the prime and absorbs every nonzero
denominator-clearing scale into a fourth power.  It does not enumerate
primes, residue-field elements, or squareclasses.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
namespace MazurProof.N13QuadraticAlgebraDoubleRoot
noncomputable section
open N13GoodPrimeSimpleRoot
abbrev QA
    (R : Type*) [CommRing R]
    (B C : R) :=
  QuadraticAlgebra R (-C) (-B)
def delta
    {R : Type*} [CommRing R]
    {B C : R} (x : R) : QA R B C :=
  QuadraticAlgebra.omega -
    algebraMap R (QA R B C) x
def qtrace
    {R : Type*} [CommRing R]
    {B C : R} (z : QA R B C) : R :=
  2 * z.re - B * z.im
end
end MazurProof.N13QuadraticAlgebraDoubleRoot
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerAwayDifferentParity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerAwayDifferentParity =====
section
/-!
# Uniform N13 parity away from the different

The simple- and double-root principles together cover every primitive
quadratic at every height-one prime where the sextic is étale.  No
condition is imposed on the denominator-clearing scale.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerAwayDifferentParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
open N13GlobalKummerSimpleRootParity
open N13QuadraticAlgebraDoubleRoot
abbrev O : Type :=
  N13GlobalKummerSimpleRootParity.O
end
end MazurProof.N13GlobalKummerAwayDifferentParity
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianClassNumberOne =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianClassNumberOne =====
section
/-!
# Class number one for the N13 number field

The field is a totally complex sextic of discriminant `-10816`, so its
Minkowski bound is strictly below four.  Prime ideals of norms two and
three are excluded by reducing the integral sextic satisfied by
`θ = α + 9`; the finite-field arguments use Frobenius, not enumeration.
-/
open Algebra Module Polynomial Nat
open scoped nonZeroDivisors Real
namespace MazurProof.N13GaussianClassNumberOne
noncomputable section
open N13GaussianGlobalArithmetic
/-- Uniform interface for excluding roots over a field of prescribed size. -/
def NoRootAtCard (q : ℕ) : Prop :=
  ∀ {k : Type} [Field k] [Fintype k],
    Fintype.card k = q →
      ∀ x : k,
        eval₂ (Int.castRingHom k) x
          N13SexticIrreducible.fInt ≠ 0
/-- The N13 sextic has no root over any field with two elements. -/
theorem fInt_noRoot_card_two :
    NoRootAtCard 2 := by
  intro k _ _ hcard x hroot
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP k 2 := charP_of_card_eq_prime hcard
  have hx2 : x ^ 2 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hxpow := pow_pos_eq_self_of_sq_eq_self hx2
  have htwo : (2 : k) = 0 :=
    CharP.cast_eq_zero k 2
  have hfour : (4 : k) = 0 := by
    linear_combination 2 * htwo
  have hsix : (6 : k) = 0 := by
    linear_combination 3 * htwo
  have heval :
      x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 +
          2 * x ^ 3 + x ^ 2 + 2 * x + 1 = 0 := by
    simpa [N13SexticIrreducible.fInt] using hroot
  rw [hxpow 5, hxpow 4, hxpow 3,
    hxpow 2, hxpow 1] at heval
  rw [htwo, hfour, hsix] at heval
  have hone : (1 : k) = 0 := by
    linear_combination heval - x * htwo
  exact one_ne_zero hone
/-- The N13 sextic has no root over any field with three elements. -/
theorem fInt_noRoot_card_three :
    NoRootAtCard 3 := by
  intro k _ _ hcard x hroot
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CharP k 3 := charP_of_card_eq_prime hcard
  have hx3 : x ^ 3 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hx6 : x ^ 6 = x ^ 2 := by
    calc
      x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = x ^ 2 := by rw [hx3]
  have hx5 : x ^ 5 = x := by
    calc
      x ^ 5 = x ^ 3 * x ^ 2 := by ring
      _ = x * x ^ 2 := by rw [hx3]
      _ = x ^ 3 := by ring
      _ = x := hx3
  have hthree : (3 : k) = 0 :=
    CharP.cast_eq_zero k 3
  have hfour : (4 : k) = 1 := by
    linear_combination hthree
  have hsix : (6 : k) = 0 := by
    linear_combination 2 * hthree
  have heval :
      x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 +
          2 * x ^ 3 + x ^ 2 + 2 * x + 1 = 0 := by
    simpa [N13SexticIrreducible.fInt] using hroot
  rw [hx6, hx5, hx3] at heval
  by_cases hx0 : x = 0
  · subst x
    norm_num at heval
  · have hx2 : x ^ 2 = 1 := by
      simpa [hcard] using
        FiniteField.pow_card_sub_one_eq_one x hx0
    rw [hx2] at heval
    rw [hfour, hsix] at heval
    have htwox : (2 : k) * x = 0 := by
      linear_combination heval - hthree - x * hthree
    have htwo_ne : (2 : k) ≠ 0 := by
      intro htwo
      have hdiv : 3 ∣ 2 :=
        (CharP.cast_eq_zero_iff k 3 2).mp htwo
      norm_num at hdiv
    exact hx0 ((mul_eq_zero.mp htwox).resolve_left htwo_ne)
/-! ## Minkowski's bound -/
/-! ## Excluding small prime ideals -/
end
end MazurProof.N13GaussianClassNumberOne
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerPID =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerPID =====
section
/-!
# Class-number-one endpoint for normalized N13 Kummer ideals

The structural class-number-one theorem supplies the sole global
principality input in the good-locus ideal-square theorem.  Consequently
every normalized N13 Kummer value becomes a unit times a square after
removing its denominator scale and the different.
-/
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
theorem isIntegralElem_int_of
    {A : Type*} [Ring A]
    {f g : ℤ →+* A} {x : A}
    (hx : f.IsIntegralElem x) :
    g.IsIntegralElem x := by
  have hfg : g = f :=
    RingHom.ext_int _ _
  rwa [hfg]
end
end MazurProof.N13GlobalKummerPID
end

end

-- ===== FLT.Assumptions.MazurProof.EvenPrincipalIdeal =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.EvenPrincipalIdeal =====
section
/-!
# Even height-one counts in a Dedekind PID

If every prime-ideal exponent of a nonzero principal ideal is even, halve
the ideal factorization itself.  This gives a literal square ideal, rather
than merely a class-group equality.  Principality of its square root then
recovers the original generator as a unit times a square.

The construction is structural: it uses the factorization Finsupp of an
ideal and never enumerates height-one primes or chooses prime elements.
-/
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.EvenPrincipalIdeal
/-! ## Halving a factorization -/
/-! ## From fractional-ideal counts to the integral ideal factorization -/
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
/-- The height-one count of the principal fractional ideal generated by an
integral element. -/
noncomputable def principalCount
    (P : HeightOneSpectrum O) (x : O) : ℤ :=
  FractionalIdeal.count L P
    (FractionalIdeal.spanSingleton O⁰ (algebraMap O L x))
/-! ## Unit times square -/
variable [IsPrincipalIdealRing O]
end MazurProof.EvenPrincipalIdeal
end
end

end

-- ===== FLT.Assumptions.MazurProof.RamifiedDlog =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.RamifiedDlog =====
section
/-!
# The first ramified logarithm

For a field `k`, the units of the dual-number ring
`k[ε] = k ⊕ εk`, `ε² = 0`, have a canonical first-order logarithm

`a + εb ↦ b / a`.

It is additive under multiplication.  In characteristic two it kills
squares, as well as constant units.  This is the structural finite quotient
used by the local N13 fake-descent calculation at two.
-/
namespace MazurProof.RamifiedDlog
open TrivSqZeroExt
noncomputable section
variable {k : Type*} [Field k]
local instance dualNumberUnitsIsMulCommutative :
    IsMulCommutative (DualNumber k)ˣ :=
  IsMulCommutative.of_comm fun a b => by
    apply Units.ext
    exact mul_comm (a : DualNumber k) (b : DualNumber k)
/-- The first ramified logarithm on a dual-number unit. -/
def dlog (z : (DualNumber k)ˣ) : k :=
  snd (z : DualNumber k) / fst (z : DualNumber k)
@[simp] theorem dlog_one : dlog (1 : (DualNumber k)ˣ) = 0 := by
  simp [dlog]
/-- Package `a + εb` as a unit when its residue `a` is nonzero. -/
def unitOf (a b : k) (ha : a ≠ 0) : (DualNumber k)ˣ :=
  ((isUnit_iff_isUnit_fst (x := ((a, b) : DualNumber k))).2
    (isUnit_iff_ne_zero.mpr ha)).unit
end
end MazurProof.RamifiedDlog
end

end

-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
/-!
# The first ramified local character for N13 at two

Let `π = 1 - i`.  The first ramified quotient of the unramified cubic
extension of `ℚ₂(i)` is the dual-number ring

`𝔽₈[ε] / (ε²)`, where `𝔽₈ = 𝔽₂[α] / (α³ + α + 1)`.

This file formalizes the finite algebra in that quotient.  The logarithm
`a + εb ↦ b / a`, including its descent through squares and scalar units,
is supplied by `RamifiedDlog`.  Here we calculate the four N13 generator
jets and prove structurally that vanishing of the resulting `𝔽₈` character
leaves exactly the two candidates `(0, 0, s, s)`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
/-! ## The residue field -/
/-! ## The four generator jets -/
/--
The first-order reduction of `ζ = i`, under `i ↦ 1 + ε`.
-/
def zetaJet : JetUnit :=
  RamifiedDlog.unitOf 1 1 one_ne_zero
/--
The first-order reduction of
`e₁ = 1 - θ² + (i - 1)θ`.
-/
def e1Jet : JetUnit :=
  RamifiedDlog.unitOf (alpha ^ 2 + 1) alpha
    alpha_sq_add_one_ne_zero
/--
The first-order reduction of
`e₂ = 1 + iθ² + (1 + 2i)θ`.
-/
def e2Jet : JetUnit :=
  RamifiedDlog.unitOf
    (alpha ^ 2 + alpha + 1) (alpha ^ 2)
    alpha_sq_add_alpha_add_one_ne_zero
/-! ## Structural collapse of the candidate space -/
/--
The logarithm of the candidate
`ζⁱ e₁ʲ e₂ᵏ (aq)ˢ`, collected in the basis `1, α, α²`.
-/
def candidateDlog (i j k s : ZMod 2) : F8 :=
  (i : F8) + ((k + s : ZMod 2) : F8) * alpha +
    ((j + k + s : ZMod 2) : F8) * alpha ^ 2
end
end MazurProof.N13LocalDlogTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13LocalDlogRegimes =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalDlogRegimes =====
section
/-!
# The two local first-jet regimes for N13 at two

This file connects the finite first-jet calculation in
`N13LocalDlogTwo` to the two valuation regimes for a `2`-adic affine
coordinate.

For an integral coordinate, reduction gives

`x - θ ↦ x̄ - α`,

a constant unit of the dual-number ring.  For a nonintegral coordinate,
putting `t = x⁻¹` and removing the rational scalar `x` gives

`1 - t θ ↦ 1`,

because positive `2`-adic valuation forces `t̄ = 0`.  Both jets therefore
have zero first ramified logarithm.  No local square-class enumeration is
used.

Proof boundary: this file proves the two coordinate-jet calculations and
their `ℚ₂` residue adapters.  It does not yet construct the map from the
actual completed sextic order modulo its prime square, nor identify a
Mumford/Jacobian Kummer value with one of these coordinate jets.  That
fixed local-order compatibility is isolated in
`scratch/N13_Q2_ADAPTER.md`.
-/
open scoped CharTwo
namespace MazurProof.N13LocalDlogRegimes
open N13LocalDlogTwo
open TrivSqZeroExt
noncomputable section
/-! ## Exact dual-number semantics -/
/-! ## `ℚ₂` and `ℤ₂` adapters -/
/-- Reduction of a `2`-adic integer into constant dual numbers. -/
def padicScalarDualHom : Z2 →+* DualNumber F8 :=
  (algebraMap F8 (DualNumber F8)).comp
    ((algebraMap (ZMod 2) F8).comp PadicInt.toZMod)
/-- If `x` is nonintegral, its inverse is a `2`-adic integer. -/
def inverseIntegralPart (x : Q2) (hx : x.valuation < 0) : Z2 :=
  ⟨x⁻¹, (Padic.norm_le_one_iff_val_nonneg x⁻¹).2 (by
    rw [Padic.valuation_inv]
    omega)⟩
theorem inverseIntegralPart_ne_zero
    (x : Q2) (hx : x.valuation < 0) :
    inverseIntegralPart x hx ≠ 0 := by
  apply PadicInt.coe_ne_zero.mp
  simp only [inverseIntegralPart, Subtype.coe_mk]
  intro h
  have hx0 : x = 0 := inv_eq_zero.mp h
  rw [hx0, Padic.valuation_zero] at hx
  omega
theorem inverseIntegralPart_valuation_pos
    (x : Q2) (hx : x.valuation < 0) :
    0 < (inverseIntegralPart x hx).valuation := by
  have hval :
      ((inverseIntegralPart x hx).valuation : ℤ) = -x.valuation := by
    rw [← PadicInt.valuation_coe]
    exact Padic.valuation_inv x
  omega
/-- Positive valuation of `x⁻¹` forces zero residue modulo `2`. -/
theorem inverseIntegralPart_residue_eq_zero
    (x : Q2) (hx : x.valuation < 0) :
    PadicInt.toZMod (inverseIntegralPart x hx) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  have hmem :=
    (PadicInt.mem_span_pow_iff_le_valuation
      (p := 2) (inverseIntegralPart x hx)
      (inverseIntegralPart_ne_zero x hx) 1).2 (by
        have hv := inverseIntegralPart_valuation_pos x hx
        omega)
  simpa only [pow_one, Ideal.mem_span_singleton] using hmem
end
end MazurProof.N13LocalDlogRegimes
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
/-!
# The fixed Gaussian order at two for N13

This file constructs the first ramified quotient directly from the
Gaussian cubic presentation.  We first adjoin a root `i` of `T² + 1`
over `ℤ₂`, and then a root `θ` of

`T³ + 2T² - T - 1 - i(2T(T+1))`.

Sending `i` to `1 + ε` and `θ` to the cubic residue `α` defines a
surjective ring homomorphism to `𝔽₈[ε]/(ε²)`.  Its kernel is proved to
be exactly `(1-i)² = (2)` by the two nested monic power bases.  Hence the
ramified-prime-square quotient is identified with the dual-number ring.
This is the direct quotient-ring core needed by the local N13 descent;
no ray-class enumeration is involved.

The remaining arithmetic identification with the completed maximal
order is recorded separately in `scratch/N13_GAUSSIAN_ORDER_TWO.md`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13GaussianOrderTwo
noncomputable section
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module
/-! ## The integral Gaussian cubic order -/
/-- The Gaussian quadratic polynomial over `ℤ₂`. -/
def gaussianPolynomial : Z2[X] :=
  X ^ 2 + 1
/-- The Gaussian `ℤ₂`-order. -/
abbrev GaussianOrder : Type :=
  AdjoinRoot gaussianPolynomial
instance gaussianOrderNontrivial : Nontrivial GaussianOrder :=
  AdjoinRoot.nontrivial (f := gaussianPolynomial) (by
    have hdeg : gaussianPolynomial.degree = 2 := by
      unfold gaussianPolynomial
      compute_degree!
    rw [hdeg]
    norm_num)
/-- The integral Gaussian generator. -/
def gaussianI : GaussianOrder :=
  AdjoinRoot.root gaussianPolynomial
/-- The cubic factor of the N13 sextic over the Gaussian order. -/
def cubicPolynomial : GaussianOrder[X] :=
  X ^ 3 + 2 * X ^ 2 - X - 1 -
    C gaussianI * (2 * X * (X + 1))
/-- The fixed integral Gaussian cubic order used at the prime over two. -/
abbrev Order : Type :=
  AdjoinRoot cubicPolynomial
/-- The Gaussian generator inside the cubic order. -/
def i : Order :=
  AdjoinRoot.of cubicPolynomial gaussianI
/-! ## The two nested power bases -/
/-! ## Direct reduction to the dual-number ring -/
/-- Reduction of Gaussian `ℤ₂` to the first ramified jet. -/
def gaussianReduction : GaussianOrder →+* DualNumber F8 :=
  AdjoinRoot.lift padicScalarDualHom gaussianIDual (by
    simp only [gaussianPolynomial, eval₂_add, eval₂_X_pow,
      eval₂_one]
    rw [gaussianIDual_sq]
    exact neg_add_cancel 1)
@[simp] theorem gaussianReduction_i :
    gaussianReduction gaussianI = gaussianIDual := by
  exact AdjoinRoot.lift_root _
/-- The fixed first-jet reduction of the Gaussian cubic order. -/
def reduction : Order →+* DualNumber F8 :=
  AdjoinRoot.lift gaussianReduction thetaDual (by
    simpa [cubicPolynomial] using gaussian_cubic_jet_relation)
/-! ## Exactness of the first-jet quotient -/
/-! ## Compatibility with the N13 descent generators -/
/-! ## The ramified prime square -/
/-! ## Structural surjectivity -/
end
end MazurProof.N13GaussianOrderTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo =====
section
/-!
# Global N13 integers in the first ramified quotient at two

The relative maximal order is monogenic over the Gaussian integers.  Its
power-basis universal property therefore maps the full global maximal order
to the fixed integral Gaussian order used at two:

* the Gaussian generator maps to the local generator `i`;
* the translated cubic generator maps to `theta - 9`.

Composing with the exact quotient map gives a genuine ring homomorphism from
the full ring of integers to `F₈[ε]/(ε²)`.  Thus later logarithmic detectors
act on every global unit, rather than only on a displayed list of elements.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraGI
abbrev Order := N13GaussianOrderTwo.Order
end
end MazurProof.N13GaussianGlobalReductionTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses =====
section
/-!
# Unit squareclasses in the N13 field

Dirichlet's theorem decomposes the unit group as finite cyclic torsion
times a free abelian group of rank two.  Squaring has index two on the
torsion factor and index `2^2` on the free factor, so the N13 unit
squareclass group has exactly eight elements.  No units are enumerated.
-/
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
end MazurProof.UnitSquareClass
namespace NumberField.Units
variable (K : Type*) [Field K] [NumberField K]
noncomputable def dirichletCoordinatesHom :
    torsion K ×
        Multiplicative (Fin (rank K) → ℤ) →*
      (NumberField.RingOfIntegers K)ˣ where
  toFun z :=
    (z.1 : (NumberField.RingOfIntegers K)ˣ) *
      ∏ i, (fundSystem K i) ^ (z.2.toAdd i)
  map_one' := by
    simp
  map_mul' := by
    rintro ⟨ζ, a⟩ ⟨ξ, b⟩
    change
      ((ζ : (NumberField.RingOfIntegers K)ˣ) *
          (ξ : (NumberField.RingOfIntegers K)ˣ)) *
          ∏ i, (fundSystem K i) ^
            (a.toAdd i + b.toAdd i) =
        ((ζ : (NumberField.RingOfIntegers K)ˣ) *
            ∏ i, (fundSystem K i) ^
              (a.toAdd i)) *
          ((ξ : (NumberField.RingOfIntegers K)ˣ) *
            ∏ i, (fundSystem K i) ^
              (b.toAdd i))
    simp_rw [zpow_add, Finset.prod_mul_distrib]
    ac_rfl
end NumberField.Units
namespace MazurProof.N13GaussianUnitSquareclasses
end MazurProof.N13GaussianUnitSquareclasses
end
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses =====
section
/-!
# Named unit squareclasses in the N13 field

The three displayed N13 units are literal units of the maximal order.  Their
first ramified logarithms are `1`, `α²`, and `α + α²`, hence they are
independent modulo squares.  Dirichlet's theorem gives exactly eight unit
squareclasses, so these three classes form a basis and every maximal-order
unit is their binary product times a square.

The proof uses the genuine global reduction homomorphism from
`N13GaussianGlobalReductionTwo`; no field-unit surrogate or enumeration of
the eight classes is used.
-/
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraGI
/-! ## Literal units of the relative and absolute maximal orders -/
/-! ## The global first-jet logarithm -/
/-! ## Structural generation of all unit squareclasses -/
/-- Three binary exponents, kept as a product so no class is enumerated. -/
abbrev Exp3 := F2 × F2 × F2
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNormalizationOrderTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNormalizationOrderTransport =====
section
/-!
# Transport from the N13 normalization order

The global Kummer normalization and the structural class-number computation
use definitionally different presentations of the same integral closure.
This file crosses that seam once through the compiled ring equivalence, then
transports a unit-times-square identity to the sextic presentation.

When every principal count is even there is no exceptional prime carrier.
Consequently the fourth candidate coordinate is literally zero.
-/
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
abbrev Oi : Type := N13GlobalKummerIdealSquare.O
local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField
end
end MazurProof.N13GaussianNormalizationOrderTransport
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianLocalization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianLocalization =====
section
/-!
# The global N13 sextic algebra inside the local Gaussian order

The fixed Gaussian cubic order is an integral presentation over `ℤ₂`.
After inverting `2`, its two generators satisfy the global sextic
presentation over `ℚ`.  This gives a structural specialization map from the
global sextic algebra to the localized order.

The construction deliberately stops before reduction modulo `2`: reduction
does not extend across an inverted `2`.  Instead, later lemmas identify the
global descent generators with integral elements of the order, which may then
be reduced by `N13GaussianOrderTwo.reduction`.
-/
open Polynomial
namespace MazurProof.N13GaussianLocalization
noncomputable section
open N13GaussianOrderTwo
abbrev Order : Type :=
  N13GaussianOrderTwo.Order
/-! ## Integral images of the global descent generators -/
end
end MazurProof.N13GaussianLocalization
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianCandidateDlog =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianCandidateDlog =====
section
/-!
# Integral first jets of the N13 global candidates

The global candidate generators specialize to short integral elements of
the fixed Gaussian order.  Their reduction is therefore computed by the
exact quotient map of `N13GaussianOrderTwo`, rather than by assigning jets
formally.

This file proves that the first logarithm of that genuine integral reduction
is exactly `N13LocalDlogTwo.candidateDlog`.
-/
namespace MazurProof.N13GaussianCandidateDlog
noncomputable section
open N13LocalDlogTwo
open N13GaussianOrderTwo
open N13GaussianLocalization
abbrev Order : Type :=
  N13GaussianOrderTwo.Order
end
end MazurProof.N13GaussianCandidateDlog
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianLowDegree =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianLowDegree =====
section
/-!
# Low-degree polynomial jets in the N13 Gaussian order

Every integral polynomial in `θ` reduces to a constant dual number: the
coefficients have no infinitesimal part and `θ` reduces to `α`.  If its
coefficient reduction is nonzero of degree at most two, evaluation at
`α` cannot vanish because the residue polynomial of `α` has degree three.

This treats split and nonsplit degree-two support uniformly.  It is a
statement about the explicit Gaussian order and its first quotient; the
global-to-completion and genuine local Kummer comparisons remain separate.
-/
open Polynomial
namespace MazurProof.N13GaussianLowDegree
noncomputable section
open N13GaussianOrderTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
abbrev Order : Type := N13GaussianOrderTwo.Order
/-- Coefficientwise reduction of a `2`-adic integral polynomial. -/
def residuePolynomial (U : Z2[X]) : (ZMod 2)[X] :=
  U.map PadicInt.toZMod
/-- Evaluation of the reduced polynomial at the cubic residue generator. -/
def residueEval (U : Z2[X]) : F8 :=
  AdjoinRoot.mk residueCubic (residuePolynomial U)
/-- A nonzero polynomial of degree below three cannot vanish at `α`. -/
theorem residueEval_ne_zero
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    residueEval U ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
    residueCubic_monic hne
  rw [residueCubic_natDegree]
  omega
/-- The constant first jet, packaged as a dual-number unit. -/
def lowDegreeJet
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    (DualNumber F8)ˣ :=
  RamifiedDlog.unitOf
    (residueEval U) 0
    (residueEval_ne_zero U hne hdeg)
end
end MazurProof.N13GaussianLowDegree
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordAbelJacobi =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordAbelJacobi =====
section
/-!
# The N13 Abel--Jacobi embedding in oriented Mumford coordinates

The chosen positive infinity is the base point.  A curve point is first sent
to its balanced Mumford representative and then to its oriented Picard class.
-/
namespace MazurProof.N13MumfordAbelJacobi
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
abbrev ConcretePic : Type u :=
  SexticMumford.ConcretePic (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)
def abelJacobi :
    SexticMumford.CurvePoint (N13Mumford.model K) → ConcretePic K :=
  fun P => SexticMumford.classOf (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)
    (SexticMumford.pointMumford (N13Mumford.model K) P)
def cuspAbelJacobi : Cusp13 → ConcretePic ℚ :=
  (abelJacobi ℚ).comp cuspPoint
end
end MazurProof.N13MumfordAbelJacobi
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityHalf =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityHalf =====
section
/-!
# A half of the infinity-difference class on the N13 sextic

The Gaussian factorization `f = A² + B²` supplies a balanced Mumford pair
`u = X(X+1)`, `v = -(2X+1)` and the function `g = Y-A`.  We prove

`(u, Y-v)² = (g)` and `ord_{∞₊}(g) = -1`.

The corresponding oriented Picard identity says that this Mumford class
doubles to the difference of the two points at infinity.  This removes the
extra even-degree ambiguity in the fake 2-Kummer kernel.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13InfinityHalf
noncomputable section
open SexticMumford
def halfA2Factor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) (C ((4 : ℚ)⁻¹))
def halfABFactor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (halfU + N13GaussianFactorization.A *
      (C ((4 : ℚ)⁻¹) * (X + 1)))
    (C ((4 : ℚ)⁻¹) * (X + 1))
def halfB2Q : ℚ[X] :=
  C ((4 : ℚ)⁻¹) * (4 + (X + 1) ^ 2)
def halfB2Factor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (-2 * halfV + N13GaussianFactorization.A * halfB2Q)
    halfB2Q
def backP : ℚ[X] :=
  -(C ((2 : ℚ)⁻¹) *
    (2 * X ^ 3 + 5 * X ^ 2 + 4 * X - 3))
def backR : ℚ[X] := X + C ((2 : ℚ)⁻¹)
end
end MazurProof.N13InfinityHalf
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicEndgame =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicEndgame =====
section
/-!
# The N13 two-adic endgame without Mordell--Weil finite generation

A trivial fake two-descent says that multiplication by two on `J(ℚ)` is
surjective.  For the actual finite image quotient of reduction, doubling is
then bijective.  Compatible halves of a kernel element stay in the kernel, so
a separated two-adic filtration already forces reduction to be injective.

The older exponent-nineteen route is retained below as a stronger optional
conclusion.  All arithmetic inputs remain explicit hypotheses: fake-descent
soundness, the reduction map, and the formal filtration.
-/
namespace MazurProof.N13TwoAdicEndgame
noncomputable section
open N18RouteC.Separated
namespace FormalKernelData
variable {K : Type*} [AddCommGroup K]
end FormalKernelData
/-- The exact group-theoretic output of a trivial fake two-descent. -/
def TwoSurjective (G : Type*) [AddCommGroup G] : Prop :=
  ∀ P : G, ∃ Q : G, P = 2 • Q
end
end MazurProof.N13TwoAdicEndgame
end

end

-- ===== FLT.Assumptions.MazurProof.N13KummerKernelAssembly =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KummerKernelAssembly =====
section
/-!
# Removing the even-sextic infinity ambiguity from the N13 Kummer kernel

The generic fake-Kummer kernel theorem for an even sextic has two branches:
a class is either a double, or a double plus the difference of the two
points at infinity.  For N13 the latter class is itself a double, by the
explicit half-class constructed in `N13InfinityHalf`.

This file records the exact group-theoretic assembly.  Its only remaining
input is the genuine generic Kummer-kernel theorem; no finiteness or
representative enumeration occurs here.
-/
namespace MazurProof.N13KummerKernelAssembly
noncomputable section
abbrev O :=
  N13Infinity.positiveInfinityOrder ℚ
abbrev G : Type :=
  SexticMumford.ConcretePic M O
def infinityClass : G :=
  SexticMumford.classOf M O
    (SexticMumford.infinityMinusMumford M)
def infinityHalfClass : G :=
  SexticMumford.classOf M O N13InfinityHalf.infinityHalf
end
end MazurProof.N13KummerKernelAssembly
end

end

-- ===== FLT.Assumptions.MazurProof.N13FakeDescentAssembly =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FakeDescentAssembly =====
section
/-!
# Assembly of the structural N13 fake descent

The finite algebra is already complete: a candidate whose first ramified
logarithm vanishes has trivial fake square class.  This file isolates the two
semantic arithmetic inputs needed to apply that calculation to the genuine
Jacobian Kummer map:

1. every global Kummer value has a representative in the four-generator
   candidate envelope;
2. the representative attached to a rational Jacobian class has vanishing
   first local logarithm at two.

No candidate enumeration, Mordell--Weil generators, or finiteness hypothesis
is used in the assembly.
-/
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
abbrev G : Type :=
  N13KummerKernelAssembly.G
abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget
/-! ## The unconditional structural Kummer map -/
end
end MazurProof.N13FakeDescentAssembly
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog =====
section
/-!
# Global zero-carrier classes and the first ramified logarithm

The global factorization of a normalized N13 Kummer integer is an exact
identity

`x = ε * y²`

in the maximal order.  The same maximal order has an honest reduction to the
first ramified quotient at two.  Reducing the identity therefore shows that
the logarithm of `ε` vanishes: the square contributes twice its logarithm,
while `x` is the evaluation of a primitive polynomial of degree at most two
and hence has a constant nonzero first jet.

This aligns the global named-unit coordinates with the local logarithm
without a valuation case split or a finite candidate search.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
abbrev Oi := N13GlobalKummerIdealSquare.O
abbrev Order := N13GaussianOrderTwo.Order
/-! ## The global integral evaluation in the explicit order -/
/-! ## The same named-unit word globally and locally -/
/-! ## Group-level capstone -/
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerHom =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerHom =====
section
/-!
# The N13 fake-Kummer homomorphism from balanced representatives

Principal-ideal invariance and its three-ideal multiplicativity theorem allow
the raw value `u(θ)` to descend to the oriented Picard group.  Only existence
of balanced representatives is needed: a noncomputable section of `classOf`
may be chosen, and the principal-relation theorems prove that the resulting
map is independent of this choice and additive.

In particular, uniqueness of Mumford normal forms and a transported group law
on the representation type are not prerequisites for the Kummer map.
-/
namespace MazurProof.N13MumfordKummerHom
noncomputable section
open SexticMumford
abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ
abbrev G : Type :=
  SexticMumford.ConcretePic M O
abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget
end
end MazurProof.N13MumfordKummerHom
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward =====
section
/-!
# The forward N13 fake-Kummer kernel inclusions

The actual fake-Kummer homomorphism has an exponent-two target, so it kills
every double.  The even-sextic infinity class is represented by the balanced
Mumford datum with `u = 1`; its raw value `u(θ)` is therefore one, so that
class is killed as well.

These are only the forward inclusions in the standard even-sextic kernel
description.  No converse half-divisor theorem is assumed here.
-/
namespace MazurProof.N13MumfordKummerKernelForward
noncomputable section
open SexticMumford
abbrev G : Type :=
  N13MumfordKummerHom.G
abbrev infinityClass : G :=
  N13KummerKernelAssembly.infinityClass
/-! ## Unconditional low-degree Kummer homomorphism -/
end
end MazurProof.N13MumfordKummerKernelForward
end

end

-- ===== FLT.Assumptions.MazurProof.N13FullNormPairGaussian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FullNormPairGaussian =====
section
/-!
# The N13 full norm-pair sign is gauge-trivial

The N13 sextic field is a cubic extension of the Gaussian field, so it
contains a unit `i` with

`i² = -1`,  `Norm(i) = 1`.

Consequently the square/norm gauge at `i`, multiplied by the scalar/cubic
gauge at `-1`, is exactly the sign pair `(1,-1)`.  Thus the distinguished
sign class in the full norm-pair target is already trivial for N13.

This is a field-structure argument.  It uses neither divisor enumeration
nor a finite square-class certificate.
-/
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField
end
end MazurProof.N13FullNormPairGaussian
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordOrientedFullKummer =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordOrientedFullKummer =====
section
/-!
# The oriented full N13 Mumford Kummer value

The raw norm pair `(u(θ), Res(u,v))` forgets the integer recording the two
points at infinity.  For an even sextic the missing coordinate is exactly

`(-1) ^ (n∞ - 1)`.

The shift by one is forced by the oriented Picard convention: the identity
Mumford datum has `n∞ = 1`, whereas the difference of the two infinity
points has `n∞ = 0`.  Thus the identity gives the trivial full class and the
infinity difference gives the unique possible sign class.

This file identifies that orientation bit before attempting to descend the
full value through principal relations.  No Cantor inverse, divisor
enumeration, or finite certificate is used.
-/
namespace MazurProof.N13MumfordOrientedFullKummer
noncomputable section
/-- The sign missing from the affine resultant norm root. -/
def orientationSignUnit (D : LowRep) : ℚˣ :=
  (-1 : ℚˣ) ^ orientationExponent D
@[simp] theorem orientationSignUnit_sq (D : LowRep) :
    orientationSignUnit D ^ 2 = 1 := by
  have heven :
      Even (orientationExponent D * (2 : ℤ)) :=
    ⟨orientationExponent D, by ring⟩
  rw [orientationSignUnit, ← zpow_natCast, ← zpow_mul]
  exact heven.neg_one_zpow
/-! ## The two oriented base classes -/
/-! ## The full lift of the actual structural Kummer map -/
abbrev G : Type :=
  N13LowDegreeKummerHom.G
abbrev infinityClass : G :=
  N13MumfordKummerKernelForward.infinityClass
end
end MazurProof.N13MumfordOrientedFullKummer
end

end

-- ===== FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm =====
section
/-!
# Norms in monic quadratic polynomial quotients

For a monic quadratic `u`, multiplication by the class of `x + yX` has
matrix

```
!![x, -u.coeff 0 * y; y, x - u.coeff 1 * y].
```

Its determinant is the fixed-degree resultant of `u` and `x + yX`.
Reducing a cubic representative modulo `u` then identifies its algebra norm
with the resultant padded to formal degrees `(2, 3)`.  This gives a
root-free bridge between quadratic quotient algebras and the fixed-degree
resultants used by Padé identities.
-/
namespace MazurProof.QuadraticAdjoinRootNorm
noncomputable section
open Polynomial
variable {K : Type*} [Field K]
def quad (a b : K) : K[X] :=
  X ^ 2 + C b * X + C a
def linearPoly (x y : K) : K[X] :=
  C x + C y * X
end
end MazurProof.QuadraticAdjoinRootNorm
end

end

-- ===== FLT.Assumptions.MazurProof.SquareRootUnitLift =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SquareRootUnitLift =====
section
/-!
# Lifting a square root of a unit

In a commutative monoid, an element whose square is a unit is itself a
unit.  This packages the elementary construction needed when a polynomial
ideal square is identified with an invertible Mumford ideal.
-/
namespace MazurProof.SquareRootUnitLift
variable {A : Type*} [CommMonoid A]
/-- If the square of `a` is a unit, retain a unit lift whose value is
literally `a` together with its square identity. -/
theorem exists_unit_val_eq_and_sq_eq
    (a : A) (u : Aˣ) (h : a ^ 2 = (u : A)) :
    ∃ v : Aˣ, (v : A) = a ∧ v ^ 2 = u := by
  have ha : IsUnit a := by
    apply isUnit_of_mul_isUnit_left
    rw [← pow_two, h]
    exact u.isUnit
  refine ⟨ha.unit, ha.unit_spec, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, ha.unit_spec] using h
end MazurProof.SquareRootUnitLift
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
abbrev O : SexticMumford.InfinityOrder M :=
  N13LowDegreeKummerHom.O
abbrev G : Type :=
  N13LowDegreeKummerHom.G
/-! ## Unfolding the full-gauge fibre -/
theorem scalarUnits_neg (q : ℚˣ) :
    N13FullNormPair.scalarUnits (-q) =
      -N13FullNormPair.scalarUnits q := by
  apply Units.ext
  change
    algebraMap ℚ L (-(q : ℚ)) =
      -algebraMap ℚ L (q : ℚ)
  exact map_neg (algebraMap ℚ L) (q : ℚ)
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-- Multiply a quadratic numerator by the chosen branch square root and
reduce modulo the sextic. -/
def padeRemainderMap (B : ℚ[X]) :
    Polynomial.degreeLT ℚ 3 →ₗ[ℚ] ℚ[X] :=
  (Polynomial.modByMonicHom N13SexticSquareclass.f).comp
    ((LinearMap.mulRight ℚ B).comp
      (Polynomial.degreeLT ℚ 3).subtype)
/-- Only the degree-four and degree-five coefficients obstruct a sextic
remainder from having degree at most three. -/
def padeHighCoeffMap (B : ℚ[X]) :
    Polynomial.degreeLT ℚ 3 →ₗ[ℚ] ℚ × ℚ :=
  (LinearMap.prod
      (Polynomial.lcoeff ℚ 4)
      (Polynomial.lcoeff ℚ 5)).comp
    (padeRemainderMap B)
@[simp] theorem padeRemainderMap_apply
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3) :
    padeRemainderMap B a =
      ((a : ℚ[X]) * B) %ₘ N13SexticSquareclass.f :=
  rfl
/-- The Padé numerator is a dimension argument: a three-dimensional space
maps to the two high coefficients, so its kernel contains a nonzero
quadratic numerator.  This is the structural replacement for searching
over coefficient tuples. -/
theorem exists_pade_numerator (B : ℚ[X]) :
    ∃ a : Polynomial.degreeLT ℚ 3,
      a ≠ 0 ∧ padeHighCoeffMap B a = 0 := by
  have hdim :
      Module.finrank ℚ (ℚ × ℚ) <
        Module.finrank ℚ (Polynomial.degreeLT ℚ 3) := by
    rw [Module.finrank_prod,
      Module.finrank_self,
      Module.finrank_eq_card_basis
        (Polynomial.degreeLT.basis ℚ 3),
      Fintype.card_fin]
    norm_num
  have hker :
      LinearMap.ker (padeHighCoeffMap B) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨a, haKer, ha0⟩ :=
    (Submodule.ne_bot_iff
      (LinearMap.ker (padeHighCoeffMap B))).mp hker
  exact ⟨a, ha0, LinearMap.mem_ker.mp haKer⟩
/-- A nonzero Padé numerator has degree at most two. -/
theorem padeNumerator_natDegree_le_two
    (a : Polynomial.degreeLT ℚ 3) (ha : a ≠ 0) :
    (a : ℚ[X]).natDegree ≤ 2 := by
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha (Subtype.ext h)
  have hlt :
      (a : ℚ[X]).natDegree < 3 :=
    (natDegree_lt_iff_degree_lt haPoly).mpr
      (Polynomial.mem_degreeLT.mp a.property)
  omega
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- The exact graph geometry retained by the Padé square root.  The inverse
of `root` is literally the auxiliary graph ideal `(a,Y-L₀)`, while
`square_eq` is the finite ideal identity used by the quotient proof. -/
structure PadeIdealRootData
    (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (a L₀ : K[X]) where
  root : SexticMumford.InvFrac C
  inverseRoot_coe :
    ((root⁻¹ : SexticMumford.InvFrac C) :
        FractionalIdeal
          (SexticMumford.CoordinateRing C)⁰
          (SexticMumford.FunctionField C)) =
      (mumfordIdeal C a L₀ :
        FractionalIdeal
          (SexticMumford.CoordinateRing C)⁰
          (SexticMumford.FunctionField C))
  square_eq :
    mumfordIdealUnit C D *
        toPrincipalIdeal
          (SexticMumford.CoordinateRing C)
          (SexticMumford.FunctionField C)
          (ySubFunctionUnit C L₀)⁻¹ =
      root ^ 2
/-- The integral Padé identity already makes the auxiliary graph ideal
invertible: an explicit inverse is `J · I_D · (Y-L)⁻¹`.  Hence the target
Mumford fractional ideal is the square of `J⁻¹` after multiplying by the
inverse graph function.  This version retains the literal graph ideal. -/
def padeIdealRootData
    (C : SexticMumford.Model K)
    (D : SexticMumford.SemiMumford C)
    (a L₀ : K[X])
    (hideal :
      mumfordIdeal C a L₀ ^ 2 *
          mumfordIdeal C D.u D.v =
        Ideal.span
          ({ySubClass C L₀} :
            Set (SexticMumford.CoordinateRing C))) :
    PadeIdealRootData C D a L₀ := by
  let J₀ :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C) :=
    (mumfordIdeal C a L₀ :
      FractionalIdeal
        (SexticMumford.CoordinateRing C)⁰
        (SexticMumford.FunctionField C))
  let Dᵤ : SexticMumford.InvFrac C :=
    mumfordIdealUnit C D
  let Pᵤ : SexticMumford.InvFrac C :=
    toPrincipalIdeal
      (SexticMumford.CoordinateRing C)
      (SexticMumford.FunctionField C)
      (ySubFunctionUnit C L₀)
  have hfrac :
      J₀ * J₀ *
          (Dᵤ :
            FractionalIdeal
              (SexticMumford.CoordinateRing C)⁰
              (SexticMumford.FunctionField C)) =
        (Pᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) := by
    dsimp only [J₀, Dᵤ, Pᵤ]
    simp only [coe_mumfordIdealUnit,
      coe_toPrincipalIdeal, coe_ySubFunctionUnit]
    rw [← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul,
      ← pow_two, hideal,
      FractionalIdeal.coeIdeal_span_singleton]
  have hJmul :
      J₀ *
          (J₀ *
            (Dᵤ :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C))) =
        1 := by
    calc
      J₀ *
            (J₀ *
              (Dᵤ :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C)) *
              ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C))) =
          (J₀ * J₀ *
              (Dᵤ :
                FractionalIdeal
                  (SexticMumford.CoordinateRing C)⁰
                  (SexticMumford.FunctionField C))) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) := by
                  ac_rfl
      _ =
          (Pᵤ :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) *
            ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
              FractionalIdeal
                (SexticMumford.CoordinateRing C)⁰
                (SexticMumford.FunctionField C)) := by
                  rw [hfrac]
      _ = 1 := by
        rw [← Units.val_mul]
        simp
  let Jᵤ : SexticMumford.InvFrac C :=
    Units.mkOfMulEqOne
      J₀
      (J₀ *
        (Dᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) *
        ((Pᵤ⁻¹ : SexticMumford.InvFrac C) :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)))
      hJmul
  have hunit :
      Jᵤ ^ 2 * Dᵤ = Pᵤ := by
    apply Units.ext
    change
      J₀ ^ 2 *
          (Dᵤ :
            FractionalIdeal
              (SexticMumford.CoordinateRing C)⁰
              (SexticMumford.FunctionField C)) =
        (Pᵤ :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C))
    simpa only [pow_two] using hfrac
  refine
    { root := Jᵤ⁻¹
      inverseRoot_coe := ?_
      square_eq := ?_ }
  · change
      (((Jᵤ⁻¹)⁻¹ : SexticMumford.InvFrac C) :
          FractionalIdeal
            (SexticMumford.CoordinateRing C)⁰
            (SexticMumford.FunctionField C)) =
        J₀
    rw [inv_inv]
    rfl
  · rw [map_inv]
    change Dᵤ * Pᵤ⁻¹ = Jᵤ⁻¹ ^ 2
    rw [← hunit]
    simp only [mul_inv_rev, pow_two]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
/-! ## Closing the finite ideal square -/
namespace FinitePadeGraphRootData
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
/-- The class with trivial finite ideal and prescribed integer infinity
coordinate. -/
def pureInfinityClass (z : ℤ) : G :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      ((1, Multiplicative.ofAdd z) : OrientedFrac M)
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective =====
section
/-!
# Surjectivity of doubling for the N13 concrete Picard group

The global zero-carrier calculation proves that the actual Mumford Kummer
homomorphism is identically zero.  The structural identity-fibre theorem
identifies its kernel with the subgroup of doubles.  Their composition is
exactly surjectivity of multiplication by two.
-/
namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
abbrev G : Type :=
  N13LowDegreeKummerHom.G
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityBaseChange =====
section
/-!
# Base change at the positive infinity of the N13 sextic

Coefficient extension commutes with the chosen positive Laurent branch of
the N13 function field.  The only apparent issue is the formal square root
used to define that branch.  We avoid coefficient calculations: after base
change the two candidate square roots have the same square and constant
coefficient `1`, so the factorization of a difference of squares excludes
the negative root.

For an injective coefficient map, coefficientwise extension of Laurent
series also preserves the support, hence its integer order.  Together these
facts give compatibility of the oriented infinity order and the induced
base-change map on concrete Picard groups.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
/-- Coefficientwise extension of Laurent series as a bundled ring map. -/
def laurentMap (ι : K →+* K') :
    LaurentSeries K →+* LaurentSeries K' where
  toFun z := z.map ι
  map_zero' := HahnSeries.map_zero ι.toZeroHom
  map_one' := HahnSeries.map_one ι.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add ι.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul ι.toNonUnitalRingHom
omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_coeff
    (ι : K →+* K') (z : LaurentSeries K) (n : ℤ) :
    (laurentMap ι z).coeff n = ι (z.coeff n) := rfl
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
end
end MazurProof.N13InfinityBaseChange
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralFiberDetection =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralFiberDetection =====
section
open Polynomial
open scoped BigOperators nonZeroDivisors
namespace MazurProof.N13IntegralFiberDetection
noncomputable section
attribute [local instance] MazurProof.N13IntegralFiberDetection.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
namespace DefectDualFrame
end DefectDualFrame
namespace ContractedDualFrame
variable {J : Ideal RationalRing}
end ContractedDualFrame
namespace ContractedDualFrame
variable {J : Ideal RationalRing}
end ContractedDualFrame
end
end MazurProof.N13IntegralFiberDetection
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialProductLift =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialProductLift =====
section
/-!
# The finite N13 product-lift seam

The special affine dual frame has three evaluations whose sum is one.
For the integral argument it is unnecessary to lift the six factors
separately.  It suffices to lift each evaluation into the product of the
contracted lattice with its multiplier inverse.  This is a weaker interface
than factorwise dual base change, but it is still the full special trace-unit
certificate and does not follow formally from contraction.

This file records exactly that weaker geometric obligation and connects it
to the generic--special fibre criterion.
-/
open scoped BigOperators nonZeroDivisors
namespace MazurProof.N13SpecialProductLift
noncomputable section
local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
namespace Data
variable {J : Ideal RationalRing}
end Data
end
end MazurProof.N13SpecialProductLift
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphSpread =====
section
/-!
# Invertible integral spreads of N13 Mumford graphs

A smooth integral generalized Mumford graph already gives an invertible
fractional ideal on the integral affine model: this is the explicit global
Jacobian dual-frame theorem.  Exact graph contraction then identifies the
canonical contraction of its generic sextic graph with that same integral
ideal.

Consequently the divisorial-hull construction makes no change at all on an
integral graph.  This is the representative-level adapter needed by the
proper-spread construction; it uses neither local factoriality nor a special
fibre classification.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphSpread
noncomputable section
local instance integralRationalAlgebra :
    Algebra IntegralRing N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
end
end MazurProof.N13IntegralGraphSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13ReductionClassifier =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ReductionClassifier =====
section
/-!
# A set-valued finite reduction target for N13

Reduction injectivity does not require a group law on the nineteen-element
special Abel quotient.  It is enough to define a subgroup `K` of the rational
Picard group and a set-valued classifier whose fibres are exactly the cosets
of `K`.  The quotient group `G ⧸ K` then embeds into the finite classifier
type.

This file isolates that purely structural passage.  The remaining fixed-curve
geometry must construct the classifier and prove its exactness.
-/
namespace MazurProof.N13ReductionClassifier
noncomputable section
open N18RouteC.Separated
universe u v
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- A set-valued classifier whose fibres are precisely the cosets of a
subgroup.  No operation on `S` is assumed. -/
structure Data (G : Type u) (S : Type v) [AddCommGroup G] where
  kernel : AddSubgroup G
  classify : G → S
  exact : ∀ P Q : G,
    classify P = classify Q ↔ P - Q ∈ kernel
namespace Data
variable {G : Type u} {S : Type v} [AddCommGroup G]
/-- The genuine additive reduction target: the actual image quotient. -/
abbrev Target (D : Data G S) : Type u :=
  G ⧸ D.kernel
/-- The quotient map onto the actual image target. -/
def red (D : Data G S) : G →+ D.Target :=
  QuotientAddGroup.mk' D.kernel
theorem classify_respects_leftRel
    (D : Data G S) (P Q : G)
    (hPQ : QuotientAddGroup.leftRel D.kernel P Q) :
    D.classify P = D.classify Q := by
  apply (D.exact P Q).2
  have hQP : -P + Q ∈ D.kernel :=
    QuotientAddGroup.leftRel_apply.mp hPQ
  have hPQ' := D.kernel.neg_mem hQP
  simpa [sub_eq_add_neg, add_comm] using hPQ'
/-- The set-valued classifier descends to the actual image quotient. -/
def quotientClassify (D : Data G S) : D.Target → S :=
  fun z =>
    Quotient.liftOn' z D.classify D.classify_respects_leftRel
theorem quotientClassify_injective (D : Data G S) :
    Function.Injective D.quotientClassify := by
  intro x y
  revert y
  refine QuotientAddGroup.induction_on x (fun P y => ?_)
  refine QuotientAddGroup.induction_on y (fun Q hxy => ?_)
  apply QuotientAddGroup.eq.mpr
  have hclass : D.classify P = D.classify Q := by
    simpa only [quotientClassify,
      QuotientAddGroup.quotient_liftOn_mk] using hxy
  have hPQ : P - Q ∈ D.kernel :=
    (D.exact P Q).1 hclass
  have hQP := D.kernel.neg_mem hPQ
  simpa [sub_eq_add_neg, add_comm] using hQP
noncomputable instance targetFinite
    (D : Data G S) [Finite S] :
    Finite D.Target :=
  Finite.of_injective D.quotientClassify
    D.quotientClassify_injective
end Data
abbrev G : Type :=
  N13MumfordFullKummerTwoSurjective.G
end
end MazurProof.N13ReductionClassifier
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialCuspReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCuspReduction =====
section
/-!
# The six N13 cusps on the special fibre

The good characteristic-two model has three hyperelliptic base points and
two sheets over each of them.  The six rational cusps reduce to these six
points bijectively.  This file records that correspondence as an explicit
equivalence.

The proof uses only the structural fact that every element of `F₂` is zero
or one.  It does not enumerate divisors or Jacobian representatives.
-/
namespace MazurProof.N13SpecialCuspReduction
noncomputable section
open N13AbelFiberTwoModel
/-- Coordinates of a rational cusp on the good special fibre.  The affine
coordinate change is `Y = 2y + x³ + x + 1`; this explains the reversal of
the two sheets over `x = 1`. -/
def cuspCoordinate : Cusp13 → BasePoint × K
  | .infinityPlus => (Sum.inr (), 0)
  | .infinityMinus => (Sum.inr (), 1)
  | .zeroPlus => (Sum.inl 0, 0)
  | .zeroMinus => (Sum.inl 0, 1)
  | .negOnePlus => (Sum.inl 1, 1)
  | .negOneMinus => (Sum.inl 1, 0)
end
end MazurProof.N13SpecialCuspReduction
end

end

-- ===== FLT.Assumptions.MazurProof.N13RationalPointEndgame =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RationalPointEndgame =====
section
/-!
# The structural N13 rational-point endgame

This file isolates the exact proper-reduction input still needed after the
N13 two-descent and formal-kernel arguments.

A compatible reduction consists of the existing exact set-valued Picard
classifier, a reduction of rational curve points to the good special fibre,
and compatibility with the Abel map and the six rational cusps.  Since the
six cusps cover the special curve, every rational curve point has the same
reduced Abel class as a cusp.  Separatedness makes Picard reduction
injective, and the already-proved Abel--Jacobi embedding then identifies the
two curve points.

No group law on the nineteen-element set and no finite table are used.
-/
namespace MazurProof.N13RationalPointEndgame
noncomputable section
open scoped Sym2
abbrev G : Type :=
  N13ReductionClassifier.G
def rationalAbel : RationalCurvePoint → G :=
  N13MumfordAbelJacobi.abelJacobi ℚ
namespace CompatibleReduction
end CompatibleReduction
end
end MazurProof.N13RationalPointEndgame
end

end

-- ===== FLT.Assumptions.MazurProof.N13ProperCurveReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ProperCurveReduction =====
section
/-!
# Proper two-chart reduction of N13 curve points at two

Rational points on the sextic are first transported to the generalized
hyperelliptic equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`.

If `x` is integral, its monic equation makes `y` integral and the point
reduces on the affine chart.  If `x` is nonintegral, put `t = x⁻¹` and
`v = t³y`; then the monic infinity-chart equation makes `v` integral,
while positive valuation of `t` forces its residue to be zero.  Thus the
construction is proper and genuinely uses both charts.

The final theorem identifies the reductions of the six rational cusps
with the previously constructed six-point special-fibre equivalence.
No point enumeration is used.
-/
namespace MazurProof.N13ProperCurveReduction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem norm_le_one_of_quadratic
    (a b y : Q₂)
    (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1)
    (h : y ^ 2 + a * y = b) :
    ‖y‖ ≤ 1 := by
  by_contra hy
  have hy1 : 1 < ‖y‖ := lt_of_not_ge hy
  have hay : ‖a * y‖ ≤ ‖y‖ := by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ha (norm_nonneg y)
  have hylt : ‖y‖ < ‖y ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hsmall : ‖a * y‖ < ‖y ^ 2‖ :=
    lt_of_le_of_lt hay hylt
  have hsum :
      ‖y ^ 2 + a * y‖ = ‖y ^ 2‖ := by
    rw [Padic.add_eq_max_of_ne (ne_of_gt hsmall),
      max_eq_left (le_of_lt hsmall)]
  have hbig : 1 < ‖b‖ := by
    rw [← h, hsum]
    exact hy1.trans hylt
  exact (not_lt_of_ge hb) hbig
def integralAffineLift
    (x y : Q₂)
    (hx : ‖x‖ ≤ 1)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    {p : Z₂ × Z₂ //
      N13GoodModelTwo.AffineEquation p.1 p.2} := by
  let xi : Z₂ := ⟨x, hx⟩
  have ha :
      ‖(N13GoodModelTwo.h xi : Q₂)‖ ≤ 1 :=
    by
      change ‖((↑(N13GoodModelTwo.h xi)) : Q₂)‖ ≤ 1
      exact PadicInt.norm_le_one _
  have hb :
      ‖(N13GoodModelTwo.rhs xi : Q₂)‖ ≤ 1 :=
    by
      change ‖((↑(N13GoodModelTwo.rhs xi)) : Q₂)‖ ≤ 1
      exact PadicInt.norm_le_one _
  have hxy' :
      y ^ 2 + (N13GoodModelTwo.h xi : Q₂) * y =
        (N13GoodModelTwo.rhs xi : Q₂) := by
    simpa [xi, N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs] using hxy
  let yi : Z₂ :=
    ⟨y, norm_le_one_of_quadratic
      (N13GoodModelTwo.h xi : Q₂)
      (N13GoodModelTwo.rhs xi : Q₂) y ha hb hxy'⟩
  refine ⟨(xi, yi), ?_⟩
  exact Subtype.coe_injective (by
    simpa [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs, yi] using hxy')
def reduceIntegralAffine
    (x y : Q₂)
    (hx : ‖x‖ ≤ 1)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SpecialCurvePoint := by
  let P := integralAffineLift x y hx hxy
  exact Sum.inl ⟨
    (PadicInt.toZMod P.1.1, PadicInt.toZMod P.1.2),
    by
      simpa [N13GoodModelTwo.AffineEquation,
        N13GoodModelTwo.h, N13GoodModelTwo.rhs] using
        congrArg (PadicInt.toZMod (p := 2)) P.2⟩
def nonintegralInfinityLift
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    {p : Z₂ × Z₂ //
      N13GoodModelTwo.InfinityChartEquation p.1 p.2} := by
  let ti : Z₂ :=
    N13LocalDlogRegimes.inverseIntegralPart x hx
  let v : Q₂ := (ti : Q₂) ^ 3 * y
  have hx0 : x ≠ 0 :=
    N13LocalDlogRegimes.nonintegral_coordinate_ne_zero x hx
  have hxt : x * (ti : Q₂) = 1 := by
    simpa [ti, N13LocalDlogRegimes.inverseIntegralPart] using
      mul_inv_cancel₀ hx0
  have hyrel : x ^ 3 * v = y := by
    calc
      x ^ 3 * v = x ^ 3 * (x⁻¹ ^ 3 * y) := by
        simp [v, ti, N13LocalDlogRegimes.inverseIntegralPart]
      _ = (x * x⁻¹) ^ 3 * y := by rw [mul_pow, mul_assoc]
      _ = y := by rw [mul_inv_cancel₀ hx0, one_pow, one_mul]
  have hinf :
      N13GoodModelTwo.InfinityChartEquation (ti : Q₂) v := by
    apply (N13GoodModelTwo.affine_iff_infinity_on_overlap hxt).mp
    simpa only [hyrel] using hxy
  have ha :
      ‖((1 + ti ^ 2 + ti ^ 3 : Z₂) : Q₂)‖ ≤ 1 := by
    exact PadicInt.norm_le_one _
  have hb :
      ‖((ti + ti ^ 2 : Z₂) : Q₂)‖ ≤ 1 := by
    exact PadicInt.norm_le_one _
  have hv :
      ‖v‖ ≤ 1 := by
    apply norm_le_one_of_quadratic
      ((1 + ti ^ 2 + ti ^ 3 : Z₂) : Q₂)
      ((ti + ti ^ 2 : Z₂) : Q₂) v ha hb
    simpa [N13GoodModelTwo.InfinityChartEquation] using hinf
  let vi : Z₂ := ⟨v, hv⟩
  refine ⟨(ti, vi), ?_⟩
  exact Subtype.coe_injective (by
    simpa [N13GoodModelTwo.InfinityChartEquation, vi] using hinf)
def reduceNonintegralAffine
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SpecialCurvePoint := by
  let P := nonintegralInfinityLift x y hx hxy
  have htzero :
      PadicInt.toZMod P.1.1 = 0 := by
    change PadicInt.toZMod
      (N13LocalDlogRegimes.inverseIntegralPart x hx) = 0
    exact
      N13LocalDlogRegimes.inverseIntegralPart_residue_eq_zero x hx
  exact Sum.inr ⟨PadicInt.toZMod P.1.2, by
    have hred :=
      congrArg (PadicInt.toZMod (p := 2)) P.2
    simpa [N13GoodModelTwo.InfinityChartEquation, htzero] using hred⟩
def reduceAffine
    (X Y : ℚ) (hcurve : N13CurveModel.C13SexticEq X Y) :
    SpecialCurvePoint := by
  let x : Q₂ := ratToQ₂ X
  let y : Q₂ :=
    ratToQ₂ (N13GoodModelTwo.sexticToGoodY X Y)
  have hxy : N13GoodModelTwo.AffineEquation x y := by
    exact map_good_equation hcurve
  by_cases hx : ‖x‖ ≤ 1
  · exact reduceIntegralAffine x y hx hxy
  · have hxval : x.valuation < 0 := by
      exact lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx)
    exact reduceNonintegralAffine x y hxval hxy
@[simp] theorem toZMod_mk_neg_one
    (h : ‖(-1 : Q₂)‖ ≤ 1) :
    PadicInt.toZMod (⟨-1, h⟩ : Z₂) = 1 := by
  have heq : (⟨-1, h⟩ : Z₂) = -(1 : ℤ_[2]) := by
    apply Subtype.ext
    simp
  rw [heq, map_neg, map_one]
  exact ZMod.neg_eq_self_mod_two 1
end
end MazurProof.N13ProperCurveReduction
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread =====
section
/-!
# Integral spreads of affine N13 points

An integral point of the good two-adic affine chart gives the monic linear
generalized Mumford graph `(X-x, y)`.  Its curve equation follows by the
factor theorem.  Completion of the square identifies its generic sextic
graph with the standard Mumford graph of the corresponding curve point.

The semigraph contraction theorem and the global Jacobian frame therefore
make the canonical divisorial spread invertible.  This closes the affine
half of the proper degree-one branch without local factoriality.
-/
open Polynomial
namespace MazurProof.N13IntegralAffinePointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpread.instFactPrimeOfNatNat_fLT
def pointU (P : IntegralPoint) : R₂[X] :=
  X - C P.1.1
def pointV (P : IntegralPoint) : R₂[X] :=
  C P.1.2
def pointResidual (P : IntegralPoint) : R₂[X] :=
  pointV P ^ 2 +
    N13GeneralizedMumfordIntegral.hPoly (R := R₂) * pointV P -
    N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)
theorem pointResidual_eval (P : IntegralPoint) :
    (pointResidual P).eval P.1.1 = 0 := by
  simpa [pointResidual, pointV,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodModelTwo.AffineEquation,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    sub_eq_zero] using P.2
theorem pointU_dvd_pointResidual (P : IntegralPoint) :
    pointU P ∣ pointResidual P := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointResidual P) (a := P.1.1)
  simpa [pointU, pointResidual_eval] using h
def pointW (P : IntegralPoint) : R₂[X] :=
  Classical.choose (pointU_dvd_pointResidual P)
theorem pointResidual_eq_mul_pointW (P : IntegralPoint) :
    pointResidual P = pointU P * pointW P :=
  Classical.choose_spec (pointU_dvd_pointResidual P)
/-- The literal monic linear integral graph of an affine integral point. -/
def integralSemiGraph (P : IntegralPoint) :
    IntegralSemiMumford where
  u := pointU P
  v := pointV P
  w := pointW P
  u_monic := monic_X_sub_C P.1.1
  curve_eq := pointResidual_eq_mul_pointW P
@[simp] theorem sexticSemi_u (P : IntegralPoint) :
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi
      (integralSemiGraph P) 0).u =
      X - C (P.1.1 : Q₂) := by
  simp [integralSemiGraph, pointU,
    N13TwoAdicMumfordTransport.mapPoly,
    N13TwoAdicMumfordTransport.coeffMap]
/-- The literal integral affine graph ideal of an integral point. -/
def pointIdeal (P : IntegralPoint) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal
    (integralSemiGraph P).u (integralSemiGraph P).v
/-! ## The integral branch of the selected degree-one Padé graph -/
end
end MazurProof.N13IntegralAffinePointSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13CechLaurentSeriesCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CechLaurentSeriesCore =====
section
/-!
# The formal Laurent-series Čech core

The proper two-chart calculation at infinity uses Laurent series, not only
Laurent polynomials: a function such as `1 / (1 + t)` is regular at
`t = 0`, but has an infinite power-series tail.

Write a formal overlap function in the basis `1,v` as `a(t) + b(t)v`.
The affine chart contributes scalar exponents at most zero and
`v`-exponents at most `-3`; the formal infinity chart contributes
nonnegative exponents.  Their additive Čech quotient is therefore still
represented exactly by

`b₋₂, b₋₁`.

Unlike the finite Laurent-polynomial model, this file includes every
power-series tail and hence gives the correct formal neighbourhood used by
the proper lifting argument.
-/
namespace MazurProof.N13CechLaurentSeriesCore
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
universe u
variable {R : Type u} [CommRing R]
/-- Read the coefficients of `v t⁻²` and `v t⁻¹`. -/
def obstruction :
    Overlap (R := R) →ₗ[R] Obstruction (R := R) where
  toFun z := ![z.2.coeff (-2), z.2.coeff (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp
  map_smul' c z := by
    funext i
    fin_cases i <;> simp
@[simp] theorem obstruction_apply_zero
    (z : Overlap (R := R)) :
    obstruction z 0 = z.2.coeff (-2) := rfl
@[simp] theorem obstruction_apply_one
    (z : Overlap (R := R)) :
    obstruction z 1 = z.2.coeff (-1) := rfl
/-- Coercion of a formal power series to a Laurent series, as a linear
map. -/
def includePower :
    Power (R := R) →ₗ[R] Laurent (R := R) where
  toFun f := (f : Laurent (R := R))
  map_add' f g := PowerSeries.coe_add f g
  map_smul' c f := PowerSeries.coe_smul c f
section Field
variable {F : Type u} [Field F]
end Field
end
end MazurProof.N13CechLaurentSeriesCore
end

end

-- ===== FLT.Assumptions.MazurProof.N13CechLaurentCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CechLaurentCore =====
section
/-!
# The two-chart Laurent Čech core

For a generalized hyperelliptic equation of degree six, write an overlap
function in the infinity coordinates as `a(t) + b(t)v`.  The affine chart
contributes scalar Laurent exponents at most zero and `v`-exponents at most
`-3`; the infinity chart contributes nonnegative exponents.  Their additive
Čech quotient is therefore represented exactly by the two coefficients

`b₋₂, b₋₁`.

This calculation is valid over every commutative coefficient ring.  Keeping
it ring-generic lets the N13 special fibre and its integral two-adic lift use
the same decomposition theorem.
-/
namespace MazurProof.N13CechLaurentCore
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
universe u
variable {R : Type u} [CommRing R]
/-- Read the coefficients of `v t⁻²` and `v t⁻¹`. -/
def obstruction :
    Overlap (R := R) →ₗ[R] Obstruction (R := R) where
  toFun z := ![AddMonoidAlgebra.coeff z.2 (-2), AddMonoidAlgebra.coeff z.2 (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul]
  map_smul' c z := by
    funext i
    fin_cases i <;> simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul]
@[simp] theorem obstruction_apply_zero
    (z : Overlap (R := R)) :
    obstruction z 0 = AddMonoidAlgebra.coeff z.2 (-2) := rfl
@[simp] theorem obstruction_apply_one
    (z : Overlap (R := R)) :
    obstruction z 1 = AddMonoidAlgebra.coeff z.2 (-1) := rfl
section Field
variable {F : Type u} [Field F]
end Field
end
end MazurProof.N13CechLaurentCore
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralFormalCech =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralFormalCech =====
section
/-!
# The actual formal principal parts in the integral N13 Čech complex

The second N13 base point produces a regular tail containing
`1 / (1 + t)`.  This is why the proper/formal overlap must use Laurent
series rather than Laurent polynomials.

This file writes both integral principal parts as genuine formal Laurent
series, proves their cleared-denominator identities, and identifies their
classes with the finite connecting matrix already used by the
Čech--Nakayama argument.
-/
namespace MazurProof.N13IntegralFormalCech
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralFormalCech.instFactPrimeOfNatNat_fLT
@[simp] theorem tPow_mul (m n : ℤ) :
    tPow m * tPow n = tPow (m + n) := by
  simp [tPow]
/-! ## The genuine formal Čech quotient -/
end
end MazurProof.N13IntegralFormalCech
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalLineBundleCech =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalLineBundleCech =====
section
/-!
# Near-trivial formal line bundles in the N13 Čech chart

A line bundle in the kernel of specialization admits, after choosing local
trivializations, a formal overlap transition which reduces to `1`.  Twisting
the two actual principal parts by such a transition perturbs the integral
connecting matrix, but does not change its special fibre.

This file encodes the actual quadratic formal curve algebra at infinity,
proves coefficientwise reduction respects its multiplication, and applies
the previously proved Čech--Nakayama theorem to every invertible transition
reducing to `1`.

The remaining geometric task is now sharply isolated: construct these two
local trivializations from a rational Picard class in the specialization
kernel.  No cohomology or matrix-surjectivity hypothesis remains.
-/
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalLineBundleCech.instFactPrimeOfNatNat_fLT
/-- A Laurent monomial over an arbitrary coefficient ring. -/
def tPow
    {R : Type*} [CommRing R] (n : ℤ) :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  HahnSeries.single n 1
/-- The coefficient of `v` in the integral infinity-chart equation. -/
def hInfinity
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  tPow 0 + tPow 2 + tPow 3
/-- The right-hand side of the integral infinity-chart equation. -/
def rhsInfinity
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  tPow 1 + tPow 2
/-- Coefficientwise reduction of a two-adic Laurent series. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod
def reduceLaurent (f : Laurent₂) : LaurentBar :=
  f.map reduceBase
@[simp] theorem reduceLaurent_coeff
    (f : Laurent₂) (n : ℤ) :
    (reduceLaurent f).coeff n =
      reduceBase (f.coeff n) := rfl
@[simp] theorem reduceLaurent_zero :
    reduceLaurent 0 = 0 :=
  HahnSeries.map_zero
    reduceBase.toZeroHom
@[simp] theorem reduceLaurent_one :
    reduceLaurent 1 = 1 := by
  exact
    HahnSeries.map_one
      reduceBase.toMonoidWithZeroHom
@[simp] theorem reduceLaurent_add
    (f g : Laurent₂) :
    reduceLaurent (f + g) =
      reduceLaurent f + reduceLaurent g := by
  exact
    HahnSeries.map_add
      reduceBase.toAddMonoidHom
@[simp] theorem reduceLaurent_mul
    (f g : Laurent₂) :
    reduceLaurent (f * g) =
      reduceLaurent f * reduceLaurent g := by
  exact
    HahnSeries.map_mul
      reduceBase.toNonUnitalRingHom
/-- Coefficientwise reduction in the basis `1,v`. -/
def reduceOverlap (z : Overlap₂) : OverlapBar :=
  (reduceLaurent z.1, reduceLaurent z.2)
@[simp] theorem reduceOverlap_one :
    reduceOverlap (oneOverlap (R := R₂)) =
      oneOverlap (R := K) := by
  simp [reduceOverlap, oneOverlap]
namespace NearIdentityTransition
end NearIdentityTransition
end
end MazurProof.N13FormalLineBundleCech
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalCurveOverlap =====
section
/-!
# The actual formal overlap algebra for the N13 integral curve

The pair multiplication used by the formal Čech calculation is not an
abstract two-dimensional algebra.  It is the normal-form multiplication in
the quadratic algebra

`R₂((t))[v] / (v² + (1+t²+t³)v - (t+t²))`.

This file identifies the two descriptions and constructs the restriction
homomorphism from the actual affine coordinate ring by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

Thus a unit obtained from a genuine local trivialization gives, without any
extra inverse hypothesis, the `NearIdentityTransition` consumed by the
Čech--Nakayama theorem.
-/
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The quadratic equation of the actual formal infinity chart. -/
def formalCurvePoly : Laurent[X] :=
  X ^ 2 +
    Polynomial.C
        (N13FormalLineBundleCech.hInfinity (R := R₂)) * X -
      Polynomial.C
        (N13FormalLineBundleCech.rhsInfinity (R := R₂))
theorem formalCurvePoly_monic :
    formalCurvePoly.Monic := by
  unfold formalCurvePoly
  monicity <;> norm_num
/-- The actual quadratic algebra on the punctured formal infinity chart. -/
abbrev FormalCurve : Type :=
  AdjoinRoot formalCurvePoly
/-- The formal coordinate `v`. -/
def vClass : FormalCurve :=
  AdjoinRoot.root formalCurvePoly
/-- The canonical normal polynomial of degree below two. -/
def normalPoly :
    FormalCurve →ₗ[Laurent] Laurent[X] :=
  AdjoinRoot.modByMonicHom formalCurvePoly_monic
/-- Scalar coefficient in the basis `1,v`. -/
def coeff0 :
    FormalCurve →ₗ[Laurent] Laurent :=
  (Polynomial.lcoeff Laurent 0).comp normalPoly
/-- `v`-coefficient in the basis `1,v`. -/
def coeffV :
    FormalCurve →ₗ[Laurent] Laurent :=
  (Polynomial.lcoeff Laurent 1).comp normalPoly
/-! ## Restriction of the actual affine coordinate ring -/
/-- Laurent monomials in the overlap parameter. -/
def tPow (n : ℤ) : Laurent :=
  HahnSeries.single n 1
@[simp] theorem tPow_mul (m n : ℤ) :
    tPow m * tPow n = tPow (m + n) := by
  simp [tPow]
@[simp] theorem tPow_zero :
    tPow 0 = 1 := rfl
/-- Evaluate an affine polynomial at `x=t⁻¹`. -/
def polyAtTInv : R₂[X] →+* Laurent :=
  Polynomial.eval₂RingHom
    (algebraMap R₂ Laurent) (tPow (-1))
/-- Coefficients of the affine quadratic equation restricted to the formal
overlap. -/
def affineCoeffMap : R₂[X] →+* FormalCurve :=
  (AdjoinRoot.of formalCurvePoly).comp polyAtTInv
/-- The affine coordinate `y` restricts to `t⁻³v`. -/
def yImage : FormalCurve :=
  algebraMap Laurent FormalCurve (tPow (-3)) * vClass
end
end MazurProof.N13FormalCurveOverlap
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityChart =====
section
/-!
# The actual formal infinity chart of the N13 integral curve

The additive Čech calculation described the infinity-chart image as pairs of
power series.  This file realizes that submodule as the image of the actual
quadratic formal curve

`ℤ₂[[t]][v] / (v² + (1+t²+t³)v - (t+t²))`

inside the punctured formal overlap.  In particular, the previously defined
`infinitySections` is neither an approximation nor a coefficientwise
superset: it is exactly the restriction image of the genuine chart ring.
-/
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13FormalInfinityChart.instFactPrimeOfNatNat_fLT
abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve
/-- The quadratic equation on the complete infinity chart. -/
def infinityCurvePoly : Power[X] :=
  X ^ 2 + Polynomial.C hPower * X -
    Polynomial.C rhsPower
theorem infinityCurvePoly_monic :
    infinityCurvePoly.Monic := by
  unfold infinityCurvePoly
  monicity <;> norm_num
/-- The actual complete formal infinity-chart ring. -/
abbrev InfinityCurve : Type :=
  AdjoinRoot infinityCurvePoly
/-- Its formal coordinate `v`. -/
def vClass : InfinityCurve :=
  AdjoinRoot.root infinityCurvePoly
/-- Coercion of power series to Laurent series as a ring homomorphism. -/
def includePowerRing : Power →+* Laurent :=
  HahnSeries.ofPowerSeries ℤ R₂
@[simp] theorem includePowerRing_X :
    includePowerRing PowerSeries.X =
      N13FormalCurveOverlap.tPow 1 := by
  exact HahnSeries.ofPowerSeries_X
/-- Restriction of formal-chart coefficients to the punctured overlap. -/
def infinityCoeffMap : Power →+* FormalCurve :=
  (AdjoinRoot.of N13FormalCurveOverlap.formalCurvePoly).comp
    includePowerRing
/-! ## Normal form on the complete chart -/
def normalPoly :
    InfinityCurve →ₗ[Power] Power[X] :=
  AdjoinRoot.modByMonicHom infinityCurvePoly_monic
def coeff0 :
    InfinityCurve →ₗ[Power] Power :=
  (Polynomial.lcoeff Power 0).comp normalPoly
def coeffV :
    InfinityCurve →ₗ[Power] Power :=
  (Polynomial.lcoeff Power 1).comp normalPoly
end
end MazurProof.N13FormalInfinityChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityChart =====
section
/-!
# The ordinary integral infinity chart of N13

This algebraic chart precedes completion.  It is the quadratic algebra over
`ℤ₂[t]` cut out by

`v² + (1+t²+t³)v = t+t²`.

The coefficientwise map `ℤ₂[t] → ℤ₂[[t]]` induces the canonical completion
map to the already constructed formal infinity chart.
-/
open Polynomial
namespace MazurProof.N13IntegralInfinityChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityChart.instFactPrimeOfNatNat_fLT
abbrev FormalInfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve
/-- The ordinary quadratic infinity-chart equation. -/
def infinityCurvePoly : Base[X] :=
  X ^ 2 + C hBase * X - C rhsBase
theorem infinityCurvePoly_monic :
    infinityCurvePoly.Monic := by
  unfold infinityCurvePoly
  monicity <;> norm_num
/-- The actual algebraic infinity-chart coordinate ring before completion. -/
abbrev InfinityCurve : Type :=
  AdjoinRoot infinityCurvePoly
/-- The ordinary coordinates `t` and `v`. -/
def tClass : InfinityCurve :=
  algebraMap Base InfinityCurve X
def vClass : InfinityCurve :=
  AdjoinRoot.root infinityCurvePoly
theorem formal_v_relation :
    infinityCurvePoly.eval₂
        ((algebraMap Power FormalInfinityCurve).comp baseToPower)
        N13FormalInfinityChart.vClass = 0 := by
  simp only [infinityCurvePoly, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C, eval₂_mul,
    RingHom.comp_apply, baseToPower_hBase,
    baseToPower_rhsBase]
  change
    AdjoinRoot.mk
      N13FormalInfinityChart.infinityCurvePoly
      N13FormalInfinityChart.infinityCurvePoly = 0
  exact
    AdjoinRoot.mk_self
/-- Completion of the ordinary infinity chart at the parameter `t`. -/
def toFormalInfinity :
    InfinityCurve →+* FormalInfinityCurve :=
  AdjoinRoot.lift
    ((algebraMap Power FormalInfinityCurve).comp baseToPower)
    N13FormalInfinityChart.vClass formal_v_relation
@[simp] theorem toFormalInfinity_tClass :
    toFormalInfinity tClass =
      algebraMap Power FormalInfinityCurve PowerSeries.X := by
  simp [toFormalInfinity, tClass, baseToPower]
@[simp] theorem toFormalInfinity_vClass :
    toFormalInfinity vClass =
      N13FormalInfinityChart.vClass := by
  exact AdjoinRoot.lift_root formal_v_relation
end
end MazurProof.N13IntegralInfinityChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap =====
section
/-!
# The ordinary algebraic overlap of the two N13 charts

This file begins the ordinary, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13OrdinaryCurveOverlap.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev InfinityOverlap : Type :=
  Localization.Away N13IntegralInfinityChart.tClass
def tOverlap : InfinityOverlap :=
  algebraMap InfinityCurve InfinityOverlap
    N13IntegralInfinityChart.tClass
def xOverlap : InfinityOverlap :=
  IsLocalization.Away.invSelf N13IntegralInfinityChart.tClass
def vOverlap : InfinityOverlap :=
  algebraMap InfinityCurve InfinityOverlap
    N13IntegralInfinityChart.vClass
@[simp] theorem tOverlap_mul_xOverlap :
    tOverlap * xOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := InfinityOverlap)
      N13IntegralInfinityChart.tClass
theorem xOverlap_isUnit :
    IsUnit xOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨tOverlap, by simpa [mul_comm] using tOverlap_mul_xOverlap⟩
def coefficientToInfinityOverlap : R₂ →+* InfinityOverlap :=
  (algebraMap InfinityCurve InfinityOverlap).comp
    ((algebraMap Base InfinityCurve).comp
      (Polynomial.C : R₂ →+* Base))
def affineCoeffMap : R₂[X] →+* InfinityOverlap :=
  Polynomial.eval₂RingHom coefficientToInfinityOverlap xOverlap
def affineYImage : InfinityOverlap :=
  xOverlap ^ 3 * vOverlap
@[simp] theorem affineCoeffMap_hPoly :
    affineCoeffMap
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      xOverlap ^ 3 + xOverlap + 1 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GeneralizedMumfordIntegral.hPoly]
@[simp] theorem affineCoeffMap_rhsPoly :
    affineCoeffMap
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      xOverlap ^ 5 + xOverlap ^ 4 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GeneralizedMumfordIntegral.rhsPoly]
/-! ## The reverse chart map -/
@[simp] theorem xAffineOverlap_mul_tAffineOverlap :
    xAffineOverlap * tAffineOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := AffineOverlap) xClass
theorem tAffineOverlap_isUnit :
    IsUnit tAffineOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨xAffineOverlap,
      by simpa [mul_comm] using xAffineOverlap_mul_tAffineOverlap⟩
def infinityCoeffMap : Base →+* AffineOverlap :=
  Polynomial.eval₂RingHom
    coefficientToAffineOverlap tAffineOverlap
@[simp] theorem infinityCoeffMap_hBase :
    infinityCoeffMap N13IntegralInfinityChart.hBase =
      1 + tAffineOverlap ^ 2 + tAffineOverlap ^ 3 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13IntegralInfinityChart.hBase]
@[simp] theorem infinityCoeffMap_rhsBase :
    infinityCoeffMap N13IntegralInfinityChart.rhsBase =
      tAffineOverlap + tAffineOverlap ^ 2 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13IntegralInfinityChart.rhsBase]
end
end MazurProof.N13OrdinaryCurveOverlap
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveScheme =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveScheme =====
section
/-!
# The integral two-chart N13 curve

The ordinary affine and infinity charts over `R₂` are glued along their
distinguished principal opens.  As for the special fibre, the index type
is `Bool`, so the genuinely three-distinct-index part of
`CategoryTheory.GlueData'` is empty.
-/
open CategoryTheory CategoryTheory.Limits
open Polynomial
namespace MazurProof.N13IntegralCurveScheme
noncomputable section
attribute [local instance] MazurProof.N13IntegralCurveScheme.instFactPrimeOfNatNat_fLT
abbrev Infinity :=
  N13OrdinaryCurveOverlap.InfinityCurve
abbrev InfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap
open AlgebraicGeometry
/-- The ordinary affine and infinity charts. -/
def chart : Bool → Scheme
  | false => Spec (.of Affine)
  | true => Spec (.of Infinity)
/-- The two oriented principal-open intersections. -/
def overlap : ∀ i j : Bool, i ≠ j → Scheme
  | false, false, h => False.elim (h rfl)
  | false, true, _ => Spec (.of AffineOverlap)
  | true, false, _ => Spec (.of InfinityOverlap)
  | true, true, h => False.elim (h rfl)
end
end MazurProof.N13IntegralCurveScheme
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveProperties =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveProperties =====
section
/-!
# Integrality of the ordinary N13 model

The affine chart embeds in its rational generic fibre.  On the infinity
chart, the parameter `t` is regular because the coordinate ring is free over
`ℤ₂[t]`; localizing at `t` identifies it with the affine overlap.  Thus both
charts and their common principal open are domains.

The two irreducible chart images cover the glued scheme and have nonempty
intersection.  This proves that the ordinary two-chart N13 model is reduced,
irreducible, and integral without any point enumeration.
-/
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
attribute [local instance] MazurProof.N13IntegralCurveProperties.instFactPrimeOfNatNat_fLT
open AlgebraicGeometry
abbrev InfinityCurve :=
  N13OrdinaryCurveOverlap.InfinityCurve
abbrev InfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap
end
end MazurProof.N13IntegralCurveProperties
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
/-!
# Integral point ideals on the N13 infinity chart

An integral point `(t₀,v₀)` on the ordinary infinity chart with
`t₀ ≡ 0 mod 2` defines the linear graph ideal

`(t-t₀, v-v₀)`.

Its generalized Jacobian in the ordinate direction reduces to `1`, hence
is a two-adic unit.  The abstract graph-ideal product theorem then gives an
explicit inverse for this point ideal.  This is the infinity-chart analogue
of the integral affine semigraph construction.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityPointSpread.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev FunctionField : Type :=
  FractionRing InfinityCurve
abbrev InfinityFractionalIdeal : Type :=
  FractionalIdeal InfinityCurve⁰ FunctionField
def xClassHom : Base →+* InfinityCurve :=
  AdjoinRoot.of N13IntegralInfinityChart.infinityCurvePoly
def yClass : InfinityCurve :=
  N13IntegralInfinityChart.vClass
@[simp] theorem xClassHom_X :
    xClassHom X = N13IntegralInfinityChart.tClass := rfl
theorem yClass_relation :
    yClass ^ 2 +
        xClassHom N13IntegralInfinityChart.hBase * yClass =
      xClassHom N13IntegralInfinityChart.rhsBase := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13IntegralInfinityChart.infinityCurvePoly]
  ring
def pointU (P : IntegralInfinityPoint) : Base :=
  X - C P.1.1
def pointV (P : IntegralInfinityPoint) : Base :=
  C P.1.2
def pointResidual (P : IntegralInfinityPoint) : Base :=
  pointV P ^ 2 +
    N13IntegralInfinityChart.hBase * pointV P -
    N13IntegralInfinityChart.rhsBase
def pointJacobian (P : IntegralInfinityPoint) : Base :=
  2 * pointV P + N13IntegralInfinityChart.hBase
@[simp] theorem pointJacobian_eval (P : IntegralInfinityPoint) :
    (pointJacobian P).eval P.1.1 = pointJacobianValue P := by
  simp [pointJacobian, pointJacobianValue, pointV,
    N13IntegralInfinityChart.hBase]
theorem pointU_dvd_pointJacobian_sub_value
    (P : IntegralInfinityPoint) :
    pointU P ∣ pointJacobian P - C (pointJacobianValue P) := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointJacobian P) (a := P.1.1)
  simpa [pointU, pointJacobian_eval] using h
def pointJacobianQuotient (P : IntegralInfinityPoint) : Base :=
  Classical.choose (pointU_dvd_pointJacobian_sub_value P)
def pointIdeal (P : IntegralInfinityPoint) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    xClassHom yClass (pointU P) (pointV P)
def conjugatePointIdeal
    (P : IntegralInfinityPoint) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    xClassHom yClass (pointU P)
      (GeneralizedGraphIdealCore.conjugateV
        N13IntegralInfinityChart.hBase (pointV P))
/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/
def affineU (P : IntegralInfinityPoint) : R₂[X] :=
  1 - C P.1.1 * X
def affineV (P : IntegralInfinityPoint) : R₂[X] :=
  C P.1.2 * X ^ 3
def affineW (P : IntegralInfinityPoint) : R₂[X] :=
  C P.1.2 * X ^ 3 +
    C (P.1.2 - 1 + P.1.1 * P.1.2) * X ^ 4 +
    C (-1 - P.1.1 + P.1.1 * P.1.2 +
      P.1.1 ^ 2 * P.1.2) * X ^ 5
theorem affineU_ne_zero (P : IntegralInfinityPoint) :
    affineU P ≠ 0 := by
  intro hzero
  have h :=
    congrArg (Polynomial.eval (0 : R₂)) hzero
  simpa [affineU] using h
def affinePointIdeal
    (P : IntegralInfinityPoint) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  GeneralizedGraphIdealCore.graphIdeal
    N13GeneralizedMumfordIntegral.xClassHom
    N13GeneralizedMumfordIntegral.yClass
    (affineU P) (affineV P)
theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        (u : A) (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.mul_mem_left _
        (v : A) (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have h :
          (u : A) * a ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((u⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
    · rw [hz]
      have h :
          (v : A) * b ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((v⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
theorem nonintegralLift_t_residue_eq_zero
    (x y : N13ProperCurveReduction.Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    PadicInt.toZMod
        (N13ProperCurveReduction.nonintegralInfinityLift
          x y hx hxy).1.1 = 0 := by
  change
    PadicInt.toZMod
      (N13LocalDlogRegimes.inverseIntegralPart x hx) = 0
  exact
    N13LocalDlogRegimes.inverseIntegralPart_residue_eq_zero x hx
end
end MazurProof.N13IntegralInfinityPointSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphJacobian =====
section
/-!
# Integral graph ideals on the N13 infinity chart

The ordinary infinity chart has equation

`v² + (1 + t² + t³)v = t + t²`.

An explicit integral Bézout certificate for its two relative Jacobian
rows has the odd value `117`.  Hence the rows generate one over the
two-adic integers, and the general graph-Jacobian dual frame makes every
nondegenerate integral polynomial graph on this chart invertible.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphJacobian.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev FunctionField : Type :=
  FractionRing InfinityCurve
abbrev InfinityFractionalIdeal : Type :=
  FractionalIdeal InfinityCurve⁰ FunctionField
def xClassHom : Base →+* InfinityCurve :=
  N13IntegralInfinityPointSpread.xClassHom
def yClass : InfinityCurve :=
  N13IntegralInfinityPointSpread.yClass
abbrev GraphData : Type :=
  GeneralizedGraphIdealCore.SemiGraph
    N13IntegralInfinityChart.hBase
    N13IntegralInfinityChart.rhsBase
/-- The relative ordinate-Jacobian row. -/
def jacobianV : InfinityCurve :=
  2 * yClass +
    xClassHom N13IntegralInfinityChart.hBase
/-- The relative horizontal-Jacobian row. -/
def jacobianT : InfinityCurve :=
  xClassHom (derivative N13IntegralInfinityChart.hBase) *
      yClass -
    xClassHom (derivative N13IntegralInfinityChart.rhsBase)
def bezoutA : InfinityCurve :=
  (624 * N13IntegralInfinityChart.tClass ^ 4 +
      289 * N13IntegralInfinityChart.tClass ^ 3 -
      101 * N13IntegralInfinityChart.tClass ^ 2 +
      1713 * N13IntegralInfinityChart.tClass + 232) +
    (-450 * N13IntegralInfinityChart.tClass ^ 2 +
      924 * N13IntegralInfinityChart.tClass - 535) * yClass
def bezoutB : InfinityCurve :=
  (-1350 * N13IntegralInfinityChart.tClass ^ 3 -
      624 * N13IntegralInfinityChart.tClass ^ 2 -
      289 * N13IntegralInfinityChart.tClass + 349) +
    (1350 * N13IntegralInfinityChart.tClass ^ 4 +
      1102 * N13IntegralInfinityChart.tClass + 1233) * yClass
end
end MazurProof.N13IntegralInfinityGraphJacobian
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart =====
section
/-!
# Two-chart closures of integral N13 infinity graphs

An integral polynomial graph on the ordinary infinity chart can be
homogenized with the weights

`u ↦ X² u(X⁻¹)`, `v ↦ X³ v(X⁻¹)`, `w ↦ X⁴ w(X⁻¹)`.

`Polynomial.reflect` implements these three weighted reversals.  Reflecting
the infinity semigraph identity at total weight six gives the affine
semigraph identity, while on the Laurent overlap the two graph generators
differ by the units `x²` and `x³`.  Thus every bounded integral infinity
graph supplies an invertible root-free two-chart line.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphTwoChart.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityGraphJacobian.InfinityFractionalIdeal
abbrev GraphData : Type :=
  N13IntegralInfinityGraphJacobian.GraphData
def affineU (D : GraphData) : R₂[X] :=
  D.u.reflect 2
def affineV (D : GraphData) : R₂[X] :=
  D.v.reflect 3
def affineW (D : GraphData) : R₂[X] :=
  D.w.reflect 4
theorem affineU_ne_zero
    (D : GraphData)
    (hu : D.u ≠ 0) :
    affineU D ≠ 0 := by
  intro hzero
  apply hu
  exact Polynomial.reflect_eq_zero_iff.mp hzero
theorem tOverlap_isUnit :
    IsUnit N13OrdinaryCurveOverlap.tOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨N13OrdinaryCurveOverlap.xOverlap,
      N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap⟩
/-- Evaluating a bounded weighted reflection on the affine overlap equals
the original polynomial evaluated at `t=x⁻¹`, multiplied by `xⁿ`. -/
theorem reflect_on_overlap
    (n : ℕ)
    (p : Base)
    (hp : p.natDegree ≤ n) :
    N13OrdinaryCurveOverlap.affineCoeffMap (p.reflect n) =
      N13OrdinaryCurveOverlap.xOverlap ^ n *
        p.eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.tOverlap := by
  letI : Invertible N13OrdinaryCurveOverlap.tOverlap :=
    tOverlap_isUnit.invertible
  have hinv :
      ⅟N13OrdinaryCurveOverlap.tOverlap =
        N13OrdinaryCurveOverlap.xOverlap := by
    exact
      invOf_eq_right_inv
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.tOverlap n p hp
  rw [hinv] at hreflect
  change
    (p.reflect n).eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.xOverlap =
      N13OrdinaryCurveOverlap.xOverlap ^ n *
        p.eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.tOverlap
  calc
    (p.reflect n).eval₂
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
          N13OrdinaryCurveOverlap.xOverlap =
        1 *
          ((p.reflect n).eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap) := by simp
    _ =
        (N13OrdinaryCurveOverlap.xOverlap ^ n *
            N13OrdinaryCurveOverlap.tOverlap ^ n) *
          ((p.reflect n).eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap) := by
          rw [← mul_pow,
            mul_comm N13OrdinaryCurveOverlap.xOverlap
              N13OrdinaryCurveOverlap.tOverlap,
            N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap,
            one_pow, one_mul]
    _ =
        N13OrdinaryCurveOverlap.xOverlap ^ n *
          (((p.reflect n).eval₂
              N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              N13OrdinaryCurveOverlap.xOverlap) *
            N13OrdinaryCurveOverlap.tOverlap ^ n) := by ring
    _ =
        N13OrdinaryCurveOverlap.xOverlap ^ n *
          p.eval₂
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            N13OrdinaryCurveOverlap.tOverlap := by rw [hreflect]
theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        (u : A) (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.mul_mem_left _
        (v : A) (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have h :
          (u : A) * a ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((u⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
    · rw [hz]
      have h :
          (v : A) * b ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((v⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityChart =====
section
/-!
# The special N13 infinity chart is integral

Over `F₂`, the infinity chart is

`v² + (1+t²+t³)v = t+t²`.

Irreducibility follows from a degree gap.  A factorization of the monic
quadratic would give polynomials `a,b` with `a*b = t+t²` and
`a+b = 1+t²+t³`.  The product forces both factors to have degree at most
two, whereas their sum has degree three.

No polynomial enumeration or coefficient table is used.
-/
open Polynomial
namespace MazurProof.N13SpecialInfinityChart
noncomputable section
/-- Coefficient of `v` on the special infinity chart. -/
def hPoly : K[X] :=
  1 + X ^ 2 + X ^ 3
/-- Right-hand side on the special infinity chart. -/
def rhsPoly : K[X] :=
  X + X ^ 2
/-- The outer variable is `v`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly
theorem hPoly_natDegree :
    hPoly.natDegree = 3 := by
  unfold hPoly
  compute_degree
  all_goals norm_num
theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity
  all_goals norm_num
theorem rhsPoly_natDegree :
    rhsPoly.natDegree = 2 := by
  unfold rhsPoly
  compute_degree
  all_goals norm_num
theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity
  all_goals norm_num
theorem curvePoly_natDegree :
    curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree
  all_goals norm_num
theorem curvePoly_irreducible :
    Irreducible curvePoly := by
  by_contra hred
  obtain ⟨a, b, hmul, hadd⟩ :=
    (curvePoly_monic.not_irreducible_iff_exists_add_mul_eq_coeff
      curvePoly_natDegree).mp hred
  have hmul' : rhsPoly = a * b := by
    calc
      rhsPoly = -rhsPoly := (CharTwo.neg_eq rhsPoly).symm
      _ = a * b := by simpa [curvePoly] using hmul
  have hadd' : hPoly = a + b := by
    simpa [curvePoly] using hadd
  have ha0 : a ≠ 0 := by
    intro ha
    apply rhsPoly_monic.ne_zero
    simpa [ha] using hmul'
  have hb0 : b ≠ 0 := by
    intro hb
    apply rhsPoly_monic.ne_zero
    simpa [hb] using hmul'
  have hdegMul :
      (a * b).natDegree = a.natDegree + b.natDegree :=
    Polynomial.natDegree_mul'
      (mul_ne_zero
        (leadingCoeff_ne_zero.mpr ha0)
        (leadingCoeff_ne_zero.mpr hb0))
  rw [← hmul', rhsPoly_natDegree] at hdegMul
  have haDegree : a.natDegree ≤ 2 := by omega
  have hbDegree : b.natDegree ≤ 2 := by omega
  have hsumDegree : (a + b).natDegree ≤ 2 :=
    (natDegree_add_le a b).trans
      (max_le haDegree hbDegree)
  rw [← hadd', hPoly_natDegree] at hsumDegree
  omega
instance curvePolyIrreducibleFact :
    Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩
/-- Coordinate ring of the special infinity chart. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly
instance instIsDomainCoordinateRing : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime
noncomputable instance instAlgebraKCoordinateRing : Algebra K CoordinateRing :=
  inferInstance
noncomputable instance instAlgebraPolynomialKCoordinateRing : Algebra K[X] CoordinateRing :=
  inferInstance
/-- The special coordinates `t` and `v`. -/
def tClass : CoordinateRing :=
  algebraMap K[X] CoordinateRing X
def vClass : CoordinateRing :=
  AdjoinRoot.root curvePoly
end
end MazurProof.N13SpecialInfinityChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityReduction =====
section
/-!
# Reduction of the N13 infinity chart at two

Coefficientwise reduction induces the special infinity chart

`v² + (1+t²+t³)v = t+t²`.

The induced map is onto and its kernel is exactly the vertical ideal `(2)`.
Both statements use the common rank-two normal form `a(t) + b(t)v`; no
enumeration of the special fibre is involved.
-/
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
abbrev IntegralRing : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev SpecialRing : Type :=
  N13SpecialInfinityChart.CoordinateRing
/-- Coefficient reduction on the infinity-chart base. -/
def reduceBase : R₂ →+* K :=
  N13GeneralizedMumfordReduction.reduceBase
/-- Coefficientwise reduction in the parameter `t`. -/
def reducePoly : IntegralBase →+* SpecialBase :=
  Polynomial.mapRingHom reduceBase
@[simp] theorem reducePoly_apply (p : IntegralBase) :
    reducePoly p = p.map reduceBase := rfl
@[simp] theorem reduce_hBase :
    reducePoly N13IntegralInfinityChart.hBase =
      N13SpecialInfinityChart.hPoly := by
  simp [reducePoly, reduceBase,
    N13IntegralInfinityChart.hBase,
    N13SpecialInfinityChart.hPoly]
@[simp] theorem reduce_rhsBase :
    reducePoly N13IntegralInfinityChart.rhsBase =
      N13SpecialInfinityChart.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13IntegralInfinityChart.rhsBase,
    N13SpecialInfinityChart.rhsPoly]
theorem reduce_curvePoly :
    N13IntegralInfinityChart.infinityCurvePoly.map reducePoly =
      N13SpecialInfinityChart.curvePoly := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    N13SpecialInfinityChart.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly N13IntegralInfinityChart.hBase) * X -
        C (reducePoly N13IntegralInfinityChart.rhsBase) =
      X ^ 2 + C N13SpecialInfinityChart.hPoly * X -
        C N13SpecialInfinityChart.rhsPoly
  rw [reduce_hBase, reduce_rhsBase]
theorem special_curve_dvd :
    N13SpecialInfinityChart.curvePoly ∣
      N13IntegralInfinityChart.infinityCurvePoly.map reducePoly := by
  rw [reduce_curvePoly]
/-- Reduction on the ordinary infinity-chart coordinate ring. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd
@[simp] theorem reduce_tClass :
    reduceCoordinate N13IntegralInfinityChart.tClass =
      N13SpecialInfinityChart.tClass := by
  simp [reduceCoordinate, N13IntegralInfinityChart.tClass,
    N13SpecialInfinityChart.tClass]
/-- Ordinary base polynomials inside the ordinary infinity chart. -/
def integralBaseClass (p : IntegralBase) : IntegralRing :=
  algebraMap IntegralBase IntegralRing p
/-- Special base polynomials inside the special infinity chart. -/
def specialBaseClass (p : SpecialBase) : SpecialRing :=
  algebraMap SpecialBase SpecialRing p
end
end MazurProof.N13IntegralInfinityReduction
end

end

-- ===== FLT.Assumptions.MazurProof.N13LocalizationIdealPatch =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalizationIdealPatch =====
section
/-!
# Patching an invertible ideal across one principal localization

Let `B = A[f⁻¹]` and let `K` be the common fraction field.  For a finitely
generated fractional ideal, extension from `A` to `B` commutes with the
multiplier inverse: one power of `f` clears the finitely many denominators
that occur on a generating family.

Consequently, if an integral ideal becomes invertible over `B`, some power
of `f` belongs to `I I⁻¹`.  If `f` is already a unit modulo `I`, a finite
geometric series gives `1 ∈ I I⁻¹`, so `I` is invertible over `A`.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
/-- Every element inverted in the domain localization is nonzero. -/
theorem submonoid_le_nonZeroDivisors :
    M ≤ A⁰ := by
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hunit := IsLocalization.map_units B ⟨x, hx⟩
  have hmapZero : algebraMap A B x = 0 := by
    rw [hzero, map_zero]
  exact hunit.ne_zero hmapZero
variable [IsFractionRing A K] [IsFractionRing B K]
end
end MazurProof.N13LocalizationIdealPatch
end

end

-- ===== FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart =====
section
/-!
# Proper two-chart closure of a finite N13 affine divisor

An invertible ideal on the affine chart need not by itself record its
behaviour at infinity.  For an ideal with finite support over the two-adic
coefficient ring, however, the affine coordinate is integral in the
quotient.  A monic equation for that coordinate reflects to an equation with
constant coefficient one on the infinity chart.  Hence the infinity
uniformizer is a unit modulo the contracted overlap ideal.

The principal-localization patching theorem then upgrades invertibility on
the punctured infinity chart to invertibility on the full infinity chart.
This supplies proper extensions for finite N13 graph ideals, including
integral affine points and the finite irreducible quadratic branch, without
choosing reciprocal coordinates.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13FiniteAffineTwoChart.instFactPrimeOfNatNat_fLT
/-- The ordinary affine integral chart. -/
abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve
/-- The ordinary infinity integral chart. -/
abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve
/-- The common principal-open overlap, expressed in infinity coordinates. -/
abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap
/-- Affine fractional ideals in the canonical N13 function field. -/
abbrev AffineFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
/-- Infinity-chart fractional ideals in its canonical fraction field. -/
abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityPointSpread.InfinityFractionalIdeal
/-- The canonical affine integral lattice attached to a generic Mumford
graph.  Keeping the contraction as an ordinary ideal makes it directly
usable as the affine component of a two-chart line. -/
def finiteAffineIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal AffineCurve :=
  N13IntegralModelContraction.contractIdeal
    (N13CanonicalContractionQuotient.graphIdeal D)
/-! ## Integral affine point lines -/
/-! ## Finite quadratic lines -/
end
end MazurProof.N13FiniteAffineTwoChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread =====
section
/-!
# The generic class of an escaping degree-one point line

For a nonintegral affine point `(x,y)` on the good two-adic model, the
infinity lift has coordinates `t=x⁻¹` and `v=t³y`.  The two-chart line
constructed from this integral point has affine graph

`(1-tX, Y-vX³)`.

After passing to the generic fibre, its first generator is a unit multiple
of `X-x`, and its completed-square ordinate agrees modulo `X-x` with the
standard sextic ordinate `2y+h(x)`.  Hence the generic fibre is exactly the
usual degree-one Mumford point ideal.

For an integral affine point, the finite-support closure theorem instead
contracts the overlap ideal onto the infinity chart.  Together the two
constructions give a proper two-chart line for every selected degree-one
graph.
-/
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13EscapingDegreeOneSpread.instFactPrimeOfNatNat_fLT
def lift
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    PInf :=
  N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
def genericU
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Q₂[X] :=
  N13TwoAdicCoordinateBaseChange.mapPoly
    (N13IntegralInfinityPointSpread.affineU
      (lift x y hx hxy))
def genericV
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Q₂[X] :=
  N13GoodSexticMumfordTransport.completedGraph
    (N13TwoAdicCoordinateBaseChange.mapPoly
      (N13IntegralInfinityPointSpread.affineV
        (lift x y hx hxy)))
end
end MazurProof.N13EscapingDegreeOneSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoChartLineTensor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoChartLineTensor =====
section
/-!
# Tensor products of explicit N13 two-chart lines

The ordinary affine and infinity presentations of a line multiply
chartwise.  Ideal extension commutes with multiplication, so the overlap
compatibility is preserved.  This turns the explicit escaping point lines
into proper spreads of split effective divisors without constructing a
Picard functor.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
attribute [local instance] MazurProof.N13TwoChartLineTensor.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
/-! ## The two rational points at infinity -/
/-- The positive point at infinity in the good chart, with coordinates
`t = 0` and `v = 0`. -/
def infinityPlusPoint : IntegralInfinityPoint :=
  ⟨(0, 0), by
    norm_num [N13GoodModelTwo.InfinityChartEquation]⟩
/-- The negative point at infinity in the good chart, with coordinates
`t = 0` and `v = -1`. -/
def infinityMinusPoint : IntegralInfinityPoint :=
  ⟨(0, -1), by
    norm_num [N13GoodModelTwo.InfinityChartEquation]⟩
/-- The linear graph through two points with distinct horizontal
coordinates. -/
def secantV
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂[X] :=
  C z₁ +
    C ((z₂ - z₁) * (x₂ - x₁)⁻¹) * (X - C x₁)
end
end MazurProof.N13TwoChartLineTensor
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCurveOverlap =====
section
/-!
# The special algebraic overlap of the two N13 charts

This file begins the special, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
abbrev AffineCurve : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing
abbrev CoordinateRing : Type :=
  N13SpecialInfinityChart.CoordinateRing
def xClass : AffineCurve :=
  N13GoodCoordinateRingTwo.xClass X
def yClass : AffineCurve :=
  N13GoodCoordinateRingTwo.yClass
abbrev AffineOverlap : Type :=
  Localization.Away xClass
abbrev InfinityOverlap : Type :=
  Localization.Away N13SpecialInfinityChart.tClass
def tOverlap : InfinityOverlap :=
  algebraMap CoordinateRing InfinityOverlap
    N13SpecialInfinityChart.tClass
def xOverlap : InfinityOverlap :=
  IsLocalization.Away.invSelf N13SpecialInfinityChart.tClass
def vOverlap : InfinityOverlap :=
  algebraMap CoordinateRing InfinityOverlap
    N13SpecialInfinityChart.vClass
@[simp] theorem tOverlap_mul_xOverlap :
    tOverlap * xOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := InfinityOverlap)
      N13SpecialInfinityChart.tClass
theorem xOverlap_isUnit :
    IsUnit xOverlap := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨tOverlap, ?_⟩
  rw [mul_comm]
  exact tOverlap_mul_xOverlap
def coefficientToInfinityOverlap : K →+* InfinityOverlap :=
  (algebraMap CoordinateRing InfinityOverlap).comp
    ((algebraMap Base CoordinateRing).comp
      (Polynomial.C : K →+* Base))
def affineCoeffMap : K[X] →+* InfinityOverlap :=
  Polynomial.eval₂RingHom coefficientToInfinityOverlap xOverlap
def affineYImage : InfinityOverlap :=
  xOverlap ^ 3 * vOverlap
@[simp] theorem affineCoeffMap_rhsPoly :
    affineCoeffMap
        (N13GoodCoordinateRingTwo.rhsPoly) =
      xOverlap ^ 5 + xOverlap ^ 4 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GoodCoordinateRingTwo.rhsPoly]
/-! ## The reverse chart map -/
def xAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap xClass
def tAffineOverlap : AffineOverlap :=
  IsLocalization.Away.invSelf xClass
def yAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap yClass
@[simp] theorem xAffineOverlap_mul_tAffineOverlap :
    xAffineOverlap * tAffineOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := AffineOverlap) xClass
theorem tAffineOverlap_isUnit :
    IsUnit tAffineOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨xAffineOverlap,
      by simpa [mul_comm] using xAffineOverlap_mul_tAffineOverlap⟩
def coefficientToAffineOverlap : K →+* AffineOverlap :=
  (algebraMap AffineCurve AffineOverlap).comp
    ((AdjoinRoot.of
      (N13GoodCoordinateRingTwo.curvePoly)).comp
        (Polynomial.C : K →+* K[X]))
def infinityCoeffMap : Base →+* AffineOverlap :=
  Polynomial.eval₂RingHom
    coefficientToAffineOverlap tAffineOverlap
def infinityVImage : AffineOverlap :=
  tAffineOverlap ^ 3 * yAffineOverlap
@[simp] theorem infinityCoeffMap_rhsPoly :
    infinityCoeffMap N13SpecialInfinityChart.rhsPoly =
      tAffineOverlap + tAffineOverlap ^ 2 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13SpecialInfinityChart.rhsPoly]
end
end MazurProof.N13SpecialCurveOverlap
end

end

-- ===== FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility =====
section
-- ===== FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility =====
section
/-!
# Reduction commutes with the N13 two-chart overlap

The ordinary affine and infinity reductions extend to their distinguished
principal opens.  The two resulting squares commute with the ordinary and
special overlap equivalences.

Everything is proved from localization and `AdjoinRoot` universal
properties.  No pointwise calculation on either special chart is used.
-/
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13OverlapReductionCompatibility.instFactPrimeOfNatNat_fLT
abbrev OrdinaryInfinity :=
  N13OrdinaryCurveOverlap.InfinityCurve
abbrev OrdinaryInfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap
abbrev SpecialAffine :=
  N13SpecialCurveOverlap.AffineCurve
abbrev SpecialInfinity :=
  N13SpecialCurveOverlap.CoordinateRing
abbrev SpecialAffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap
abbrev SpecialInfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap
/-- Affine reduction followed by restriction to the special principal
open. -/
def affineReduceToOverlap :
    OrdinaryAffine →+* SpecialAffineOverlap :=
  (algebraMap SpecialAffine SpecialAffineOverlap).comp
    N13GeneralizedMumfordReduction.reduceCoordinate
@[simp] theorem affineReduceToOverlap_x :
    affineReduceToOverlap N13OrdinaryCurveOverlap.xClass =
      algebraMap SpecialAffine SpecialAffineOverlap
        N13SpecialCurveOverlap.xClass := by
  simp [affineReduceToOverlap,
    N13OrdinaryCurveOverlap.xClass,
    N13SpecialCurveOverlap.xClass,
    RingHom.comp_apply,
    N13GeneralizedMumfordReduction.reducePoly]
theorem affine_x_mapsToUnit :
    IsUnit
      (affineReduceToOverlap
        N13OrdinaryCurveOverlap.xClass) := by
  rw [affineReduceToOverlap_x]
  exact
    IsLocalization.Away.algebraMap_isUnit
      N13SpecialCurveOverlap.xClass
/-- Reduction on the affine distinguished principal open. -/
def reduceAffineOverlap :
    OrdinaryAffineOverlap →+* SpecialAffineOverlap :=
  IsLocalization.Away.lift
    N13OrdinaryCurveOverlap.xClass
    affine_x_mapsToUnit
@[simp] theorem reduceAffineOverlap_algebraMap
    (z : OrdinaryAffine) :
    reduceAffineOverlap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      affineReduceToOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13OrdinaryCurveOverlap.xClass
      affine_x_mapsToUnit z
/-- Restriction to the affine principal open commutes with reduction. -/
theorem reduceAffineOverlap_comp_algebraMap :
    reduceAffineOverlap.comp
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap) =
      (algebraMap SpecialAffine SpecialAffineOverlap).comp
        N13GeneralizedMumfordReduction.reduceCoordinate := by
  apply RingHom.ext
  intro z
  change
    reduceAffineOverlap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      algebraMap SpecialAffine SpecialAffineOverlap
        (N13GeneralizedMumfordReduction.reduceCoordinate z)
  rw [reduceAffineOverlap_algebraMap]
  rfl
/-- Infinity reduction followed by restriction to the special principal
open. -/
def infinityReduceToOverlap :
    OrdinaryInfinity →+* SpecialInfinityOverlap :=
  (algebraMap SpecialInfinity SpecialInfinityOverlap).comp
    N13IntegralInfinityReduction.reduceCoordinate
@[simp] theorem infinityReduceToOverlap_t :
    infinityReduceToOverlap
        N13IntegralInfinityChart.tClass =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        N13SpecialInfinityChart.tClass := by
  simp [infinityReduceToOverlap, RingHom.comp_apply]
theorem infinity_t_mapsToUnit :
    IsUnit
      (infinityReduceToOverlap
        N13IntegralInfinityChart.tClass) := by
  rw [infinityReduceToOverlap_t]
  exact
    IsLocalization.Away.algebraMap_isUnit
      N13SpecialInfinityChart.tClass
/-- Reduction on the infinity distinguished principal open. -/
def reduceInfinityOverlap :
    OrdinaryInfinityOverlap →+* SpecialInfinityOverlap :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_t_mapsToUnit
@[simp] theorem reduceInfinityOverlap_algebraMap
    (z : OrdinaryInfinity) :
    reduceInfinityOverlap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      infinityReduceToOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13IntegralInfinityChart.tClass
      infinity_t_mapsToUnit z
/-- Restriction to the infinity principal open commutes with reduction. -/
theorem reduceInfinityOverlap_comp_algebraMap :
    reduceInfinityOverlap.comp
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap) =
      (algebraMap SpecialInfinity SpecialInfinityOverlap).comp
        N13IntegralInfinityReduction.reduceCoordinate := by
  apply RingHom.ext
  intro z
  change
    reduceInfinityOverlap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        (N13IntegralInfinityReduction.reduceCoordinate z)
  rw [reduceInfinityOverlap_algebraMap]
  rfl
end
end MazurProof.N13OverlapReductionCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoChartSpecialRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoChartSpecialRestriction =====
section
/-!
# Chartwise special restriction of proper N13 lines

A `TwoChartLine` is an invertible ideal on each ordinary chart together with
literal equality after extension to their common overlap.  Reducing both chart
ideals modulo two preserves that overlap equality because the ordinary and
special overlap maps form a commutative square.

This construction deliberately retains both reduced ideals.  It is the
ring-theoretic restriction datum needed before identifying the special fibre
with a concrete effective divisor; it does not assert a general sheaf-descent
theorem that is absent from the pinned Mathlib API.
-/
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoChartSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Coordinate ring of the reduced ordinary affine chart. -/
abbrev SpecialAffine : Type :=
  N13GeneralizedMumfordReduction.SpecialRing
/-- Coordinate ring of the reduced infinity chart. -/
abbrev SpecialInfinity : Type :=
  N13IntegralInfinityReduction.SpecialRing
end
end MazurProof.N13TwoChartSpecialRestriction
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
/-!
# Canonical special-chart ideals of degree-two divisors

The completed special N13 curve is covered by its ordinary affine chart and
its infinity chart.  A finite point with horizontal coordinate zero is absent
from the overlap, a finite point with horizontal coordinate one lies on both
charts, and an infinity point is absent from the ordinary affine chart.

This file assigns to every completed point its compatible pair of chart
ideals.  Products of two point pairs then descend through the symmetric square
to give canonical chart ideals for every effective divisor of degree two.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The special affine coordinate ring. -/
abbrev SpecialAffine : Type :=
  N13TwoChartSpecialRestriction.SpecialAffine
/-- The special infinity-chart coordinate ring. -/
abbrev SpecialInfinity : Type :=
  N13TwoChartSpecialRestriction.SpecialInfinity
/-- The common special overlap ring. -/
abbrev SpecialOverlap : Type :=
  N13SpecialCurveOverlap.InfinityOverlap
end
end MazurProof.N13SpecialDivisorCharts
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoChartPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoChartPicardRealization =====
section
/-!
# Two-fibre Picard realization of proper N13 lines

Mathlib does not currently descend the two chart ideals of a `TwoChartLine`
to a global invertible sheaf on the glued curve.  The N13 endgame needs less:
an oriented generic fractional ideal and a literal degree-two divisor on the
special fibre.

The structure in this file retains precisely that rigorous ring-level data.
Its two special equalities compare both reduced chart ideals with the
canonical chart pair of one effective divisor.  The generic and special
Picard classes are consequently definitions, rather than hypothesized class
maps.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoChartPicardRealization.instFactPrimeOfNatNat_fLT
/-- The oriented generic Picard group used by the N13 Mumford model. -/
abbrev GenericPic : Type :=
  SexticMumford.ConcretePic
    Model
    (N13Infinity.positiveInfinityOrder Q₂)
/-- Algebra structure used to extend an integral fractional ideal to the
generic sextic coordinate ring. -/
local instance integralRationalAlgebra :
    Algebra N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
namespace Data
end Data
end
end MazurProof.N13TwoChartPicardRealization
end

end

-- ===== FLT.Assumptions.MazurProof.N13CoherentChartComparison =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CoherentChartComparison =====
section
/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate only. Lean elaboration / build / axiom checks: NOT RUN.
A denominator-cleared, two-chart principal comparison. Existence is not asserted.
-/
namespace MazurProof.N13CoherentChartComparison
noncomputable section
attribute [local instance] MazurProof.N13CoherentChartComparison.instFactPrimeOfNatNat_fLT
abbrev A := N13IntegralGraphJacobian.IntegralRing
abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
abbrev As := N13TwoChartSpecialRestriction.SpecialAffine
abbrev Bs := N13TwoChartSpecialRestriction.SpecialInfinity
abbrev Os := N13SpecialCurveOverlap.InfinityOverlap
/-- Reduction preserves a denominator-cleared equality of invertible ideals.
No assertion about lifting a special rational function is made. -/
theorem map_cleared_ideal_eq
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (I J : Ideal R)
    (h : Ideal.span ({a} : Set R) * I = Ideal.span ({b} : Set R) * J) :
    Ideal.span ({f a} : Set S) * Ideal.map f I =
      Ideal.span ({f b} : Set S) * Ideal.map f J := by
  have hm := congrArg (Ideal.map f) h
  simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using hm
end
end MazurProof.N13CoherentChartComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13PrimitiveChartTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13PrimitiveChartTransport =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Transport an affine numerator and denominator with nonzero reductions to
the ordinary infinity chart without losing their reductions. Both chart
fractions are proved equal by an exact overlap cross-product equation.
No equality of line ideals is assumed or claimed in this transport lemma.
-/
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13PrimitiveChartTransport.instFactPrimeOfNatNat_fLT
abbrev B := N13OrdinaryCurveOverlap.InfinityCurve
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
abbrev As := N13SpecialCurveOverlap.AffineCurve
abbrev Bs := N13SpecialCurveOverlap.CoordinateRing
abbrev Os := N13SpecialCurveOverlap.InfinityOverlap
abbrev AOs := N13SpecialCurveOverlap.AffineOverlap
theorem special_x_ne_zero : N13SpecialCurveOverlap.xClass ≠ 0 :=
  N13GoodCoordinateRingTwo.xClass_ne_zero Polynomial.X_ne_zero
instance instIsDomainAOs : IsDomain AOs :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors special_x_ne_zero)
end
end MazurProof.N13PrimitiveChartTransport
end

end

-- ===== FLT.Assumptions.MazurProof.N13EffectiveInfinityRepair =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13EffectiveInfinityRepair =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Move the balanced upper wall by an actual Cantor principal relation. The
result lies in the effective degree-two chamber relative to two copies of
positive infinity. This does not assert an integral chart extension theorem.
-/
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MazurProof.N13EffectiveInfinityRepair.instDecidableEq_fLT
open SexticMumford N13MumfordInfinityBalance
open Polynomial
/-- The only balanced inputs outside the effective chamber are on the
upper wall d + nInf = 2. One positive-branch cubic Cantor step repairs
all of them, changing the affine polynomial and its principal relation. -/
def repair (D : N13Mumford.Mumford K) : N13Mumford.SemiMumford K :=
  if D.u.natDegree + D.nInf = 2 then plusStep D.toSemi else D.toSemi
end
end MazurProof.N13EffectiveInfinityRepair
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts =====
section
/-!
# Chart ideals of special N13 graph divisors

A smooth quadratic generalized Mumford graph on the characteristic-two
N13 fibre splits into two graph points.  This file proves that the product
of their canonical affine point ideals is exactly the original Mumford
ideal.

For distinct roots this is the graph-ideal Chinese remainder theorem.  For
a repeated root, the vertical derivative is the everywhere nonzero
polynomial `h = X³ + X + 1` on `F₂`; this identifies the tangent graph ideal
with the square of the point ideal.  Thus the result retains multiplicity
without enumerating effective divisors.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
open N13GoodCoordinateRingTwo
/-- The monic quadratic attached to an unordered pair of roots. -/
def rootPolynomial : Sym2 K → K[X] :=
  Sym2.lift
    ⟨fun a b => (X - C a) * (X - C b),
      fun a b => by
        dsimp
        rw [mul_comm]⟩
@[simp] theorem rootPolynomial_mk (a b : K) :
    rootPolynomial s(a, b) =
      (X - C a) * (X - C b) :=
  rfl
end
end MazurProof.N13SpecialGraphDivisorCharts
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph =====
section
/-!
# Constant vertical graphs on the special infinity chart

When a vertical relation specializes to the constant equation `t = a`, its
monic quadratic ordinate equation is forced by the special curve equation
to be `v²+v`.  Thus the vertical graph ideal is just the principal fibre
ideal `(t-a)`, and its divisor is the canonical pair of the two sheets over
that base point.  This calculation treats both `t=0` and `t=1` uniformly.
-/
open Polynomial
namespace MazurProof.N13SpecialConstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The special infinity coordinate ring. -/
abbrev Ring := N13SpecialDivisorCharts.SpecialInfinity
/-- The vertical graph ideal `(m(v),t-a)` on the special infinity chart. -/
def verticalIdeal (m : K[X]) (a : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13SpecialInfinityChart.vClass m,
      N13SpecialInfinityChart.tClass -
        algebraMap K[X] Ring (C a)} : Set Ring)
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineVerticalGraph =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineVerticalGraph =====
section
/-!
# Vertical graphs on the special affine chart

A rank-two affine quotient with basis `{1,y}` is cut out by a monic
quadratic `m(y)` and a linear relation `x=a+cy`.  Over `F₂` the reduced
slope is either zero or one.

For slope zero, the curve equation forces `m=y²+y`, and the graph ideal is
the principal fibre ideal `(x-a)`.  For slope one, the involution
`y=x+a` turns the vertical graph into the horizontal graph
`m(x+a)=0, y=x+a`.  This file proves both ideal identities and packages the
nonconstant branch as regular special Mumford data.
-/
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The special affine coordinate ring. -/
abbrev Ring :=
  N13GoodCoordinateRingTwo.CoordinateRing
/-- The special vertical graph ideal
`(m(y),x-(a+cy))`. -/
def verticalIdeal (m : K[X]) (a c : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13GoodCoordinateRingTwo.yClass m,
      N13GoodCoordinateRingTwo.xClass X -
        aeval N13GoodCoordinateRingTwo.yClass
          (C a + C c * X)} : Set Ring)
/-- Translation by an `F₂` coordinate is involutive. -/
theorem translateLinear_comp_translateLinear (a : K) :
    (C a + X).comp (X + C a) = X := by
  have haa : a + a = 0 := by
    fin_cases a <;> decide
  simp only [add_comp, C_comp, X_comp]
  calc
    C a + (X + C a) = X + (C a + C a) := by ring
    _ = X := by rw [← C_add, haa]; simp
/-- Translation by `a` on special affine polynomials. -/
def translate (a : K) (p : K[X]) : K[X] :=
  p.comp (X + C a)
end
end MazurProof.N13SpecialAffineVerticalGraph
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinitySaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinitySaturation =====
section
/-!
# Saturated infinity ideals on the special N13 overlap

The special infinity and affine charts meet on the principal open where
`t` is invertible.  If `t` is already a unit modulo an infinity ideal, then
extension to the overlap and contraction loses no information.  This is the
infinity-chart counterpart of `N13SpecialAffineSaturation`.

Finite affine closures acquire this property from the reflected monic
equation used in their construction.  Canonical divisors of finite special
graphs acquire it point by point: a root at `x=0` contributes the unit ideal,
and a root at `x=1` contributes the relation `t=1`.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinitySaturation.instFactPrimeOfNatNat_fLT
/-- The special infinity coordinate ring. -/
abbrev InfinityCurve :=
  N13SpecialCurveOverlap.CoordinateRing
/-- The common special overlap ring. -/
abbrev InfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap
/-- The infinity coordinate is a unit in the quotient by `I`. -/
def TUnitMod (I : Ideal InfinityCurve) : Prop :=
  ∃ q : InfinityCurve,
    1 - N13SpecialInfinityChart.tClass * q ∈ I
end
end MazurProof.N13SpecialInfinitySaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction =====
section
/-!
# Special restriction of finite irreducible N13 quadratics

A finite canonical contraction is finite flat of rank two.  The existing
coordinate-basis theorem chooses either the literal basis `{1,x}` or
`{1,y}`.  The first basis recovers an integral horizontal semigraph; the
second recovers an integral vertical graph.

After reduction, a horizontal graph gives its canonical special root
divisor.  A vertical graph has reduced slope zero or one: slope zero gives
the canonical two-sheet fibre over `x=a`, while slope one translates to a
horizontal graph.  In every case the reduced affine ideal is canonical.
The reflected monic equation makes `t` invertible modulo the source
infinity closure, and the same property holds for the target finite
divisor.  Infinity-chart saturation therefore upgrades the affine equality
to equality of the complete chart pair.
-/
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Integral vertical graph data recovered from a `{1,y}` basis. -/
abbrev VerticalGraph :=
  N13RankTwoVerticalGraphRecovery.VerticalGraph
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation =====
section
/-!
# Vertical saturation of reflected N13 infinity graphs

A monic graph on the integral infinity chart has quotient
`R₂[X] / (u)`, hence its quotient has no torsion from a nonzero base
scalar.  For a monic quadratic `u`, weighted reflection also makes the
affine coordinate `x` a unit modulo the reflected graph ideal.  These two
facts, together with equality on the ordinary overlap, show that the
reflected affine ideal is the canonical vertical contraction of its
generic fibre.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphSaturation.instFactPrimeOfNatNat_fLT
abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap
abbrev GraphData : Type :=
  N13IntegralInfinityGraphJacobian.GraphData
local instance integralRationalAlgebra :
    Algebra N13IntegralModelContraction.IntegralRing
      N13IntegralModelContraction.RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
abbrev GraphResidue (D : GraphData) : Type :=
  Base ⧸ Ideal.span ({D.u} : Set Base)
theorem graph_root_relation
    (D : GraphData) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v) = 0 := by
  change
    (X ^ 2 +
          C N13IntegralInfinityChart.hBase * X -
        C N13IntegralInfinityChart.rhsBase).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base))
      (D.v ^ 2 +
        N13IntegralInfinityChart.hBase * D.v -
        N13IntegralInfinityChart.rhsBase) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩
def graphEval (D : GraphData) :
    InfinityCurve →+* GraphResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) D.v)
    (graph_root_relation D)
/-- The affine coordinate is a unit in the quotient by `I`. -/
def XUnitMod (I : Ideal AffineCurve) : Prop :=
  ∃ q : AffineCurve,
    1 - q * N13OrdinaryCurveOverlap.xClass ∈ I
end
end MazurProof.N13IntegralInfinityGraphSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphJacobian =====
section
/-!
# Vertical graph ideals on the N13 infinity chart

A rank-two quotient whose integral basis is `{1,v}` is cut out by a monic
relation `m(v)` and a linear equation `t = a + c v`.  Substitution into the
infinity-chart equation produces the complementary factor.  Explicit
divided differences decompose both global Jacobian rows in this vertical
graph frame, so the generic decomposition theorem proves invertibility.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphJacobian.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev FunctionField : Type :=
  N13IntegralInfinityGraphJacobian.FunctionField
abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityGraphJacobian.InfinityFractionalIdeal
namespace VerticalGraph
end VerticalGraph
open N13IntegralInfinityGraphJacobian
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart =====
section
/-!
# Two-chart closure of a vertical N13 infinity graph

A recovered vertical graph has infinity ideal

`(m(v), t - (a + c v))`.

After the substitutions `t=x⁻¹` and `v=x⁻³y`, clearing weights gives the
affine generators `x⁶m(x⁻³y)` and
`x³(t-a-cv) = x²-a x³-cy`.  The direct reciprocal kernel also contains a
monic quadratic equation in `t`; its weighted reflection has constant
coefficient one.  Adding this third, redundant overlap generator keeps the
affine support inside `D(x)`.

The infinity ideal is invertible on `D(x)`.  The principal-localization
patching theorem then proves that the three-generated affine closure is
invertible globally.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphTwoChart.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve
abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13RankTwoInfinityVerticalGraphRecovery =====
section
-- ===== FLT.Assumptions.MazurProof.N13RankTwoInfinityVerticalGraphRecovery =====
section
/-!
# Rank-two vertical recovery on the N13 infinity chart

The ordinary infinity ring has the polynomial normal form
`p(t) + q(t)v`.  If a quotient has literal two-adic basis `{1,v}`, then
multiplication by `v` recovers a monic quadratic `m(v)` and the class of
`t` is a linear polynomial `a+cv`.  The generic vertical ideal-recovery
theorem identifies the original ideal with this graph, while the curve
equation supplies its complementary factor.
-/
open Module
open Polynomial
namespace MazurProof.N13RankTwoInfinityVerticalGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13RankTwoInfinityVerticalGraphRecovery.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
end
end MazurProof.N13RankTwoInfinityVerticalGraphRecovery
end

end

-- ===== FLT.Assumptions.MazurProof.N13RankTwoInfinityGraphRecovery =====
section
-- ===== FLT.Assumptions.MazurProof.N13RankTwoInfinityGraphRecovery =====
section
/-!
# Rank-two horizontal recovery on the N13 infinity chart

A quotient basis `{1,t}` recovers a monic quadratic horizontal relation
and a linear ordinate.  The infinity curve equation then supplies the
Cantor quotient, so the original ideal is literally a bounded integral
infinity semigraph.
-/
open Module
open Polynomial
namespace MazurProof.N13RankTwoInfinityGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13RankTwoInfinityGraphRecovery.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev GraphData : Type :=
  N13IntegralInfinityGraphTwoChart.GraphData
end
end MazurProof.N13RankTwoInfinityGraphRecovery
end

end

-- ===== FLT.Assumptions.MazurProof.N13AllPointAffineSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AllPointAffineSpread =====
section
/-!
# Affine integral spreads of all two-adic N13 points

An affine point of the good model has two structural integral
presentations.  If its horizontal coordinate is integral, use its monic
affine graph.  If it has negative valuation, use the affine half of its
explicit infinity-chart point line.  Both presentations are invertible
integral fractional ideals with exactly the standard sextic point ideal as
generic fibre.

Tensoring the two alternatives closes every split quadratic graph with
distinct roots, independently of the valuations of those roots.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13AllPointAffineSpread
noncomputable section
attribute [local instance] MazurProof.N13AllPointAffineSpread.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra IntegralRing N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
end
end MazurProof.N13AllPointAffineSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction =====
section
-- ===== FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction =====
section
/-!
# The reciprocal N13 divisor on the integral infinity chart

For a quadratic generic Mumford graph with nonzero constant coefficient,
the class of the affine coordinate is invertible in its graph quotient.
Its explicit inverse is the infinity coordinate `t`, and `t³y` is the
ordinary infinity ordinate.  The ordinary overlap identity therefore
defines a canonical map from the integral infinity chart into the original
generic Mumford quotient.  Its kernel is the integral infinity ideal used
for rank-two recovery.
-/
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
abbrev InfinityRing : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev SpecialRing : Type :=
  N13SpecialInfinityChart.CoordinateRing
local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13IntegralInfinityReduction.reduceBase.toAlgebra
def reduceInfinityQuotient
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    InfinityRing ⧸ I →+* SpecialRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13IntegralInfinityReduction.reduceCoordinate I J hmap
@[simp] theorem reduceInfinityQuotient_mk
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J)
    (z : InfinityRing) :
    reduceInfinityQuotient I J hmap (Ideal.Quotient.mk I z) =
      Ideal.Quotient.mk J
        (N13IntegralInfinityReduction.reduceCoordinate z) :=
  rfl
end
end MazurProof.N13ReciprocalInfinityContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction =====
section
/-!
# Contraction of a vertical N13 infinity graph

The direct reciprocal kernel maps the integral infinity chart into the
original Mumford quotient.  Since the infinity coordinate `t` maps to a
unit, this map extends to the ordinary overlap.  Its kernel there is the
extension of the direct kernel.

For a recovered vertical graph, the three-generated affine closure has the
same overlap ideal and already makes `x` a unit modulo the ideal.  Contracting
from the overlap therefore identifies this affine closure with the canonical
vertical contraction of the original generic Mumford ideal.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphContraction.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve
abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap
/-- The affine integral model maps to the original Mumford quotient by
generic coefficient extension followed by quotient projection. -/
def affineToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    AffineCurve →+* GenericQuotient D :=
  (Ideal.Quotient.mk
      (N13ReciprocalInfinityContraction.genericIdeal D)).comp
    N13TwoAdicCoordinateBaseChange.integralToSextic
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineSaturation =====
section
/-!
# Saturated affine ideals on the special N13 overlap

The special affine and infinity charts meet on the principal open where
`x` is invertible.  If `x` is already a unit modulo an affine ideal, then
localizing at `x` loses no information: the original ideal is the contraction
of its extension to the overlap.

This gives a useful uniqueness principle for special divisors.  Two compatible
chart pairs with the same infinity ideal and `x`-saturated affine ideals have
the same affine ideal, so the infinity calculation alone determines the whole
pair.
-/
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- The special affine coordinate ring. -/
abbrev AffineCurve :=
  N13SpecialCurveOverlap.AffineCurve
/-- The special affine-to-infinity overlap ring. -/
abbrev InfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap
end
end MazurProof.N13SpecialAffineSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts =====
section
/-!
# Chart ideals of special infinity-graph divisors

This file identifies the canonical two-chart ideals of the degree-two
divisor obtained from a monic graph on the special infinity chart.  The
key local calculation treats a repeated root directly: the square of the
point ideal equals the quadratic graph ideal because the curve coefficient
`h∞(a)` is a unit at every `F₂`-rational root.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
abbrev Ring := N13SpecialDivisorCharts.SpecialInfinity
/-- The special infinity coordinate ring receives polynomials in `t`. -/
def xClassHom : K[X] →+* Ring :=
  AdjoinRoot.of N13SpecialInfinityChart.curvePoly
/-- The class of the infinity-chart vertical coordinate. -/
def yClass : Ring :=
  N13SpecialInfinityChart.vClass
/-- The coordinate-ring class of `v∞ - v(t)`. -/
def ySubClass (v : K[X]) : Ring :=
  GeneralizedGraphIdealCore.ySubClass xClassHom yClass v
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialNonconstantInfinityVerticalGraph =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialNonconstantInfinityVerticalGraph =====
section
/-!
# Nonconstant vertical graphs on the special infinity chart

In the nonconstant residue branch a vertical relation has the form
`t=a+v`.  Characteristic two makes this affine change of variable
involutive: `v=t+a`.  Consequently the vertical graph

`m(v)=0,  t=a+v`

is the same closed subscheme as the horizontal graph

`m(t+a)=0,  v=t+a`.

This file carries out that change of variables inside the special coordinate
ring and packages the translated equations as the monic horizontal graph data
already handled by the completed-root divisor construction.
-/
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The special infinity coordinate ring. -/
abbrev Ring :=
  N13SpecialDivisorCharts.SpecialInfinity
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityNormCarrier =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityNormCarrier =====
section
/-!
# The explicit N13 norm carrier at infinity

For the integral N13 equation

`y² + h(x)y = r(x)`,

the hyperelliptic conjugate of `P(x) + Q(x)y` is
`P(x) - Q(x)h(x) - Q(x)y`.  Their product is the polynomial

`P² - hPQ - rQ²`

evaluated at `x`.  Thus one affine ideal section whose two normalized
infinity branches are units can later be converted into a monic polynomial
contained in the ideal by inspecting the leading coefficient of this norm.

This file records the equation-level algebra only.  It makes no properness,
Mumford-graph, or branch-unit assumption.
-/
open Polynomial
namespace MazurProof.N13InfinityNormCarrier
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- The polynomial norm of the affine normal form `P(x)+Q(x)y`. -/
def normPoly (P Q : R[X]) : R[X] :=
  P ^ 2 -
    N13GeneralizedMumfordIntegral.hPoly * P * Q -
      N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2
end
end MazurProof.N13InfinityNormCarrier
end

end

-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread =====
section
/-!
# Proper spreads for irreducible N13 quadratics

An irreducible quadratic Mumford graph lies in one of the two ordinary
proper charts.  In the finite branch, a monic equation in the finite
quotient patches the canonical affine contraction across the infinity
uniformizer.  In the escaping branch, the literal integral reciprocal
equation gives a horizontal or vertical infinity graph.  Both cases now
produce an invertible two-chart line with the exact generic graph ideal.
-/
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticSpread
noncomputable section
abbrev InfinityGraphData : Type :=
  N13IntegralInfinityGraphTwoChart.GraphData
end
end MazurProof.N13IrreducibleQuadraticSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityLineSpecialRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityLineSpecialRestriction =====
section
/-!
# Special restriction of the two N13 infinity point lines

The integral infinity-chart point ideal has generators
`t-t₀` and `v-v₀`.  Coefficientwise reduction therefore sends it exactly to
the corresponding special point ideal.  In particular, the positive
infinity line restricts to the sheet-zero point used as the special Abel
anchor.

This is an equality of both chart ideals, not merely an equality of their
images in the special Picard quotient.
-/
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Integral points on the ordinary infinity chart. -/
abbrev IntegralInfinityPoint : Type :=
  N13IntegralInfinityPointSpread.IntegralInfinityPoint
end
end MazurProof.N13InfinityLineSpecialRestriction
end

end

-- ===== FLT.Assumptions.MazurProof.N13FiniteAffinePointInfinityClosure =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteAffinePointInfinityClosure =====
section
/-!
# Infinity closure of finite affine N13 point lines

For an integral affine point `(a,b)`, the same section on the infinity chart
is cut out by the weighted equations

`1 - a t = 0` and `v - b t³ = 0`.

The first equation makes `t` invertible modulo the weighted ideal, with
inverse `a`.  Hence the ideal is already saturated with respect to `t`;
contracting its extension from the overlap introduces no extra component.
This identifies the abstract `infinityClosure` with the explicit weighted
point ideal and makes its special reduction computable.
-/
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- The ordinary infinity-chart coordinate ring. -/
abbrev InfinityCurve : Type :=
  N13FiniteAffineTwoChart.InfinityCurve
/-- The ordinary common overlap ring. -/
abbrev InfinityOverlap : Type :=
  N13FiniteAffineTwoChart.InfinityOverlap
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end

end

-- ===== FLT.Assumptions.MazurProof.N13EscapingPointPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13EscapingPointPicardRealization =====
section
/-!
# Picard realization of escaping degree-one N13 points

An escaping affine point is integral on the ordinary infinity chart.  Its
proper point line reduces to the canonical reduced infinity point.  Tensoring
once with the positive-infinity point line supplies the second special point
required by the degree-two Abel model, while preserving the generic affine
ideal exactly.

The explicit oriented integer is `-1`: a degree-one affine Mumford point has
`nInf = 0`, and `SexticMumford.mumfordRaw` records `nInf - 1`.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13EscapingPointPicardRealization.instFactPrimeOfNatNat_fLT
/-- The two-adic coefficient field used by the proper reduction and the
oriented generic Picard model. -/
abbrev Q₂ : Type :=
  N13EscapingPointSpecialRestriction.Q₂
end
end MazurProof.N13EscapingPointPicardRealization
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation =====
section
/-!
# Vertical saturation of split quadratic N13 spreads

The affine ideal of a two-chart line is invertible in the common function
field.  If two such ideals have no vertical scalar torsion, their product has
none either: multiply by the inverse of the first fractional ideal, cancel the
base scalar in the second ideal, and multiply the first ideal back.

Applying this cancellation theorem to the valuation-independent point-line
constructor proves vertical saturation of `pairLine`.  Coincident points are
allowed, so the result covers both split secants and repeated-root tangents.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
attribute [local instance] MazurProof.N13QuadraticTwoChartSpreadSaturation.instFactPrimeOfNatNat_fLT
local instance integralRationalAlgebra :
    Algebra A N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
abbrev Frac : Type := FractionalIdeal A⁰ K
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalInfinitySplit =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalInfinitySplit =====
section
/-!
# Splitting the N13 formal infinity chart

The two Hensel roots of the formal-infinity equation differ by a unit.
Evaluation on those roots therefore identifies every function in the
quadratic chart with its values on the two disjoint branches.  Injectivity
uses the normal form `a + bv`; surjectivity is explicit two-point
interpolation.
-/
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
attribute [local instance] MazurProof.N13FormalInfinitySplit.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve
open N13FormalInfinityBranches
end
end MazurProof.N13FormalInfinitySplit
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalOverlapSplit =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalOverlapSplit =====
section
/-!
# Splitting the punctured N13 formal overlap

The two Hensel branches remain disjoint after passing from power series to
Laurent series.  Evaluation therefore splits the actual quadratic
punctured-overlap algebra as a product of two Laurent-series rings.  The
explicit interpolation inverse is compatible with restriction from the
complete formal-infinity chart.
-/
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
attribute [local instance] MazurProof.N13FormalOverlapSplit.instFactPrimeOfNatNat_fLT
abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve
abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve
open N13FormalInfinityBranches
def includePowerBranches
    (z : Power × Power) : Laurent × Laurent :=
  (N13FormalInfinityChart.includePowerRing z.1,
    N13FormalInfinityChart.includePowerRing z.2)
end
end MazurProof.N13FormalOverlapSplit
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoInfinityRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoInfinityRestriction =====
section
/-!
# Restriction of N13 fractional ideals to the two infinity branches

The two Laurent expansions at infinity combine into a faithful map from the
N13 function field to the product of the two branch fields.  Consequently an
affine fractional ideal restricts canonically to a fractional submodule of
that product.  This construction uses the ideal itself, rather than a chosen
global generator.
-/
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13TwoInfinityRestriction
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-- Simultaneous restriction of affine functions to the two infinity
branches. -/
def coordinateToBranches :
    CoordinateRing K →+* BranchPair K :=
  (N13Infinity.coordinateToLaurent K).prod
    (N13InfinityMinus.coordinateToLaurentMinus K)
local instance branchPairAlgebra :
    Algebra (CoordinateRing K) (BranchPair K) :=
  (coordinateToBranches K).toAlgebra
end
end MazurProof.N13TwoInfinityRestriction
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicInfinityCompatibility =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicInfinityCompatibility =====
section
/-!
# Compatibility of the integral and rational N13 infinity branches

The two branches obtained by X-adic Hensel lifting over `ℤ₂` are the same
branches as the positive and negative Laurent expansions of the sextic
function field after extension to `ℚ₂`.  This identifies the integral
complete-chart lattices with the rational branch pair used to restrict
fractional ideals.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicInfinityCompatibility.instFactPrimeOfNatNat_fLT
/-- Coefficientwise extension of integral Laurent series. -/
def laurentMap : IntegralLaurent →+* RationalLaurent where
  toFun z := z.map coeffMap
  map_zero' := HahnSeries.map_zero coeffMap.toZeroHom
  map_one' := HahnSeries.map_one coeffMap.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add coeffMap.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul coeffMap.toNonUnitalRingHom
@[simp] theorem laurentMap_coeff
    (f : IntegralLaurent) (n : ℤ) :
    (laurentMap f).coeff n = coeffMap (f.coeff n) :=
  rfl
/-- Its quadratic conjugate. -/
def rationalBranchOne : RationalLaurent :=
  -hInfinityQ - rationalBranchZero
end
end MazurProof.N13TwoAdicInfinityCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13CuspCARelation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CuspCARelation =====
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
abbrev H13 :
    Subgroup (SexticMumford.OrientedFrac M13) :=
  (SexticMumford.principalOriented M13
    (N13Infinity.positiveInfinityOrder ℚ)).range
abbrev Q13 : Type :=
  SexticMumford.OrientedFrac M13 ⧸ H13
/-! ## Exact order at the positive infinity branch -/
/-! ## Pass the principal divisor to the oriented Picard quotient -/
end MazurProof.N13Arithmetic
end
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityChartMarking =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityChartMarking =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Tie the infinity marking to the actual ordinary infinity ideal by extending
that ideal into the two generic formal branch rings. This reads the chart
ideal itself, not the separately stored integer. The two infinity sections
and their tensor products are certified here.
-/
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13InfinityChartMarking.instFactPrimeOfNatNat_fLT
abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
theorem generic_map_of_integral
    (f : B →+* P) (I : Ideal B) (n : ℕ)
    (h : Ideal.map f I = Ideal.span ({PowerSeries.X ^ n} : Set P)) :
    Ideal.map (N13TwoAdicInfinityCompatibility.powerMap.comp f) I =
      Ideal.span ({PowerSeries.X ^ n} : Set QP) := by
  rw [← Ideal.map_map, h, Ideal.map_span, Set.image_singleton]
  simp [N13TwoAdicInfinityCompatibility.powerMap]
end
end MazurProof.N13InfinityChartMarking
end

end

-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCompletionCompatibility =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCompletionCompatibility =====
section
/-!
# Compatibility of the ordinary and formal N13 overlaps

The ordinary infinity overlap is obtained by inverting `t`.  Composing the
ordinary infinity chart with its completion and the formal restriction sends
`t` to a Laurent unit, so the universal property of `Localization.Away`
gives a canonical map to the formal overlap.

This file proves that the resulting map agrees with both ordinary chart
restrictions.  No flatness, injectivity of completion, or algebraization
theorem is used.
-/
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13OrdinaryCompletionCompatibility.instFactPrimeOfNatNat_fLT
abbrev OrdinaryInfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve
abbrev OrdinaryOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap
abbrev FormalInfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve
abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve
end
end MazurProof.N13OrdinaryCompletionCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility =====
section
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility =====
section
/-!
# Base-change compatibility of the N13 affine restriction

There are two ways to restrict an integral affine function to the two
rational branches at infinity:

1. restrict it to the integral punctured formal chart, split the two Hensel
   branches, and extend coefficients from `ℤ₂` to `ℚ₂`;
2. pass to the good generic fibre, complete the square to the sextic model,
   and use the positive and negative rational Laurent expansions.

This file proves that the resulting square commutes.  The proof checks the
two genuine affine generators `x` and `y`, with polynomial naturality
handling all functions of `x`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAffineRestrictionCompatibility.instFactPrimeOfNatNat_fLT
def laurentMap : IntegralLaurent →+* RationalLaurent :=
  N13TwoAdicInfinityCompatibility.laurentMap
/-- Extend both integral Laurent branches coefficientwise to `ℚ₂`. -/
def laurentPairMap :
    IntegralBranchPair →+* RationalBranchPair :=
  ((laurentMap).comp
      (RingHom.fst IntegralLaurent IntegralLaurent)).prod
    ((laurentMap).comp
      (RingHom.snd IntegralLaurent IntegralLaurent))
@[simp] theorem laurentPairMap_apply
    (z : IntegralBranchPair) :
    laurentPairMap z =
      (laurentMap z.1, laurentMap z.2) :=
  rfl
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13OverlapBranchCompatibility =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OverlapBranchCompatibility =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The actual ordinary overlap has two faithful rational Laurent branch maps.
Their affine restrictions are the named function-field expansions; their
infinity restrictions are the inclusions of the named power-series maps.
Thus the primitive chart transport gives the SAME fraction on BOTH branches.
-/
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13OverlapBranchCompatibility.instFactPrimeOfNatNat_fLT
abbrev B := N13OrdinaryCurveOverlap.InfinityCurve
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
def includePower : QP →+* L := HahnSeries.ofPowerSeries ℤ Q₂
end
end MazurProof.N13OverlapBranchCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13InvertibleReductionSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InvertibleReductionSaturation =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for the integral principal-comparison seam.
Lean compilation and axiom checks: NOT RUN.

An invertible ideal with nonzero image in a domain-valued reduction is
saturated by the generator of the reduction kernel. This is a genuine
descent lemma; it assumes no Picard comparison or specialization law.
-/
namespace MazurProof.N13InvertibleReductionSaturation
noncomputable section
open scoped nonZeroDivisors
section General
variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing S] [IsDomain S]
end General
section TwoAdic
attribute [local instance] MazurProof.N13InvertibleReductionSaturation.instFactPrimeOfNatNat_fLT
variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R₂ A] [CommRing S] [IsDomain S]
end TwoAdic
section InfinityApplication
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13InvertibleReductionSaturation.instFactPrimeOfNatNat_fLT_1
abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
abbrev Bs := N13SpecialDivisorCharts.SpecialInfinity
end InfinityApplication
end
end MazurProof.N13InvertibleReductionSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13PrimitiveVerticalPresentation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13PrimitiveVerticalPresentation =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Mathlib pin: 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Krull intersection gives an actual primitive factorization of every
nonzero integral chart function. A rational function therefore has a
numerator and denominator with nonzero reductions after removing the two
explicit vertical powers. Transport to the other chart remains separate.
-/
namespace MazurProof.N13PrimitiveVerticalPresentation
noncomputable section
open scoped nonZeroDivisors
variable {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing S] [Nontrivial S]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
section N13Charts
attribute [local instance] MazurProof.N13PrimitiveVerticalPresentation.instFactPrimeOfNatNat_fLT
local instance instAlgebraAffineRationalRing : Algebra Affine N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
end N13Charts
end
end MazurProof.N13PrimitiveVerticalPresentation
end

end

-- ===== FLT.Assumptions.MazurProof.N13PrincipalBranchIdeals =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13PrincipalBranchIdeals =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Primitive presentations retain powers of two. These are Laurent-order-zero
scalars, so the SAME transported infinity numerator/denominator has the
prescribed difference of orders at both branches. Power-series division by
X^order turns the order equations into actual principal ideal equations.
-/
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13PrincipalBranchIdeals.instFactPrimeOfNatNat_fLT
local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
end
end MazurProof.N13PrincipalBranchIdeals
end

end

-- ===== FLT.Assumptions.MazurProof.N13PrimitiveAffineComparison =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13PrimitiveAffineComparison =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

A principal equality on the generic affine chart descends to the exact
primitive integral numerator/denominator equation. Powers of two removed
from a field presentation contribute unit ideals only on the generic fibre.
The integral descent uses proved saturation, not cancellation of integral
nonunits.
-/
namespace MazurProof.N13PrimitiveAffineComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InvertibleReductionSaturation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13PrimitiveAffineComparison.instFactPrimeOfNatNat_fLT
abbrev Frac := N13IntegralFractionalHull.RationalFractionalIdeal
local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
end
end MazurProof.N13PrimitiveAffineComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityBranchJets =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityBranchJets =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Finite-jet geometry for the actual ordinary N13 infinity chart and its two
named Hensel branch maps. The two roots differ by a unit. Consequently both
branch jets vanish exactly when the ordinary element is divisible by t^n.
-/
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13InfinityBranchJets.instFactPrimeOfNatNat_fLT
abbrev B := N13IntegralInfinityChart.InfinityCurve
abbrev base := N13IntegralInfinityReduction.integralBaseClass
end
end MazurProof.N13InfinityBranchJets
end

end

-- ===== FLT.Assumptions.MazurProof.N13GenericInfinityComparison =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GenericInfinityComparison =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Actual two-branch equality now yields the required approximation predicates
on the generic ordinary infinity chart. The vertical scalars are cancelled
only after localizing them. Combined with the actual principal open D(t),
this proves generic infinity-ideal equality.
-/
namespace MazurProof.N13GenericInfinityComparison
noncomputable section
open N13InfinityBranchJets N13InfinityIdealApproximation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GenericInfinityComparison.instFactPrimeOfNatNat_fLT
def verticalScalars : Submonoid B := (nonZeroDivisors R₂).map (algebraMap R₂ B)
abbrev GenericInfinity := Localization verticalScalars
def genericT : GenericInfinity := algebraMap B GenericInfinity N13IntegralInfinityChart.tClass
abbrev GenericOverlap := Localization.Away genericT
end
end MazurProof.N13GenericInfinityComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralPrincipalComparison =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralPrincipalComparison =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Transport the proved integral affine equation to the actual ordinary
overlap, then use the two actual branch equations to descend the infinity
equation. The final comparison uses one common primitive fraction.
-/
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralPrincipalComparison.instFactPrimeOfNatNat_fLT
local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
def infinityToGenericOverlap : B →+* GenericOverlap :=
  (algebraMap GenericInfinity GenericOverlap).comp (algebraMap B GenericInfinity)
theorem t_unit : IsUnit
    (infinityToGenericOverlap N13IntegralInfinityChart.tClass) :=
  IsLocalization.Away.algebraMap_isUnit genericT
def ordinaryToGenericOverlap : O →+* GenericOverlap :=
  IsLocalization.Away.lift N13IntegralInfinityChart.tClass t_unit
end
end MazurProof.N13IntegralPrincipalComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13MarkedTensorComparison =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MarkedTensorComparison =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

For the actual marked effective data constructed in this series, equality
of the generic class sums produces an integral two-chart tensor comparison.
No integral comparison, global specialization, branch compatibility, or
special additive law is assumed.
-/
namespace MazurProof.N13MarkedTensorComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13MarkedTensorComparison.instFactPrimeOfNatNat_fLT
local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
end
end MazurProof.N13MarkedTensorComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The proved raw, effective, saturated, and actual-branch properties are
packaged together without adding a comparison assumption. Equal generic
classes of certified data give an integral comparison. Every rational class
has such data, and the resulting choice already has integral tensor
comparisons. The three exact calibrations and named-point compatibility are
the remaining GlobalExistenceTarget assembly.
-/
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13EffectiveDataCompatibility.instFactPrimeOfNatNat_fLT
local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
abbrev G := N13RationalPointEndgame.G
end
end MazurProof.N13EffectiveDataCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpreadRationalPointReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpreadRationalPointReduction =====
section
/-!
# Assemble rational-point reduction from integral spreads

This is the thin geometric adapter between relation-first specialization
and the N13 rational-point endgame.  Its only point-specific hypothesis says
that the proper spread of a rational Abel divisor realizes the special Abel
class of the properly reduced point.
-/
namespace MazurProof.N13SpreadRationalPointReduction
noncomputable section
universe u
abbrev G : Type :=
  N13RationalPointEndgame.G
namespace Data
variable {Line : Type u}
end Data
end
end MazurProof.N13SpreadRationalPointReduction
end

end

-- ===== FLT.Assumptions.MazurProof.N13CoherentChooserSpecification =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CoherentChooserSpecification =====
section
/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate SPECIFICATION only. Lean elaboration / build / axiom checks: NOT RUN.
The imported candidate must be installed under FLT/Assumptions/MazurProof/.
No existence result for this structure is proved here.
-/
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section
abbrev G := N13RationalPointEndgame.G
end
end MazurProof.N13CoherentChooserSpecification
end

end

-- ===== FLT.Assumptions.MazurProof.N13CalibratedChooser =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CalibratedChooser =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Construct the exact calibrated Chooser from the actual marked effective
realizations and the proved integral comparisons. In particular the inverse
infinity value is the required existing C+A datum, with raw mark -2 and
actual branch multiplicities (0,0). GlobalExistenceTarget is unchanged.
-/
namespace MazurProof.N13CalibratedChooser
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13CalibratedChooser.instFactPrimeOfNatNat_fLT
def caMumford : N13Mumford.Mumford Q₂ where
  u := X * (X + 1)
  v := 1
  nInf := 0
  u_monic := by monicity!
  deg_u := by compute_degree!
  v_reduced := by
    have h2 : (X * (X + 1) : Q₂[X]).natDegree = 2 := by compute_degree!
    have hne : (X * (X + 1) : Q₂[X]) ≠ 0 := by
      intro h; rw [h, natDegree_zero] at h2; exact absurd h2 (by norm_num)
    rw [Polynomial.mod_eq_self_iff hne, degree_one, degree_eq_natDegree hne, h2]
    exact_mod_cast (by norm_num : (0 : ℕ) < 2)
  curve_dvd := by
    refine ⟨X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X + 2, ?_⟩
    change N13Mumford.f Q₂ - (1 : Q₂[X]) ^ 2 = _
    unfold N13Mumford.f
    ring
  infinity_bound := by
    rw [add_zero]
    compute_degree!
def caSemi : N13Mumford.SemiMumford Q₂ := { caMumford.toSemi with nInf := -1 }
theorem ca_degree : caMumford.u.natDegree = 2 := by
  change (X * (X + 1) : Q₂[X]).natDegree = 2
  compute_degree!
end
end MazurProof.N13CalibratedChooser
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The actual characteristic-two infinity chart has two power-series branches
obtained by reducing the integral Hensel roots. Both n-jets vanish exactly
on the principal ideal (t^n). This is special-fibre geometry, independent of
the unreviewed calibrated chooser and of the missing special-code theorem.
-/
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
abbrev B := N13SpecialInfinityChart.CoordinateRing
end
end MazurProof.N13SpecialInfinityBranchJets
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineNorm =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual hyperelliptic conjugation and polynomial norm on the good
characteristic-two affine coordinate ring. This is not the bad sextic
obtained by dividing the ordinate by two. Nonzero functions have nonzero
norm, and the comparison factor pair makes the norm divide an explicit
polynomial supported only over x=0 and x=1.
-/
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts
def normPolynomial (p q : K[X]) : K[X] := p ^ 2 - p * q * hPoly - q ^ 2 * rhsPoly
def norm (z : R) : K[X] := normPolynomial (coeff0 z) (coeffY z)
open N13SpecialComparisonFactorPair hiding xClass R
end
end MazurProof.N13SpecialAffineNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialLaurentBranches =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialLaurentBranches =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual Laurent expansions of the GOOD characteristic-two affine model.
The branch difference is h(x), not twice a square root. The resulting
two-infinity pole bound forces deg(A)<=d and deg(B)+3<=d for A+B*y.
-/
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
abbrev base := N13BranchNorm.evalPoly K
end
end MazurProof.N13SpecialLaurentBranches
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialOverlapBranches =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialOverlapBranches =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The actual special ordinary overlap maps to each Laurent branch. The maps
agree with the just-constructed affine expansions and with the inclusions
of the actual infinity power-series expansions. Consequently a special
comparison transports one and the same fraction to both branches.
-/
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
abbrev B := N13SpecialInfinityChart.CoordinateRing
abbrev O := N13SpecialCurveOverlap.InfinityOverlap
end
end MazurProof.N13SpecialOverlapBranches
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialBranchFaithfulness =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialBranchFaithfulness =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Each named special branch is faithful on the ordinary coordinate ring.
The norm proves affine faithfulness; localization and the actual overlap
diagram transfer it to the infinity chart. No faithfulness of completion
is postulated.
-/
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
abbrev AO := N13SpecialCurveOverlap.AffineOverlap
theorem affine_x_ne_zero : N13SpecialCurveOverlap.xClass ≠ 0 :=
  N13GoodCoordinateRingTwo.xClass_ne_zero Polynomial.X_ne_zero
instance instIsDomainAO : IsDomain AO := IsLocalization.isDomain_localization
  (powers_le_nonZeroDivisors_of_noZeroDivisors affine_x_ne_zero)
end
end MazurProof.N13SpecialBranchFaithfulness
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate =====
section
/-!
Source pin: b07243d72093bec5686e15b1208cb50d000f3e8d.
Source-only repair of the certificate candidate from
4109ba77745784c1a9f8c4c7b304df4124bf5ac4. Lean and axiom checks NOT RUN.

Finite polynomial certificates for all 32 * 4 coefficient pairs in the
GOOD F2 model. Polynomial divisibility is never passed to a decision
procedure. The six local equations have explicit cofactors. Each of the
58 unsupported nonzero norms has an explicit factor coprime to both X
and X - 1; its two Bezout identities rule out support. The zero norm is
excluded separately. The 69 supported rows have explicit six-polynomial
normal forms and first-nonzero-coefficient certificates.

All public definition values and theorem statements are unchanged.
The link between these nine-jet orders and the six geometric local
orders is a separate theorem.
-/
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def GoodJets (p : Fin 6 → K[X]) : Prop :=
  (∀ i : Fin 6, jetOrder (p i) < 9 ∧
    (p i).coeff (jetOrder (p i)) ≠ 0 ∧
    ∀ j : Fin 9, (j : ℕ) < jetOrder (p i) → (p i).coeff j = 0) ∧
  (jetOrder (p 0) : ZMod 19) - jetOrder (p 1) +
    7 * (jetOrder (p 2) : ZMod 19) - 7 * jetOrder (p 3) +
    8 * (jetOrder (p 4) : ZMod 19) - 8 * jetOrder (p 5) = 0
-- Coefficient bit codes (a, b) = (0, 0).
-- Coefficient bit codes (a, b) = (0, 1).
-- Coefficient bit codes (a, b) = (0, 2).
-- Coefficient bit codes (a, b) = (0, 3).
-- Coefficient bit codes (a, b) = (1, 0).
-- Coefficient bit codes (a, b) = (1, 1).
-- Coefficient bit codes (a, b) = (1, 2).
-- Coefficient bit codes (a, b) = (1, 3).
-- Coefficient bit codes (a, b) = (2, 0).
-- Coefficient bit codes (a, b) = (2, 1).
-- Coefficient bit codes (a, b) = (2, 2).
-- Coefficient bit codes (a, b) = (2, 3).
-- Coefficient bit codes (a, b) = (3, 0).
-- Coefficient bit codes (a, b) = (3, 1).
-- Coefficient bit codes (a, b) = (3, 2).
-- Coefficient bit codes (a, b) = (3, 3).
-- Coefficient bit codes (a, b) = (4, 0).
-- Coefficient bit codes (a, b) = (4, 1).
-- Coefficient bit codes (a, b) = (4, 2).
-- Coefficient bit codes (a, b) = (4, 3).
-- Coefficient bit codes (a, b) = (5, 0).
-- Coefficient bit codes (a, b) = (5, 1).
-- Coefficient bit codes (a, b) = (5, 2).
-- Coefficient bit codes (a, b) = (5, 3).
-- Coefficient bit codes (a, b) = (6, 0).
-- Coefficient bit codes (a, b) = (6, 1).
-- Coefficient bit codes (a, b) = (6, 2).
-- Coefficient bit codes (a, b) = (6, 3).
-- Coefficient bit codes (a, b) = (7, 0).
-- Coefficient bit codes (a, b) = (7, 1).
-- Coefficient bit codes (a, b) = (7, 2).
-- Coefficient bit codes (a, b) = (7, 3).
-- Coefficient bit codes (a, b) = (8, 0).
-- Coefficient bit codes (a, b) = (8, 1).
-- Coefficient bit codes (a, b) = (8, 2).
-- Coefficient bit codes (a, b) = (8, 3).
-- Coefficient bit codes (a, b) = (9, 0).
-- Coefficient bit codes (a, b) = (9, 1).
-- Coefficient bit codes (a, b) = (9, 2).
-- Coefficient bit codes (a, b) = (9, 3).
-- Coefficient bit codes (a, b) = (10, 0).
-- Coefficient bit codes (a, b) = (10, 1).
-- Coefficient bit codes (a, b) = (10, 2).
-- Coefficient bit codes (a, b) = (10, 3).
-- Coefficient bit codes (a, b) = (11, 0).
-- Coefficient bit codes (a, b) = (11, 1).
-- Coefficient bit codes (a, b) = (11, 2).
-- Coefficient bit codes (a, b) = (11, 3).
-- Coefficient bit codes (a, b) = (12, 0).
-- Coefficient bit codes (a, b) = (12, 1).
-- Coefficient bit codes (a, b) = (12, 2).
-- Coefficient bit codes (a, b) = (12, 3).
-- Coefficient bit codes (a, b) = (13, 0).
-- Coefficient bit codes (a, b) = (13, 1).
-- Coefficient bit codes (a, b) = (13, 2).
-- Coefficient bit codes (a, b) = (13, 3).
-- Coefficient bit codes (a, b) = (14, 0).
-- Coefficient bit codes (a, b) = (14, 1).
-- Coefficient bit codes (a, b) = (14, 2).
-- Coefficient bit codes (a, b) = (14, 3).
-- Coefficient bit codes (a, b) = (15, 0).
-- Coefficient bit codes (a, b) = (15, 1).
-- Coefficient bit codes (a, b) = (15, 2).
-- Coefficient bit codes (a, b) = (15, 3).
-- Coefficient bit codes (a, b) = (16, 0).
-- Coefficient bit codes (a, b) = (16, 1).
-- Coefficient bit codes (a, b) = (16, 2).
-- Coefficient bit codes (a, b) = (16, 3).
-- Coefficient bit codes (a, b) = (17, 0).
-- Coefficient bit codes (a, b) = (17, 1).
-- Coefficient bit codes (a, b) = (17, 2).
-- Coefficient bit codes (a, b) = (17, 3).
-- Coefficient bit codes (a, b) = (18, 0).
-- Coefficient bit codes (a, b) = (18, 1).
-- Coefficient bit codes (a, b) = (18, 2).
-- Coefficient bit codes (a, b) = (18, 3).
-- Coefficient bit codes (a, b) = (19, 0).
-- Coefficient bit codes (a, b) = (19, 1).
-- Coefficient bit codes (a, b) = (19, 2).
-- Coefficient bit codes (a, b) = (19, 3).
-- Coefficient bit codes (a, b) = (20, 0).
-- Coefficient bit codes (a, b) = (20, 1).
-- Coefficient bit codes (a, b) = (20, 2).
-- Coefficient bit codes (a, b) = (20, 3).
-- Coefficient bit codes (a, b) = (21, 0).
-- Coefficient bit codes (a, b) = (21, 1).
-- Coefficient bit codes (a, b) = (21, 2).
-- Coefficient bit codes (a, b) = (21, 3).
-- Coefficient bit codes (a, b) = (22, 0).
-- Coefficient bit codes (a, b) = (22, 1).
-- Coefficient bit codes (a, b) = (22, 2).
-- Coefficient bit codes (a, b) = (22, 3).
-- Coefficient bit codes (a, b) = (23, 0).
-- Coefficient bit codes (a, b) = (23, 1).
-- Coefficient bit codes (a, b) = (23, 2).
-- Coefficient bit codes (a, b) = (23, 3).
-- Coefficient bit codes (a, b) = (24, 0).
-- Coefficient bit codes (a, b) = (24, 1).
-- Coefficient bit codes (a, b) = (24, 2).
-- Coefficient bit codes (a, b) = (24, 3).
-- Coefficient bit codes (a, b) = (25, 0).
-- Coefficient bit codes (a, b) = (25, 1).
-- Coefficient bit codes (a, b) = (25, 2).
-- Coefficient bit codes (a, b) = (25, 3).
-- Coefficient bit codes (a, b) = (26, 0).
-- Coefficient bit codes (a, b) = (26, 1).
-- Coefficient bit codes (a, b) = (26, 2).
-- Coefficient bit codes (a, b) = (26, 3).
-- Coefficient bit codes (a, b) = (27, 0).
-- Coefficient bit codes (a, b) = (27, 1).
-- Coefficient bit codes (a, b) = (27, 2).
-- Coefficient bit codes (a, b) = (27, 3).
-- Coefficient bit codes (a, b) = (28, 0).
-- Coefficient bit codes (a, b) = (28, 1).
-- Coefficient bit codes (a, b) = (28, 2).
-- Coefficient bit codes (a, b) = (28, 3).
-- Coefficient bit codes (a, b) = (29, 0).
-- Coefficient bit codes (a, b) = (29, 1).
-- Coefficient bit codes (a, b) = (29, 2).
-- Coefficient bit codes (a, b) = (29, 3).
-- Coefficient bit codes (a, b) = (30, 0).
-- Coefficient bit codes (a, b) = (30, 1).
-- Coefficient bit codes (a, b) = (30, 2).
-- Coefficient bit codes (a, b) = (30, 3).
-- Coefficient bit codes (a, b) = (31, 0).
-- Coefficient bit codes (a, b) = (31, 1).
-- Coefficient bit codes (a, b) = (31, 2).
-- Coefficient bit codes (a, b) = (31, 3).
end
end MazurProof.N13SpecialSmallFunctionCertificate
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialAbelCode =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAbelCode =====
section
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- The three hyperelliptic base fibres receive amplitudes 1, 7, 8. -/
def baseAmplitude : BasePoint → Code
  | Sum.inl k => match k with
    | 0 => 1
    | 1 => 7
  | Sum.inr _ => 8
end
end MazurProof.N13SpecialAbelCode
end

end

-- ===== FLT.Assumptions.MazurProof.N13ConstructedSpecialization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ConstructedSpecialization =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The recentered code of the CONSTRUCTED calibrated chooser is an additive
map to ZMod19 and agrees with proper point reduction. This uses the actual
two-chart comparisons and the proved degree-four bridge. It does not use
the previously flagged exactSpreadLine or bad-characteristic sextic route.
-/
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode
abbrev G := N13RationalPointEndgame.G
end
end MazurProof.N13ConstructedSpecialization
end

end

-- ===== FLT.Assumptions.MazurProof.N13KernelBaseDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KernelBaseDivisor =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The actual additive specialization kernel, translated by the two finite
cusps C and B, has the literal special divisor C+B. The nonzero code 8
excludes the canonical pencil, so this is equality of divisors, not merely
equality of their classes. The infinity-mark shift is a separate step.
-/
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
def baseTranslate : G :=
  N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint .zeroPlus) +
    N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint .negOneMinus)
end
end MazurProof.N13KernelBaseDivisor
end

end

-- ===== FLT.Assumptions.MazurProof.N13KernelInfinityMultiplicity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KernelInfinityMultiplicity =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The finite special divisor C+B forces both actual generic infinity orders
to vanish. The proof uses the integral branch constant coefficients and
the literal element t-1 in the reduced infinity ideal; it does not infer
generic marking from an independent integer attached to Data.
-/
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
abbrev S := N13SpecialInfinityChart.CoordinateRing
abbrev red := N13IntegralInfinityReduction.reduceCoordinate
abbrev redBase := N13IntegralInfinityReduction.reduceBase
end
end MazurProof.N13KernelInfinityMultiplicity
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFormalTransition =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordFormalTransition =====
section
/-!
# The formal transition of a near-base N13 Mumford graph

The affine graph ideal of integral Mumford data contains its monic polynomial
`u(x)`.  On the punctured formal neighbourhood of infinity this polynomial
is a unit: after factoring its pole `t⁻ᵈ`, the remaining power series is the
reversal of `u`, whose constant coefficient is the leading coefficient `1`.

For data reducing to the selected base graph, the ratio between `u` and the
base polynomial is therefore a genuine unit of the integral quadratic formal
overlap.  Its coefficientwise reduction is one, so it supplies the actual
`NearIdentityTransition` required by the twisted Čech complex.  No Laurent
coefficient enumeration or global generator of the affine ideal is used.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] MazurProof.N13MumfordFormalTransition.instFactPrimeOfNatNat_fLT
abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve
@[implicit_reducible] def tInvInvertible :
    Invertible (N13FormalCurveOverlap.tPow (-1)) where
  invOf := N13FormalCurveOverlap.tPow 1
  invOf_mul_self := by
    rw [N13FormalCurveOverlap.tPow_mul]
    norm_num
  mul_invOf_self := by
    rw [N13FormalCurveOverlap.tPow_mul]
    norm_num
attribute [local instance] tInvInvertible
/-! ## Reduction of polynomial restrictions -/
/-! ## The near-base transition -/
end
end MazurProof.N13MumfordFormalTransition
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet =====
section
/-!
# First-order coordinates of the N13 formal Mumford transition

The transition of a two-disk Mumford graph is a quotient of two formal
polynomial units.  Multiplying its displacement from the identity by the
fixed base unit cancels the denominator exactly, leaving the finite Laurent
polynomial attached to `u - uBase`.

Its coefficients in degrees `-1` and `0` recover the two disk coordinates
up to the single quadratic term `x₀ * (x₁ + 1)`.  Thus the actual weighted
transition jet agrees with the Abel-chart coordinates modulo the square of
their coordinate ideal, without expanding an inverse power series.
-/
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13MumfordFormalTransitionJet.instFactPrimeOfNatNat_fLT
abbrev FormalCurve : Type :=
  N13MumfordFormalTransition.FormalCurve
end
end MazurProof.N13MumfordFormalTransitionJet
end

end

-- ===== FLT.Assumptions.MazurProof.N13CrossQuadraticPolynomial =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CrossQuadraticPolynomial =====
section
/-!
# Cross-quadratic errors in two disjoint variable blocks

For a polynomial ring whose variables are split into a left and a right
block, the two coordinate-axis ideals have intersection equal to their
product.  Consequently a polynomial that vanishes on both axes has a
mixed factor.

The proof is by monomial support.  It is independent of N13 and performs no
coefficient expansion.
-/
namespace MazurProof.N13CrossQuadraticPolynomial
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]
def leftVar (i : Fin 2) : BiPoly R :=
  X (Sum.inl i)
def rightVar (i : Fin 2) : BiPoly R :=
  X (Sum.inr i)
theorem crossMonomial_eq
    (i j : Fin 2) :
    monomial
        (Finsupp.single (Sum.inl i) 1 +
          Finsupp.single (Sum.inr j) 1)
        (1 : R) =
      leftVar R i * rightVar R j := by
  rw [monomial_add_single, ← X_pow_eq_monomial]
  simp [leftVar, rightVar]
def error
    (F : Fin 2 → BiPoly R) (i : Fin 2) : BiPoly R :=
  F i - leftVar R i - rightVar R i
end
end MazurProof.N13CrossQuadraticPolynomial
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw =====
section
/-!
# From a regular Abel law to the N13 two-adic kernel chart

The universal addition law is a polynomial in two disjoint coordinate
blocks.  If its restrictions to both axes are the identity, its nonlinear
error lies in the product of the two axis ideals.  Evaluation sends those
axis ideals into the coordinate ideals of the two input points, giving
exactly the error estimate required by `N13TwoAdicKernelChart.Chart`.

The final structure in this file records the remaining geometric seam:
kernel classes must be represented faithfully by the two Hensel disks and
their transported group law must be regular on this chart.
-/
namespace MazurProof.N13TwoAdicAbelChartLaw
noncomputable section
open MvPolynomial
attribute [local instance] MazurProof.N13TwoAdicAbelChartLaw.instFactPrimeOfNatNat_fLT
universe u
variable {K : Type u}
@[simp] theorem evalPair_leftVar
    (coord : K → Fin 2 → R₂) (z w : K) (i : Fin 2) :
    evalPair coord z w
        (N13CrossQuadraticPolynomial.leftVar R₂ i) =
      coord z i := by
  simp [evalPair, N13CrossQuadraticPolynomial.leftVar]
@[simp] theorem evalPair_rightVar
    (coord : K → Fin 2 → R₂) (z w : K) (i : Fin 2) :
    evalPair coord z w
        (N13CrossQuadraticPolynomial.rightVar R₂ i) =
      coord w i := by
  simp [evalPair, N13CrossQuadraticPolynomial.rightVar]
theorem map_leftIdeal_le_coordIdeal
    (coord : K → Fin 2 → R₂) (z w : K) :
    Ideal.map (evalPair coord z w)
        (N13CrossQuadraticPolynomial.leftIdeal R₂) ≤
      N13TwoAdicKernelChart.coordIdeal coord z := by
  rw [Ideal.map_le_iff_le_comap,
    N13CrossQuadraticPolynomial.leftIdeal, Ideal.span_le]
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  change
    evalPair coord z w
        (N13CrossQuadraticPolynomial.leftVar R₂ i) ∈
      N13TwoAdicKernelChart.coordIdeal coord z
  rw [evalPair_leftVar]
  apply Ideal.subset_span
  exact Set.mem_range_self i
theorem map_rightIdeal_le_coordIdeal
    (coord : K → Fin 2 → R₂) (z w : K) :
    Ideal.map (evalPair coord z w)
        (N13CrossQuadraticPolynomial.rightIdeal R₂) ≤
      N13TwoAdicKernelChart.coordIdeal coord w := by
  rw [Ideal.map_le_iff_le_comap,
    N13CrossQuadraticPolynomial.rightIdeal, Ideal.span_le]
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  change
    evalPair coord z w
        (N13CrossQuadraticPolynomial.rightVar R₂ i) ∈
      N13TwoAdicKernelChart.coordIdeal coord w
  rw [evalPair_rightVar]
  apply Ideal.subset_span
  exact Set.mem_range_self i
/-- Evaluation carries every universal mixed term into the product of the
two actual coordinate ideals. -/
theorem eval_mem_coordIdeal_mul
    (coord : K → Fin 2 → R₂) (z w : K)
    (p : BiPoly)
    (hp :
      p ∈ N13CrossQuadraticPolynomial.leftIdeal R₂ *
        N13CrossQuadraticPolynomial.rightIdeal R₂) :
    evalPair coord z w p ∈
      N13TwoAdicKernelChart.coordIdeal coord z *
        N13TwoAdicKernelChart.coordIdeal coord w := by
  have hmap :
      evalPair coord z w p ∈
        Ideal.map (evalPair coord z w)
          (N13CrossQuadraticPolynomial.leftIdeal R₂ *
            N13CrossQuadraticPolynomial.rightIdeal R₂) :=
    Ideal.mem_map_of_mem (evalPair coord z w) hp
  rw [Ideal.map_mul] at hmap
  exact
    (Ideal.mul_mono
      (map_leftIdeal_le_coordIdeal coord z w)
      (map_rightIdeal_le_coordIdeal coord z w)) hmap
variable [AddCommGroup K]
namespace DoublingLaw
variable {coord : K → Fin 2 → R₂}
end DoublingLaw
namespace PolynomialLaw
variable {coord : K → Fin 2 → R₂}
end PolynomialLaw
namespace DoublingGeometricData
end DoublingGeometricData
namespace GeometricData
end GeometricData
end
end MazurProof.N13TwoAdicAbelChartLaw
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartSection =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartSection =====
section
/-!
# Recovering the N13 kernel chart from Picard representatives

The two-disk Abel map is already known to be injective in `J(ℚ₂)`.
Consequently a map from an additive group into `J(ℚ₂)`, together with a
two-disk representative for each of its elements, automatically gives the
correct base pair and an injective representative map.  Those facts should
not remain separate geometric hypotheses.

For a subgroup of the rational Picard group, coefficient extension
`J(ℚ) → J(ℚ₂)` is injective as well.  Thus the only inputs left for the
formal-kernel chart are existence of the two-disk representatives and the
regularity estimate for their transported addition law.
-/
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartSection.instFactPrimeOfNatNat_fLT
universe u
abbrev Pic₂ : Type :=
  N13TwoAdicAbelChartPic.Pic
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
end DoublingData
namespace Data
end Data
abbrev RationalPic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model ℚ)
    (N13Infinity.positiveInfinityOrder ℚ)
namespace RationalKernelDoublingData
variable {H : AddSubgroup RationalPic}
end RationalKernelDoublingData
namespace RationalKernelData
variable {H : AddSubgroup RationalPic}
end RationalKernelData
end
end MazurProof.N13TwoAdicAbelChartSection
end

end

-- ===== FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter =====
section
/-!
# N13 rational-kernel unary doubling adapter

The two-adic transition calculation already controls the tensor square of
one near-base line bundle to first order.  To turn that calculation into
separatedness for the actual rational reduction kernel, two geometric
producers remain:

* a centered near-base integral Mumford graph for every kernel class; and
* comparison, modulo the square of the moving coordinate ideal, between
  the chosen graph for `2 • z` and the square of the graph for `z`.

This file packages those producers and derives the exact
`RationalKernelDoublingData` consumed by the N13 endgame.  It introduces no
new assumption and keeps the remaining first-jet theorem explicit.
-/
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT
universe u
/-- Smooth integral Mumford graphs reducing to the fixed base graph. -/
abbrev NearBaseMumford : Type :=
  N13TwoAdicAbelChartRecover.NearBaseMumford
/-! ## Recovering canonical disk pairs from kernel representatives -/
namespace NearBaseFamily
end NearBaseFamily
namespace MappedSpecialRepresentative
end MappedSpecialRepresentative
namespace MappedSpecialFamily
end MappedSpecialFamily
/-! ## Canonical mapped-special representatives -/
namespace CanonicalMappedSpecialFamily
end CanonicalMappedSpecialFamily
namespace NearBaseFamily
/-! ## Comparing a selected double with the squared transition -/
end NearBaseFamily
/-! ## The exact remaining unary compatibility -/
namespace FirstJetDoublingCompatibility
end FirstJetDoublingCompatibility
/-! ## One-call assembly from mapped-special representatives -/
namespace MappedSpecialFamily
end MappedSpecialFamily
namespace CanonicalMappedSpecialFamily
end CanonicalMappedSpecialFamily
/-! ## Specialization to the eventual spread classifier -/
namespace Concrete
variable {Line : Type u}
end Concrete
end
end MazurProof.N13RationalKernelDoublingAdapter
end

end

-- ===== FLT.Assumptions.MazurProof.N13KernelGraphContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KernelGraphContraction =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The finite C+B special divisor is the literal graph ideal (X²+X,Y).
Vertical saturation then identifies a certified affine lattice with the
canonical contraction of its same generic Mumford graph. These conclusions
retain the actual witness and do not use normal-form spread coherence.
-/
namespace MazurProof.N13KernelGraphContraction
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13KernelGraphContraction.instFactPrimeOfNatNat_fLT
local instance instAlgebraAR : Algebra A R := N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra
end
end MazurProof.N13KernelGraphContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13KernelBasePic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KernelBasePic =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

Both a finite effective quadratic and the fixed C+B divisor acquire the
same +1 raw infinity twist when their graph is balanced. Keeping this
twist explicit proves the adapter's exact centered class equality.
-/
namespace MazurProof.N13KernelBasePic
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13KernelBasePic.instFactPrimeOfNatNat_fLT
def rawClass (r : SexticMumford.OrientedFrac Model) : GenericPic :=
  Additive.ofMul (QuotientGroup.mk'
    (SexticMumford.principalOriented Model
      (N13Infinity.positiveInfinityOrder Q₂)).range r)
def infinityShift : GenericPic := rawClass (1, Multiplicative.ofAdd 1)
end
end MazurProof.N13KernelBasePic
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCenteredNumerator =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCenteredNumerator =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Change the actual small principal numerator from the sextic coordinates to
the good model. Its membership in the SAME fixed base ideal forces the
polynomial part to be divisible by uBase. Thus the regular numerator has
the exact Hermite shape uBase*A+b*y, with deg A≤2 and deg b≤1 over Q2.
-/
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13GoodCenteredNumerator.instFactPrimeOfNatNat_fLT
abbrev toGood := N13GoodSexticCoordinateEquiv.toGood (K := K)
abbrev toSextic := N13GoodSexticCoordinateEquiv.toSextic (K := K)
end
end MazurProof.N13GoodCenteredNumerator
end

end


