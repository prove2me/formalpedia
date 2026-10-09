-- Prove2me | Definitions.Def_MazurN13_L1
-- name    : MazurN13_L1
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-09T03:43:37.060479+00:00
-- url     : https://prove2.me/theorems/c844a60e-9c28-47a7-863a-c397ab53faa1
-- title:
--   Mazur order 13 (Huang FLT port): definitions, layer 1
-- statement:
--   Layer 1 of 12 of the definitions used by a machine-checked Lean proof of the case $N=13$ of Mazur's torsion theorem (no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$). It collects the definitions, structures, instances and small structural lemmas of Xiang Huang's development whose dependencies are available at this layer; larger lemmas they rely on are separate platform theorems, imported here as already-proved results. Layer $k$ imports layer $k-1$.
--
--   Port notes: only API-drift fixes (transparency options, renamed lemmas); local notations expanded and `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_h_coeff_zero
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_h_explicit
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_mumfordIdeal_mul_conj_integral
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineFiber_derivative
import Theorems.Thm_MazurProof_N13GoodModelTwo_overlap_residual
import Theorems.Thm_MazurProof_N13Infinity_reverseTail_constantCoeff
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_evalAtInfinity_eq_reverse_mul
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_order_ofPowerSeries_of_coeff_zero_ne
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_parameter_inv
import Theorems.Thm_MazurProof_N13LocalDlogTwo_residueCubic_natDegree
import Theorems.Thm_MazurProof_N13Mumford_f_monic
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_f_sub_sqrtInfinity_sq
import Theorems.Thm_MazurProof_N13SexticIrreducible_fInt_monic
import Theorems.Thm_MazurProof_N13SexticIrreducible_fModThree_irreducible
import Theorems.Thm_MazurProof_SexticMumford_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_no_artinSchreier_polynomial_root
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_evalSqrtInfinity_coeff_neg_three
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_sub_mod_dvd

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/
namespace MazurProof.N13GoodModelTwo
noncomputable section
open scoped CharTwo
open Polynomial
universe u
variable {R : Type u} [CommRing R]
/-! ## The two charts of the weighted projective completion -/
/-- The two equations agree on the overlap `xt=1`. -/
theorem affine_iff_infinity_on_overlap
    {x t v : R} (hxt : x * t = 1) :
    AffineEquation x (x ^ 3 * v) ↔ InfinityChartEquation t v := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one t hxt
  have hx6 : IsUnit (x ^ 6) := hx.pow 6
  rw [affineEquation_iff_residual, infinityChartEquation_iff,
    overlap_residual hxt]
  constructor
  · intro hz
    exact hx6.mul_left_cancel (by simpa using hz)
  · intro hz
    rw [hz, mul_zero]
theorem affineFiber_derivative_eval (x y : R) :
    (affineFiber x).derivative.eval y = affineDerivativeY x y := by
  rw [affineFiber_derivative]
  simp [affineDerivativeY]
/-! ## Structural characteristic-two point classification -/
variable {K : Type u} [Field K] [CharP K 2]
/-! ## The fields `F₂` and `F₄` -/
attribute [local instance] MazurProof.N13GoodModelTwo.instFintypeF4
end
end MazurProof.N13GoodModelTwo
end

end

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
theorem curvePoly_degree [Nontrivial R] :
    (curvePoly : R[X][X]).degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num
@[simp] theorem coeff0_xClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)
@[simp] theorem coeffY_xClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)
@[simp] theorem coeff0_yClass [Nontrivial R] :
    coeff0 (yClass (R := R)) = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num
@[simp] theorem coeffY_yClass [Nontrivial R] :
    coeffY (yClass (R := R)) = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num
@[simp] theorem coeff0_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp
@[simp] theorem coeffY_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = p
  rw [← Algebra.smul_def]
  simp
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
theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot curvePoly q := by
  intro hq
  have heq :
      q ^ 2 + hPoly * q = rhsPoly := by
    have hzero :
        q ^ 2 + hPoly * q - rhsPoly = 0 := by
      simpa only [IsRoot.def, curvePoly, eval_sub, eval_add, eval_pow,
        eval_X, eval_C, eval_mul] using hq
    exact sub_eq_zero.mp hzero
  exact no_artinSchreier_polynomial_root q heq
theorem curvePoly_irreducible : Irreducible curvePoly := by
  rw [curvePoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot q
      ((mem_roots curvePoly_monic.ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]
instance curvePolyIrreducibleFact : Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩
instance instIsDomainCoordinateRing : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime
@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)
@[simp] theorem coeffY_yClass :
    coeffY yClass = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num
theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt curvePoly_monic
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford) :
    (mumfordIdeal D.u D.v :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) =
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]
/-- A generalized Mumford graph ideal as a unit fractional ideal. -/
def mumfordIdealUnit (D : SemiMumford) : InvFrac :=
  Units.mkOfMulEqOne
    (mumfordIdeal D.u D.v :
      FractionalIdeal CoordinateRing⁰ FunctionField)
    ((mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField)⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        FunctionField (xClass_ne_zero D.u_monic.ne_zero))
@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford) :
    (mumfordIdealUnit D :
      FractionalIdeal CoordinateRing⁰ FunctionField) =
      mumfordIdeal D.u D.v := rfl
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
namespace Model
end Model
variable (M : Model K)
/-! ## The affine coordinate ring -/
theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot (curvePoly M) q := by
  intro hq
  have hsq : q ^ 2 = M.f := by
    simpa only [IsRoot.def, curvePoly, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hq
  have hqunit : IsUnit q := by
    apply M.squarefree q
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hqunit.pow 2
  exact M.not_isUnit hfunit
theorem curvePoly_irreducible : Irreducible (curvePoly M) := by
  rw [(curvePoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot M q
      ((mem_roots (curvePoly_monic M).ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]
instance curvePolyIrreducibleFact : Fact (Irreducible (curvePoly M)) :=
  ⟨curvePoly_irreducible M⟩
instance instIsDomainCoordinateRing : IsDomain (CoordinateRing M) :=
  AdjoinRoot.isDomain_of_prime (curvePoly_irreducible M).prime
theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass M p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (curvePoly_monic M)
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)
/-! ## Balanced triples -/
/-! ## Curve points and their balanced representatives -/
/-! ## Mumford ideals -/
/-! ## The oriented fractional-ideal quotient -/
def principalOriented (O : InfinityOrder M) :
    (FunctionField M)ˣ →* OrientedFrac M :=
  (toPrincipalIdeal (CoordinateRing M) (FunctionField M)).prod O.ordPlus
abbrev OrientedPic (O : InfinityOrder M) : Type u :=
  Additive (OrientedFrac M ⧸ (principalOriented M O).range)
instance (O : InfinityOrder M) : AddCommGroup (OrientedPic M O) :=
  inferInstance
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13Mumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Mumford =====
section
/-!
# The smooth sextic and Mumford model for `X₁(13)`

This file instantiates the curve-independent balanced Mumford layer with the
standard sextic model of `X₁(13)`.  Smoothness is proved by a short Bézout
identity between the sextic and its derivative.
-/
open Polynomial
namespace MazurProof.N13Mumford
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-- The `X₁(13)` instance of the generic smooth monic sextic model. -/
def model : SexticMumford.Model K where
  f := f K
  monic := f_monic K
  natDegree := f_natDegree K
  separable := f_separable K
  two_ne_zero := by norm_num
@[simp] theorem model_f :
    (model K).f = f K := rfl
abbrev CoordinateRing : Type u :=
  SexticMumford.CoordinateRing (model K)
abbrev FunctionField : Type u :=
  SexticMumford.FunctionField (model K)
abbrev Mumford : Type u :=
  SexticMumford.Mumford (model K)
abbrev SemiMumford : Type u :=
  SexticMumford.SemiMumford (model K)
/-! ## The six rational cusps -/
/-- The six cusps as points of the generic two-infinity sextic model. -/
def cuspPoint : Cusp13 → SexticMumford.CurvePoint (model ℚ)
  | .infinityPlus => .infinityPlus
  | .infinityMinus => .infinityMinus
  | .zeroPlus => .affine 0 1 (by norm_num [model, f])
  | .zeroMinus => .affine 0 (-1) (by norm_num [model, f])
  | .negOnePlus => .affine (-1) 1 (by norm_num [model, f])
  | .negOneMinus => .affine (-1) (-1) (by norm_num [model, f])
/-- A scalar point on the sextic gives a point of its projective completion. -/
def affineCurvePoint (X Y : ℚ) (h : N13CurveModel.C13SexticEq X Y) :
    SexticMumford.CurvePoint (model ℚ) :=
  .affine X Y (by
    change Y ^ 2 = (f ℚ).eval X
    rw [f_eval_eq_sexticF13]
    exact h)
end
end MazurProof.N13Mumford
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
abbrev M : SexticMumford.Model K :=
  N13Mumford.model K
abbrev SexticRing : Type u :=
  N13Mumford.CoordinateRing K
def sexticXHom : K[X] →+* SexticRing (K := K) :=
  AdjoinRoot.of (SexticMumford.curvePoly (M (K := K)))
@[simp] theorem sexticXHom_apply (p : K[X]) :
    sexticXHom (K := K) p =
      SexticMumford.xClass (M (K := K)) p := rfl
/-- The good `y` coordinate inside the sextic coordinate ring. -/
def goodYInSextic : SexticRing (K := K) :=
  (1 / 2 : K) •
    (SexticMumford.yClass (M (K := K)) -
      sexticXHom (K := K) hPoly)
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/
open Polynomial
namespace MazurProof.N13GoodSexticMumfordTransport
noncomputable section
open N13GoodSexticCoordinateEquiv
universe u
variable {K : Type u} [Field K] [CharZero K]
theorem invTwo_isUnit :
    IsUnit ((algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹) := by
  exact
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K)⁻¹ ≠ 0)).map
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K)))
/-- Completing the square carries the generalized Mumford equation to the
standard sextic equation. -/
theorem completedGraph_curve_eq
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    N13Mumford.f K - completedGraph D.v ^ 2 =
      D.u * (-4 * D.w) := by
  rw [N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs
    (K := K)]
  unfold completedGraph
  linear_combination -4 * D.curve_eq
/-- Reducing the completed graph polynomial modulo `u` preserves the
sextic divisibility relation. -/
theorem reducedCompletedGraph_curve_dvd
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    D.u ∣ N13Mumford.f K -
      reducedCompletedGraph D.u D.v ^ 2 := by
  let V : K[X] := completedGraph D.v
  let Vred : K[X] := reducedCompletedGraph D.u D.v
  obtain ⟨q, hq⟩ := dvd_sub_mod V D.u
  change V - Vred = D.u * q at hq
  refine ⟨-4 * D.w + q * (V + Vred), ?_⟩
  calc
    N13Mumford.f K - Vred ^ 2 =
        (N13Mumford.f K - V ^ 2) +
          (V - Vred) * (V + Vred) := by ring
    _ =
        D.u * (-4 * D.w) +
          (D.u * q) * (V + Vred) := by
      rw [completedGraph_curve_eq D, hq]
    _ = D.u * (-4 * D.w + q * (V + Vred)) := by ring
/-- A generalized Mumford representative over a characteristic-zero field,
written as a standard reduced sextic semirepresentative. -/
def toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    SexticMumford.SemiMumford (N13GoodSexticCoordinateEquiv.M (K := K)) where
  u := D.u
  v := reducedCompletedGraph D.u D.v
  nInf := nInf
  u_monic := D.u_monic
  v_reduced := by
    apply (Polynomial.mod_eq_self_iff D.u_monic.ne_zero).2
    exact Polynomial.degree_mod_lt _ D.u_monic.ne_zero
  curve_dvd := by
    simpa only [N13Mumford.model_f] using
      reducedCompletedGraph_curve_dvd D
@[simp] theorem toSexticSemi_u
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).u = D.u := rfl
@[simp] theorem toSexticSemi_v
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).v =
      reducedCompletedGraph D.u D.v := rfl
@[simp] theorem toSexticSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).nInf = nInf := rfl
end
end MazurProof.N13GoodSexticMumfordTransport
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport =====
section
/-!
# Transporting integral N13 Mumford data to the two-adic sextic model

Smooth generalized Mumford data over `ℤ₂` first extend coefficientwise to
`ℚ₂`.  Completion of the square then gives a standard reduced sextic
semirepresentative.  This file records that passage without choosing
coordinates or enumerating residue classes.
-/
open Polynomial
namespace MazurProof.N13TwoAdicMumfordTransport
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coefficient extension of an integral generalized Mumford datum. -/
def baseChange
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h
@[simp] theorem baseChange_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).u = mapPoly D.u := rfl
@[simp] theorem baseChange_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).v = mapPoly D.v := rfl
@[simp] theorem baseChange_w
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).w = mapPoly D.w := rfl
/-- The standard reduced sextic semirepresentative attached to arbitrary
integral generalized Mumford data. -/
def sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChangeSemi D) nInf
@[simp] theorem sexticSemiOfSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).u = mapPoly D.u := rfl
@[simp] theorem sexticSemiOfSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl
@[simp] theorem sexticSemiOfSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).nInf = nInf := rfl
/-- The standard reduced sextic semirepresentative over `ℚ₂`. -/
def sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChange D) nInf
@[simp] theorem sexticSemi_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).u = mapPoly D.u := rfl
@[simp] theorem sexticSemi_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl
@[simp] theorem sexticSemi_nInf
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).nInf = nInf := rfl
end
end MazurProof.N13TwoAdicMumfordTransport
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
/-- Coefficient extension on the affine coordinate ring of the good model. -/
def extendCoordinate : IntegralRing →+* GoodRing :=
  AdjoinRoot.map mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd
@[simp] theorem extend_xClass (p : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GeneralizedMumfordIntegral.xClass
        (R := Q₂) (mapPoly p) := by
  exact AdjoinRoot.map_of
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd p
@[simp] theorem extend_yClass :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GeneralizedMumfordIntegral.yClass (R := Q₂) := by
  exact AdjoinRoot.map_root
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd
@[simp] theorem extend_ySubClass (v : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GeneralizedMumfordIntegral.ySubClass
        (R := Q₂) (mapPoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass]
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
omit [CharZero K] in
theorem reverseTail_hasSubst : PowerSeries.HasSubst (reverseTail K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (reverseTail_constantCoeff K)
def sqrtReverseF : K⟦X⟧ :=
  PowerSeries.substAlgHom (reverseTail_hasSubst K)
    (PowerSeries.binomialSeries K (1 / 2 : K))
@[simp] theorem sqrtReverseF_constantCoeff :
    PowerSeries.constantCoeff (sqrtReverseF K) = 1 := by
  rw [sqrtReverseF]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [PowerSeries.coe_substAlgHom (reverseTail_hasSubst K)]
  rw [PowerSeries.coeff_subst' (reverseTail_hasSubst K)]
  simp only [PowerSeries.binomialSeries_coeff]
  rw [finsum_eq_single _ 0]
  · simp
  · intro b hb
    simp [PowerSeries.coeff_zero_eq_constantCoeff,
      reverseTail_constantCoeff, hb]
/-! ## An algebraic model of the function field -/
def curvePolyRat : (RatFunc K)[X] :=
  (SexticMumford.curvePoly (N13Mumford.model K)).map
    (algebraMap K[X] (RatFunc K))
theorem curvePolyRat_irreducible : Irreducible (curvePolyRat K) := by
  rw [curvePolyRat]
  exact
    (SexticMumford.curvePoly_monic
      (N13Mumford.model K)).irreducible_iff_irreducible_map_fraction_map
        (R := K[X]) (K := RatFunc K) |>.mp
        (SexticMumford.curvePoly_irreducible (N13Mumford.model K))
instance curvePolyRatIrreducibleFact :
    Fact (Irreducible (curvePolyRat K)) :=
  ⟨curvePolyRat_irreducible K⟩
abbrev AlgebraicFunctionField : Type u := AdjoinRoot (curvePolyRat K)
def coordinateToAlgebraic :
    N13Mumford.CoordinateRing K →+* AlgebraicFunctionField K :=
  AdjoinRoot.map (algebraMap K[X] (RatFunc K))
    (SexticMumford.curvePoly (N13Mumford.model K)) (curvePolyRat K) (by
      rw [curvePolyRat])
@[simp] theorem coordinateToAlgebraic_mk (g : K[X][X]) :
    coordinateToAlgebraic K (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g) =
      AdjoinRoot.mk (curvePolyRat K)
        (g.map (algebraMap K[X] (RatFunc K))) := by
  simp only [coordinateToAlgebraic, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← Polynomial.eval₂_map]
  simpa only [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def] using
    (AdjoinRoot.aeval_eq
      (f := curvePolyRat K)
      (p := g.map (algebraMap K[X] (RatFunc K))))
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
def wSeries : LaurentSeries K := (sqrtReverseF K : LaurentSeries K)
def ySeries : LaurentSeries K :=
  ((parameter K)⁻¹) ^ 3 * wSeries K
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
def xClassHom : K[X] →+* CoordinateRing M :=
  AdjoinRoot.of (curvePoly M)
@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom M p = xClass M p := rfl
@[simp] theorem xClass_zero : xClass M 0 = 0 := by
  exact map_zero (xClassHom M)
@[simp] theorem xClass_one : xClass M 1 = 1 := by
  exact map_one (xClassHom M)
@[simp] theorem xClass_sub (p q : K[X]) :
    xClass M (p - q) = xClass M p - xClass M q := by
  exact map_sub (xClassHom M) p q
@[simp] theorem xClass_neg (p : K[X]) :
    xClass M (-p) = -xClass M p := by
  exact map_neg (xClassHom M) p
@[simp] theorem xClass_mul (p q : K[X]) :
    xClass M (p * q) = xClass M p * xClass M q := by
  exact map_mul (xClassHom M) p q
@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass M (p ^ n) = xClass M p ^ n := by
  exact map_pow (xClassHom M) p n
def normalPoly : CoordinateRing M →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic M)
def coeff0 : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp (normalPoly M)
def coeffY : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp (normalPoly M)
theorem degree_curvePoly : (curvePoly M).degree = 2 := by
  rw [degree_eq_natDegree (curvePoly_monic M).ne_zero,
    curvePoly_natDegree]
  norm_num
@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY M (xClass M p) = 0 := by
  change (C p %ₘ curvePoly M).coeff 1 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)
@[simp] theorem coeffY_yClass : coeffY M (yClass M) = 1 := by
  change (X %ₘ curvePoly M).coeff 1 = 1
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num
/-! ## Hyperelliptic conjugation and the quadratic norm -/
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
abbrev MumfordResidue (D : SemiMumford M) : Type u :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])
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
theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass M v ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)
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
/-- The oriented Picard group attached to the affine sextic and the chosen
order at infinity. -/
abbrev ConcretePic : Type u :=
  OrientedPic M O
theorem zero_mumfordIdeal :
    mumfordIdeal M (zero M).u (zero M).v = ⊤ := by
  rw [zero_u, zero_v, mumfordIdeal]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp [xClass_one])
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem coeffY_xClass_mul (M : Model K)
    (a : K[X]) (z : CoordinateRing M) :
    coeffY M (xClass M a * z) = a * coeffY M z := by
  rw [show xClass M a =
    algebraMap K[X] (CoordinateRing M) a from rfl]
  rw [← Algebra.smul_def, map_smul]
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
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
set_option maxHeartbeats 2000000 in
/-- An oriented representative whose finite component is an integral ideal.
The unit remembers that this ideal is invertible as a fractional ideal. -/
structure IntegralOrientedRep where
  ideal : Ideal (CoordinateRing M)
  unit : InvFrac M
  coe_unit :
    (unit :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = ideal
  atInfinity : ℤ
namespace IntegralOrientedRep
/-- The raw oriented fractional ideal underlying an integral representative. -/
def raw (R : IntegralOrientedRep M) : OrientedFrac M :=
  (R.unit, Multiplicative.ofAdd R.atInfinity)
/-- The oriented Picard class of an integral representative. -/
def picClass (R : IntegralOrientedRep M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range (R.raw M)
theorem ideal_isUnit (R : IntegralOrientedRep M) :
    IsUnit
      (R.ideal :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  exact ⟨R.unit, R.coe_unit⟩
end IntegralOrientedRep
/-- Contract an integral ideal from the quadratic coordinate ring to its
polynomial subring. -/
def idealContraction (J : Ideal (CoordinateRing M)) : Ideal K[X] :=
  J.comap (xClassHom M)
/-- The canonical monic generator of the contraction of an integral ideal
to `K[X]`. -/
def contractionGenerator (J : Ideal (CoordinateRing M)) : K[X] := by
  classical
  exact _root_.normalize
    (Submodule.IsPrincipal.generator (idealContraction M J))
/-- An integral ideal is primitive when some element has `Y`-coefficient
one.  This is the exact algebraic hypothesis needed to put it in Mumford
graph form. -/
def IdealIsPrimitive (J : Ideal (CoordinateRing M)) : Prop :=
  ∃ z ∈ J, coeffY M z = 1
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
abbrev RationalRing : Type :=
  N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂)
abbrev IntegralOrientedRep : Type :=
  SexticMumford.IntegralOrientedRep
    (N13Mumford.model Q₂)
/-- The integral good model maps to its generalized generic fibre. -/
def integralToGood : IntegralRing →+* GoodRing :=
  N13TwoAdicCoordinateBaseChange.extendCoordinate
local instance integralGoodAlgebra :
    Algebra IntegralRing GoodRing :=
  integralToGood.toAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
end
end MazurProof.N13IntegralModelContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuotientReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientReduction =====
section
/-!
# Reduction of N13 affine quotients

A surjective ambient reduction map descends along a literal mapped-ideal
equality.  The kernel of the descended map is exactly the image of the
ambient kernel.  For the N13 integral model this is the principal ideal
generated by the quotient class of `2`.

No flatness, saturation, or chosen Mumford presentation is used here.
-/
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- The quotient map induced by a ring map carrying the source ideal
literally onto the target ideal. -/
def inducedQuotientMap
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    A ⧸ I →+* S ⧸ J :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp f)
    (sourceIdeal_le_ker_quotientComp f I J hmap)
@[simp] theorem inducedQuotientMap_mk
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (a : A) :
    inducedQuotientMap f I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f a) :=
  rfl
attribute [local instance] MazurProof.N13QuotientReduction.instFactPrimeOfNatNat_fLT
/-- N13 coefficient reduction descended along a mapped-ideal equality. -/
def reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    IntegralRing ⧸ I →+* SpecialRing ⧸ J :=
  inducedQuotientMap
    N13GeneralizedMumfordReduction.reduceCoordinate I J hmap
@[simp] theorem reduceCoordinateQuotient_mk
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J)
    (a : IntegralRing) :
    reduceCoordinateQuotient I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J
        (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
  rfl
end
end MazurProof.N13QuotientReduction
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
/-- The generic graph ideal of sextic Mumford data. -/
abbrev graphIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal Model D.u D.v
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
end
end MazurProof.N13QuotientVerticalFlatness
end

end

-- ===== FLT.Assumptions.MazurProof.N13AbelFiberTwoModel =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelFiberTwoModel =====
section
/-!
# A finite set model for the N13 Abel fibres at two

The six points of the good characteristic-two model form three
hyperelliptic pairs.  On `Sym²(C)(F₂)`, collapse the three corresponding
canonical divisors to one class and leave every other divisor unchanged.
The resulting quotient has nineteen elements.

This quotient is only a set-level model of the expected Abel fibres.  It is
not asserted to be the geometric Picard group.  The structure
`GeometricAbelCriterion` records exactly the geometric statements required
to transfer the same fibre calculation to a genuine Picard target.
-/
namespace MazurProof.N13AbelFiberTwoModel
noncomputable section
open N13GoodModelTwo
open N13SymmetricSquareTwo
/-- The six curve points are the three base points times two sheets. -/
def curvePointEquiv : CurvePoint ≃ BasePoint × K where
  toFun
    | Sum.inl P => (Sum.inl P.1.1, P.1.2)
    | Sum.inr P => (Sum.inr (), P.1)
  invFun
    | (Sum.inl x, y) =>
        Sum.inl ⟨(x, y), (affineEquation_iff_fixed f2_fourth_eq x y).2
          ⟨ZMod.pow_card x, ZMod.pow_card y⟩⟩
    | (Sum.inr _, v) =>
        Sum.inr ⟨v, (infinityChartEquation_zero_iff_fixed v).2
          (ZMod.pow_card v)⟩
  left_inv P := by
    rcases P with P | P
    · rfl
    · rfl
  right_inv P := by
    rcases P with ⟨b, z⟩
    rcases b with x | u
    · rfl
    · cases u
      rfl
/-- The hyperelliptic fibre over `b`, as an effective divisor of degree two. -/
def canonicalDivisor (b : BasePoint) : EffectiveDivisorTwo :=
  s(curvePointEquiv.symm (b, 0), curvePointEquiv.symm (b, 1))
/-- The three divisors in the canonical pencil over `F₂`. -/
def IsCanonical (D : EffectiveDivisorTwo) : Prop :=
  D ∈ Set.range canonicalDivisor
theorem canonicalDivisor_isCanonical (b : BasePoint) :
    IsCanonical (canonicalDivisor b) :=
  Set.mem_range_self b
/-- Equality except that all three canonical divisors are identified. -/
def AbelRel (D E : EffectiveDivisorTwo) : Prop :=
  D = E ∨ IsCanonical D ∧ IsCanonical E
theorem abelRel_equivalence : Equivalence AbelRel where
  refl D := Or.inl rfl
  symm := by
    intro D E h
    rcases h with rfl | ⟨hD, hE⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hE, hD⟩
  trans := by
    intro D E F hDE hEF
    rcases hDE with rfl | ⟨hD, hE⟩
    · exact hEF
    rcases hEF with rfl | ⟨_, hF⟩
    · exact Or.inr ⟨hD, hE⟩
    · exact Or.inr ⟨hD, hF⟩
def abelSetoid : Setoid EffectiveDivisorTwo :=
  ⟨AbelRel, abelRel_equivalence⟩
/-- Set-level quotient obtained by collapsing the canonical pencil. -/
abbrev PicTwoSetModel := Quotient abelSetoid
def abel : EffectiveDivisorTwo → PicTwoSetModel :=
  Quotient.mk''
theorem abel_eq_iff (D E : EffectiveDivisorTwo) :
    abel D = abel E ↔ AbelRel D E :=
  Quotient.eq''
def canonicalClass : PicTwoSetModel :=
  abel (canonicalDivisor baseAtInfinity)
/-! ## Interface to a genuine geometric Picard target -/
set_option maxHeartbeats 4000000 in
/-- The geometric facts needed to transfer the set-level fibre calculation.
Surjectivity is the genus-two Riemann--Roch input; `eq_iff` is the
degree-two linear-equivalence theorem. -/
structure GeometricAbelCriterion (J : Type*) where
  abel : EffectiveDivisorTwo → J
  canonicalClass : J
  canonical_eq :
    ∀ b : BasePoint, abel (canonicalDivisor b) = canonicalClass
  surjective : Function.Surjective abel
  eq_iff :
    ∀ D E : EffectiveDivisorTwo,
      abel D = abel E ↔ AbelRel D E
/-- The intrinsic nineteen-element quotient itself satisfies the geometric
Abel-fibre interface.  This lets later arguments use Abel rigidity without
postulating a separate special Picard-group implementation. -/
def picTwoSetModelCriterion :
    GeometricAbelCriterion PicTwoSetModel where
  abel := abel
  canonicalClass := canonicalClass
  canonical_eq := by
    intro b
    change
      abel (canonicalDivisor b) =
        abel (canonicalDivisor baseAtInfinity)
    rw [abel_eq_iff]
    exact Or.inr
      ⟨canonicalDivisor_isCanonical b,
        canonicalDivisor_isCanonical baseAtInfinity⟩
  surjective := Quotient.mk_surjective
  eq_iff := abel_eq_iff
namespace GeometricAbelCriterion
variable {J : Type*} (G : GeometricAbelCriterion J)
end GeometricAbelCriterion
end
end MazurProof.N13AbelFiberTwoModel
end

end

-- ===== FLT.Assumptions.MazurProof.N13AbelChartBase =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelChartBase =====
section
/-!
# The nonspecial base divisor for the N13 Abel chart

The integral divisor

`(0,0) + (-1,0)`

has generalized Mumford pair `u = X² + X`, `v = 0`.  Its reduction is the
unordered pair of the sheet-zero points over the distinct affine base
coordinates `0` and `1`.  A canonical hyperelliptic fibre contains one
point on each sheet, so this reduced divisor is noncanonical.

The same base pair satisfies a short Bézout identity.  Hence its graph ideal
is one of the smooth integral Mumford ideals already shown to commute with
reduction.
-/
open Polynomial
namespace MazurProof.N13AbelChartBase
noncomputable section
open N13AbelFiberTwoModel
open N13SymmetricSquareTwo
attribute [local instance] MazurProof.N13AbelChartBase.instFactPrimeOfNatNat_fLT
/-- The special-fibre point `(0,0)`. -/
def p00 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 0, 0)
/-- The special-fibre point `(1,0)`, which is the reduction of `(-1,0)`. -/
def p10 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 1, 0)
/-- Reduction of the selected integral degree-two divisor. -/
def specialBaseDivisor :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(p00, p10)
def sheet
    (P : N13AbelFiberTwoModel.CurvePoint) : K :=
  (curvePointEquiv P).2
/-- The smooth integral generalized Mumford datum of the selected base
divisor.  The Bézout certificate is

`(X-1)u + h + 2w = 1`.
-/
def baseSmoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := N13FormalAbelLinearization.uBase
  v := 0
  w := -X ^ 3
  u_monic := N13FormalAbelLinearization.uBase_monic
  curve_eq := by
    simp only [N13GeneralizedMumfordIntegral.hPoly,
      N13GeneralizedMumfordIntegral.rhsPoly,
      N13FormalAbelLinearization.uBase]
    ring
  bezout := by
    refine ⟨X - 1, 1, 2, ?_⟩
    simp only [N13FormalAbelLinearization.uBase,
      N13GeneralizedMumfordIntegral.hPoly]
    ring
@[simp] theorem baseSmoothMumford_u :
    baseSmoothMumford.u =
      N13FormalAbelLinearization.uBase := rfl
@[simp] theorem baseSmoothMumford_v :
    baseSmoothMumford.v = 0 := rfl
/-- The integral base graph reduces to the same polynomial pair
`(X²+X,0)` in characteristic two. -/
theorem reduce_baseSmoothMumford_u :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).u =
        (X ^ 2 + X :
          N13GoodCoordinateRingTwo.K[X]) := by
  simp [baseSmoothMumford,
    N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]
@[simp] theorem reduce_baseSmoothMumford_v :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).v = 0 := by
  simp [baseSmoothMumford,
    N13GeneralizedMumfordReduction.reducePoly]
end
end MazurProof.N13AbelChartBase
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialDualFrame =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDualFrame =====
section
/-!
# The explicit special-fibre dual frame

For the selected nonspecial graph ideal `(X²+X,Y)`, three explicit primal
and multiplier-dual elements have evaluation sum one.  The only
denominator is `(Y+h)/(X²+X)`; its inverse-ideal membership follows
directly from the curve equation.

This is a symbolic certificate in the special affine coordinate ring.  It
does not use invertibility of the graph ideal and is therefore suitable as
the input relation for the two-chart lifting argument.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13SpecialDualFrame
noncomputable section
def quotientDual : F :=
  (yF + hF) / uF
/-- The corresponding multiplier-dual factors. -/
def dual : Fin 3 → F :=
  ![x3F, quotientDual, cF]
end
end MazurProof.N13SpecialDualFrame
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
/-- The fixed reduced smooth Mumford datum. -/
def specialData :
    N13GoodCoordinateRingTwo.SemiMumford :=
  N13GeneralizedMumfordReduction.reduceSmoothMumford
    N13AbelChartBase.baseSmoothMumford
@[simp] theorem specialData_u :
    specialData.u = (X ^ 2 + X : k[X]) :=
  N13AbelChartBase.reduce_baseSmoothMumford_u
@[simp] theorem specialData_v :
    specialData.v = 0 :=
  N13AbelChartBase.reduce_baseSmoothMumford_v
/-- The fixed special graph ideal. -/
abbrev specialIdeal : Ideal A :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    specialData.u specialData.v
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
abbrev SpecialQuotient : Type :=
  SpecialRing ⧸ N13SpecialQuotientBasis.specialIdeal
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.baseSpecialAlgebra
local instance baseSpecialQuotientTower :
    IsScalarTower R₂ k SpecialQuotient :=
  IsScalarTower.of_algebraMap_eq
    (R := R₂) (S := k) (A := SpecialQuotient)
    fun _ => rfl
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
abbrev FunctionField : Type :=
  N13Mumford.FunctionField
    N13IntegralModelContraction.Q₂
abbrev RationalFractionalIdeal : Type :=
  FractionalIdeal RationalRing⁰ FunctionField
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField
/-- The integral graph ideal attached to generalized Mumford data. -/
def graphIdeal (D : SmoothMumford₂) : Ideal IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v
/-- The standard sextic graph ideal of smooth integral data. -/
def sexticIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).v
/-- The standard sextic generic graph attached to arbitrary integral
generalized Mumford data. -/
def sexticSemiIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v
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
theorem curveEquationAtRoot
    (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) :
    N13GoodModelTwo.AffineEquation a (D.v.eval a) := by
  have hc := congrArg (Polynomial.eval a) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at hc
  rw [ha, zero_mul] at hc
  change
    D.v.eval a ^ 2 +
        N13GoodModelTwo.h a * D.v.eval a =
      N13GoodModelTwo.rhs a
  simpa [N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    hPoly, rhsPoly] using sub_eq_zero.mp hc
theorem mumfordIdeal_eq_zero_of_dvd
    (u v : K[X]) (h : u ∣ v) :
    mumfordIdeal u v = mumfordIdeal u 0 := by
  obtain ⟨q, hq⟩ := h
  have hmultiple :
      xClass v ∈ mumfordIdeal u 0 := by
    rw [hq, xClass_mul, mul_comm]
    exact Ideal.mul_mem_left _ (xClass q)
      (xClass_mem_mumfordIdeal u 0)
  have hmultiple' :
      xClass v ∈ mumfordIdeal u v := by
    have hx : xClass v = xClass u * xClass q := by
      rw [hq, xClass_mul]
    rw [hx]
    simpa only [mul_comm] using
      Ideal.mul_mem_left _ (xClass q)
        (xClass_mem_mumfordIdeal u v)
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u 0
    · have heq : ySubClass v = ySubClass 0 - xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal u 0) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u v
    · have heq : ySubClass 0 = ySubClass v + xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal u v) hmultiple'
end
end MazurProof.N13SpecialGraphDivisor
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicDisks =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicDisks =====
section
/-!
# The two integral residue disks used by the N13 Abel chart

For the good equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`

over the two-adic integers, the fibres above the residue disks of `0` and
`-1` have a unique point whose `y`-coordinate lies in the maximal ideal.
Existence is one-variable Hensel lifting in the `y` coordinate.  Uniqueness
is the elementary factorization of the difference of two roots.

This is the local-curve part of the nonspecial Abel chart; it uses neither a
Picard scheme nor finite congruence tables.
-/
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
/-- The maximal ideal `(2)` of the two-adic integers. -/
abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂
/-- A useful local-ring form of the fact that being congruent to a unit
modulo the maximal ideal implies being a unit. -/
theorem isUnit_of_sub_mem_maximal
    {a u : R₂} (hu : IsUnit u)
    (hau : a - u ∈ maximal) :
    IsUnit a := by
  by_contra ha
  have ha_mem : a ∈ maximal := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using ha
  have hu_mem : u ∈ maximal := by
    have hsub := maximal.sub_mem ha_mem hau
    convert hsub using 1
    ring
  have hnot : ¬IsUnit u := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hu_mem
  exact hnot hu
@[simp] theorem yFiber_derivative_eval_zero (x : R₂) :
    (yFiber x).derivative.eval 0 =
      N13GoodModelTwo.h x := by
  rw [N13GoodModelTwo.affineFiber_derivative_eval]
  simp [N13GoodModelTwo.affineDerivativeY]
/-- Hensel lifting in the `Y` coordinate under the exact two hypotheses
needed at a residue disk. -/
theorem exists_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃ y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  have heval :
      (yFiber x).eval 0 ∈ maximal := by
    have hneg := maximal.neg_mem hrhs
    simpa [yFiber_eval, N13GoodModelTwo.affineResidual] using hneg
  have hderiv :
      IsUnit
        (Ideal.Quotient.mk maximal
          ((yFiber x).derivative.eval 0)) := by
    rw [yFiber_derivative_eval_zero]
    exact hh.map (Ideal.Quotient.mk maximal)
  obtain ⟨y, hy, hymem⟩ :=
    HenselianRing.is_henselian
      (R := R₂) (I := maximal)
      (yFiber x) (yFiber_monic x) 0 heval hderiv
  refine ⟨y, ?_, by simpa using hymem⟩
  rw [N13GoodModelTwo.affineEquation_iff_residual,
    ← yFiber_eval]
  exact hy
/-- Two roots in the same selected `Y` residue disk coincide. -/
theorem y_eq_of_mem_maximal
    (x y z : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hz : N13GoodModelTwo.AffineEquation x z)
    (hymem : y ∈ maximal)
    (hzmem : z ∈ maximal) :
    y = z := by
  have hyzero :
      y ^ 2 + N13GoodModelTwo.h x * y -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hy
  have hzzero :
      z ^ 2 + N13GoodModelTwo.h x * z -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hz
  have hsum_mem : y + z ∈ maximal :=
    maximal.add_mem hymem hzmem
  have hunit :
      IsUnit (y + z + N13GoodModelTwo.h x) := by
    apply isUnit_of_sub_mem_maximal hh
    convert hsum_mem using 1
    ring
  have hprod :
      (y - z) *
        (y + z + N13GoodModelTwo.h x) = 0 := by
    calc
      (y - z) *
          (y + z + N13GoodModelTwo.h x) =
        (y ^ 2 + N13GoodModelTwo.h x * y -
            N13GoodModelTwo.rhs x) -
          (z ^ 2 + N13GoodModelTwo.h x * z -
            N13GoodModelTwo.rhs x) := by ring
      _ = 0 := by rw [hyzero, hzzero, sub_self]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right hunit.ne_zero)
/-- The selected `Y` lift is unique whenever the fibre has unit derivative
and its constant term lies in the maximal ideal. -/
theorem existsUnique_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  obtain ⟨y, hy, hymem⟩ :=
    exists_y_mem_maximal x hh hrhs
  refine ⟨y, ⟨hy, hymem⟩, ?_⟩
  intro z hz
  exact y_eq_of_mem_maximal x z y hh hz.1 hy hz.2 hymem
/-! ## The disk above `(0,0)` -/
theorem h_isUnit_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 + 1) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring
theorem rhs_mem_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 3 * (x + 1)) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring
theorem existsUnique_zeroDisk_y
    (x : R₂) (hx : x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_zeroDisk hx)
    (rhs_mem_of_mem_zeroDisk hx)
/-- The unique `Y` coordinate above an `X` in the residue disk of zero. -/
def zeroDiskY (x : R₂) (hx : x ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_zeroDisk_y x hx).exists
theorem zeroDiskY_spec
    (x : R₂) (hx : x ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (zeroDiskY x hx) ∧
      zeroDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_zeroDisk_y x hx).exists
/-! ## The disk above `(-1,0)` -/
theorem h_isUnit_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_neg_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 - x + 2) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring
theorem rhs_mem_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 4) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring
theorem existsUnique_negOneDisk_y
    (x : R₂) (hx : x + 1 ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_negOneDisk hx)
    (rhs_mem_of_mem_negOneDisk hx)
/-- The unique `Y` coordinate above an `X` in the residue disk of `-1`. -/
def negOneDiskY (x : R₂) (hx : x + 1 ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_negOneDisk_y x hx).exists
theorem negOneDiskY_spec
    (x : R₂) (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (negOneDiskY x hx) ∧
      negOneDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_negOneDisk_y x hx).exists
end
end MazurProof.N13TwoAdicDisks
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicKernelChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicKernelChart =====
section
/-!
# A structural two-adic kernel chart

This file isolates the elementary formal-group argument needed for N13.
Suppose an additive group has two coordinates in `ℤ₂`, every coordinate is
divisible by two, and addition differs from coordinatewise addition by an
element of the product of the two coordinate ideals.  Then doubling raises
coordinate depth by at least one.  Infinite two-divisibility is therefore
incompatible with the separated two-adic filtration.

No formal power series, point table, or explicit genus-two addition formula
is used below.  The eventual curve-specific input is only the
cross-quadratic error statement.
-/
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The principal ideal `(2^n)` in the two-adic integers. -/
def powTwoIdeal (n : ℕ) : Ideal R₂ :=
  Ideal.span ({(2 : R₂) ^ n} : Set R₂)
universe u
variable {K : Type u} [AddCommGroup K]
/-- The ideal generated by the two coordinates of `z`. -/
def coordIdeal
    (coord : K → Fin 2 → R₂) (z : K) :
    Ideal R₂ :=
  Ideal.span (Set.range (coord z))
set_option maxHeartbeats 4000000 in
/-- A two-coordinate chart whose transported addition law has only mixed
quadratic and higher error terms. -/
structure Chart (K : Type u) [AddCommGroup K] where
  coord : K → Fin 2 → R₂
  coord_zero : coord 0 = 0
  coord_injective : Function.Injective coord
  coord_mem_two :
    ∀ z i, coord z i ∈ powTwoIdeal 1
  add_error_mem :
    ∀ z w i,
      coord (z + w) i - (coord z i + coord w i) ∈
        coordIdeal coord z * coordIdeal coord w
namespace Chart
variable (C : Chart K)
/-- All chart coordinates have depth at least `n`. -/
def CoordDepth (n : ℕ) (z : K) : Prop :=
  ∀ i, C.coord z i ∈ powTwoIdeal n
include C
end Chart
/-! ## The unary doubling interface

Separatedness only iterates multiplication by two.  The binary addition
estimate above is therefore stronger than necessary: it is enough to know
the same quadratic error estimate on the diagonal. -/
set_option maxHeartbeats 4000000 in
/-- A two-coordinate chart with only the diagonal doubling estimate needed
for two-adic separatedness. -/
structure DoublingChart (K : Type u) [AddCommGroup K] where
  coord : K → Fin 2 → R₂
  coord_zero : coord 0 = 0
  coord_injective : Function.Injective coord
  coord_mem_two :
    ∀ z i, coord z i ∈ powTwoIdeal 1
  double_error_mem :
    ∀ z i,
      coord (2 • z) i - (coord z i + coord z i) ∈
        coordIdeal coord z * coordIdeal coord z
namespace DoublingChart
variable (C : DoublingChart K)
/-- All unary-chart coordinates have depth at least `n`. -/
def CoordDepth (n : ℕ) (z : K) : Prop :=
  ∀ i, C.coord z i ∈ powTwoIdeal n
include C
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
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
abbrev maximal : Ideal R₂ :=
  N13TwoAdicDisks.maximal
set_option maxHeartbeats 4000000 in
/-- A pair of points in the two residue disks used by the nonspecial chart.
The `y`-coordinates are the canonical Hensel lifts and are therefore not
stored separately. -/
structure DiskPair where
  x₀ : R₂
  x₁ : R₂
  x₀_mem : x₀ ∈ maximal
  x₁_add_one_mem : x₁ + 1 ∈ maximal
/-- The distinguished pair `(0,0)+(-1,0)`. -/
def basePair : DiskPair where
  x₀ := 0
  x₁ := -1
  x₀_mem := maximal.zero_mem
  x₁_add_one_mem := by simp
namespace DiskPair
variable (P : DiskPair)
theorem reduceBase_eq_zero_of_mem
    {a : R₂} (ha : a ∈ maximal) :
    N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  apply RingHom.mem_ker.mp
  rw [N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod]
  exact ha
@[simp] theorem reduceBase_x₀ :
    N13GeneralizedMumfordReduction.reduceBase P.x₀ = 0 :=
  reduceBase_eq_zero_of_mem P.x₀_mem
@[simp] theorem reduceBase_x₁ :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ = 1 := by
  have hsum :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ + 1 = 0 := by
    simpa only [map_add, map_one] using
      reduceBase_eq_zero_of_mem P.x₁_add_one_mem
  simpa only [CharTwo.neg_eq] using
    eq_neg_of_add_eq_zero_left hsum
def y₀ : R₂ :=
  N13TwoAdicDisks.zeroDiskY P.x₀ P.x₀_mem
def y₁ : R₂ :=
  N13TwoAdicDisks.negOneDiskY P.x₁ P.x₁_add_one_mem
theorem y₀_spec :
    N13GoodModelTwo.AffineEquation P.x₀ P.y₀ ∧
      P.y₀ ∈ maximal :=
  N13TwoAdicDisks.zeroDiskY_spec P.x₀ P.x₀_mem
theorem y₁_spec :
    N13GoodModelTwo.AffineEquation P.x₁ P.y₁ ∧
      P.y₁ ∈ maximal :=
  N13TwoAdicDisks.negOneDiskY_spec P.x₁ P.x₁_add_one_mem
@[simp] theorem reduceBase_y₀ :
    N13GeneralizedMumfordReduction.reduceBase P.y₀ = 0 :=
  reduceBase_eq_zero_of_mem P.y₀_spec.2
@[simp] theorem reduceBase_y₁ :
    N13GeneralizedMumfordReduction.reduceBase P.y₁ = 0 :=
  reduceBase_eq_zero_of_mem P.y₁_spec.2
theorem x₁_sub_x₀_isUnit :
    IsUnit (P.x₁ - P.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem P.x₀_mem
  convert h using 1
  ring
/-- The inverse of the unit separating the two `x`-coordinates. -/
def deltaInv : R₂ :=
  ↑((P.x₁_sub_x₀_isUnit).unit⁻¹)
theorem deltaInv_mul_delta :
    P.deltaInv * (P.x₁ - P.x₀) = 1 := by
  rw [← (P.x₁_sub_x₀_isUnit).unit_spec]
  exact Units.inv_mul _
/-- The integral linear interpolant taking values `a₀,a₁` at the two
selected `x`-coordinates. -/
def interpolate (a₀ a₁ : R₂) : R₂[X] :=
  C a₀ +
    C (P.deltaInv * (a₁ - a₀)) * (X - C P.x₀)
@[simp] theorem interpolate_eval_x₀ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₀ = a₀ := by
  simp [interpolate]
@[simp] theorem interpolate_eval_x₁ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₁ = a₁ := by
  simp only [interpolate, eval_add, eval_C, eval_mul, eval_sub,
    eval_X]
  calc
    a₀ + P.deltaInv * (a₁ - a₀) * (P.x₁ - P.x₀) =
        a₀ + (a₁ - a₀) *
          (P.deltaInv * (P.x₁ - P.x₀)) := by ring
    _ = a₁ := by rw [P.deltaInv_mul_delta]; ring
/-- The monic polynomial cutting out the two selected affine points. -/
def u : R₂[X] :=
  (X - C P.x₀) * (X - C P.x₁)
/-- The graph polynomial through the two selected affine points. -/
def v : R₂[X] :=
  P.interpolate P.y₀ P.y₁
theorem u_monic : P.u.Monic := by
  exact (monic_X_sub_C P.x₀).mul (monic_X_sub_C P.x₁)
@[simp] theorem v_eval_x₀ :
    P.v.eval P.x₀ = P.y₀ :=
  P.interpolate_eval_x₀ P.y₀ P.y₁
@[simp] theorem v_eval_x₁ :
    P.v.eval P.x₁ = P.y₁ :=
  P.interpolate_eval_x₁ P.y₀ P.y₁
/-- The generalized-hyperelliptic residual after restriction to the graph
`Y=v(X)`. -/
def curveError : R₂[X] :=
  P.v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly * P.v -
    N13GeneralizedMumfordIntegral.rhsPoly
/-- The vertical derivative `2v+h` restricted to the graph. -/
def verticalDerivative : R₂[X] :=
  2 * P.v + N13GeneralizedMumfordIntegral.hPoly
@[simp] theorem verticalDerivative_eval_x₀ :
    P.verticalDerivative.eval P.x₀ =
      2 * P.y₀ + N13GoodModelTwo.h P.x₀ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]
@[simp] theorem verticalDerivative_eval_x₁ :
    P.verticalDerivative.eval P.x₁ =
      2 * P.y₁ + N13GoodModelTwo.h P.x₁ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]
theorem verticalDerivative_eval_x₀_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₀) := by
  rw [P.verticalDerivative_eval_x₀]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₀_spec.2
  convert h using 1
  ring
theorem verticalDerivative_eval_x₁_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₁) := by
  rw [P.verticalDerivative_eval_x₁]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk
      P.x₁_add_one_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₁_spec.2
  convert h using 1
  ring
def derivativeInv₀ : R₂ :=
  ↑((P.verticalDerivative_eval_x₀_isUnit).unit⁻¹)
def derivativeInv₁ : R₂ :=
  ↑((P.verticalDerivative_eval_x₁_isUnit).unit⁻¹)
/-- Interpolate the inverses of the two vertical derivatives. -/
def derivativeInverse : R₂[X] :=
  P.interpolate P.derivativeInv₀ P.derivativeInv₁
@[simp] theorem reducePoly_u :
    N13GeneralizedMumfordReduction.reducePoly P.u =
      (X ^ 2 + X :
        N13GoodCoordinateRingTwo.K[X]) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp only [u, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C,
    P.reduceBase_x₀, P.reduceBase_x₁, C_0, C_1, sub_zero]
  rw [CharTwo.sub_eq_add]
  ring
@[simp] theorem reducePoly_v :
    N13GeneralizedMumfordReduction.reducePoly P.v = 0 := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp [v, interpolate]
/-- Coordinates centered at the distinguished pair. -/
def coord : DiskPair → Fin 2 → R₂ :=
  fun Q => ![Q.x₀, Q.x₁ + 1]
@[simp] theorem coord_zero (Q : DiskPair) :
    coord Q 0 = Q.x₀ := rfl
@[simp] theorem coord_one (Q : DiskPair) :
    coord Q 1 = Q.x₁ + 1 := rfl
@[simp] theorem coord_basePair :
    coord basePair = 0 := by
  funext i
  fin_cases i <;> simp [coord, basePair]
theorem coord_mem_maximal
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈ maximal := by
  fin_cases i
  · exact Q.x₀_mem
  · exact Q.x₁_add_one_mem
theorem maximal_eq_powTwoIdeal_one :
    maximal =
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  change IsLocalRing.maximalIdeal R₂ = _
  rw [PadicInt.maximalIdeal_eq_span_p,
    N13TwoAdicKernelChart.powTwoIdeal, pow_one]
  norm_num
theorem coord_mem_two
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  rw [← maximal_eq_powTwoIdeal_one]
  exact coord_mem_maximal Q i
theorem coord_injective :
    Function.Injective coord := by
  intro P Q hPQ
  have hx₀ := congrFun hPQ (0 : Fin 2)
  have hx₁ := congrFun hPQ (1 : Fin 2)
  cases P
  cases Q
  simp_all [coord]
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
theorem coordinateToAlgebraic_xClass (p : K[X]) :
    coordinateToAlgebraic K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      AdjoinRoot.of (curvePolyRat K)
        (algebraMap K[X] (RatFunc K) p) := by
  simpa only [SexticMumford.xClass, SexticMumford.mk, Polynomial.map_C,
    AdjoinRoot.mk_C] using coordinateToAlgebraic_mk K (C p)
def coordinateConstUnit (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c
def functionConstUnit (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnit K c)
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
def ySeriesMinus : LaurentSeries K := -(N13Infinity.ySeries K)
@[simp] theorem ySeriesMinus_eq_neg :
    ySeriesMinus K = -(N13Infinity.ySeries K) := rfl
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
end
end MazurProof.N13InfinityMinus
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem wSeries_coeff_zero :
    (wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, sqrtReverseF_constantCoeff]
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

-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
@[simp] lemma order_parameter_inv_pow (n : ℕ) :
    ((parameter K)⁻¹ ^ n).order = -(n : ℤ) := by
  rw [parameter_inv, HahnSeries.order_pow]
  simp [HahnSeries.order_single]
lemma order_eval_parameter_reverse (p : K[X]) (hp : p ≠ 0) :
    (p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)).order = 0 := by
  rw [eval_parameter_eq_ofPowerSeries]
  apply order_ofPowerSeries_of_coeff_zero_ne
  simpa using p.leadingCoeff_ne_zero.mpr hp
theorem order_evalAtInfinity (p : K[X]) (hp : p ≠ 0) :
    (evalAtInfinity K p).order = -(p.natDegree : ℤ) := by
  rw [evalAtInfinity_eq_reverse_mul, HahnSeries.order_mul]
  · rw [order_eval_parameter_reverse K p hp, order_parameter_inv_pow]
    simp
  · rw [eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _ (inv_ne_zero (parameter_ne_zero K))
end
end N13LaurentPolynomialOrder
end MazurProof
end

end

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K] in
theorem evalPoly_order (p : K[X]) (hp : p ≠ 0) :
    (evalPoly K p).order = -(p.natDegree : ℤ) := by
  rw [evalPoly_eq_evalAtInfinity]
  exact N13LaurentPolynomialOrder.order_evalAtInfinity K p hp
def linearFunction (p q : K[X]) : N13Mumford.CoordinateRing K :=
  SexticMumford.xClass (N13Mumford.model K) p +
    SexticMumford.xClass (N13Mumford.model K) q *
      SexticMumford.yClass (N13Mumford.model K)
end
end MazurProof.N13BranchNorm
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
def conjugateSemiMumford (M : Model K) (D : SemiMumford M) :
    SemiMumford M where
  u := D.u
  v := -D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := by
    rw [← Polynomial.modByMonic_eq_mod (-D.v) D.u_monic,
      Polynomial.neg_modByMonic,
      Polynomial.modByMonic_eq_mod D.v D.u_monic,
      D.v_reduced]
  curve_dvd := by
    simpa only [neg_sq] using D.curve_dvd
@[simp] theorem conjugateSemiMumford_u (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).u = D.u := rfl
@[simp] theorem conjugateSemiMumford_v (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).v = -D.v := rfl
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
/-- The ideal of all `Y` coefficients of elements of an integral ideal. -/
def yCoeffIdeal (J : Ideal (CoordinateRing M)) : Ideal K[X] where
  carrier :=
    { b | ∃ z : CoordinateRing M, z ∈ J ∧ coeffY M z = b }
  zero_mem' := ⟨0, J.zero_mem, map_zero (coeffY M)⟩
  add_mem' := by
    rintro b₁ b₂ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₁ + z₂, J.add_mem hz₁ hz₂, map_add (coeffY M) z₁ z₂⟩
  smul_mem' := by
    rintro r b ⟨z, hz, rfl⟩
    refine ⟨xClass M r * z, J.mul_mem_left (xClass M r) hz, ?_⟩
    exact coeffY_xClass_mul M r z
/-- A canonical (not prematurely normalized) generator of the coefficient
content. -/
def contentGenerator (J : Ideal (CoordinateRing M)) : K[X] :=
  Submodule.IsPrincipal.generator (yCoeffIdeal M J)
/-! ## Division by content as a colon ideal -/
/-! ## Fractional invertibility -/
/-! ## Oriented primitive representatives -/
def contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M d))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hd))
@[simp] theorem coe_contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (contentFunctionUnit M d hd : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M d) := rfl
namespace IntegralOrientedRep
variable (O : InfinityOrder M)
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
/-- Replacing `v` by a congruent polynomial modulo `u` does not change the
Mumford ideal. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v V : K[X]) (h : u ∣ V - v) :
    mumfordIdeal M u V = mumfordIdeal M u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u v
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u v := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u v)
      have heq :
          ySubClass M V =
            ySubClass M v - xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal M u v) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u V
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u V := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u V)
      have heq :
          ySubClass M v =
            ySubClass M V + xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal M u V) hmultiple
/-! ## The Cantor product identity -/
/-! ## Degree descent -/
/-! ## The normalized next semirepresentative -/
/-! ## Conjugating the complement -/
/-! ## Principal functions in one oriented step -/
def xClassFunctionUnit (p : K[X]) (hp : p ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M p))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hp))
@[simp] theorem coe_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    (xClassFunctionUnit M p hp : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M p) := rfl
/-! ## Exact oriented update -/
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
/-- At degree three use the monic lift `v+u`; otherwise use the reduced
graph polynomial itself. -/
def degreeLift (D : SemiMumford M) : K[X] :=
  if D.u.natDegree = 3 then D.v + D.u else D.v
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- A semi-Mumford representative together with the terminal affine degree
bound.  This does not yet impose the independent infinity-balance bounds. -/
structure LowDegreeSemi where
  toSemi : SemiMumford M
  degree_le_two : toSemi.u.natDegree ≤ 2
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
abbrev M : SexticMumford.Model K := N13Mumford.model K
omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq_natDegree_le :
    (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤ 2 := by
  rw [f_sub_sqrtInfinity_sq]
  compute_degree!
variable (D : N13Mumford.SemiMumford K)
/-! ## The two adapted lifts -/
def plusRemainder : K[X] :=
  (sqrtInfinity - D.v) % D.u
/-- Congruent to `v` and monic cubic; adapted to the positive branch. -/
def plusLift : K[X] :=
  sqrtInfinity - plusRemainder D
def minusRemainder : K[X] :=
  (-sqrtInfinity - D.v) % D.u
/-- Congruent to `v`, with `-minusLift` monic cubic. -/
def minusLift : K[X] :=
  -sqrtInfinity - minusRemainder D
theorem plusLift_congr :
    D.u ∣ plusLift D - D.v := by
  unfold plusLift plusRemainder
  convert sub_mod_dvd (sqrtInfinity - D.v) D.u using 1
  all_goals ring
theorem minusLift_congr :
    D.u ∣ minusLift D - D.v := by
  unfold minusLift minusRemainder
  convert sub_mod_dvd (-sqrtInfinity - D.v) D.u using 1
  all_goals ring
theorem curve_dvd_of_congr
    (V : K[X]) (hV : D.u ∣ V - D.v) :
    D.u ∣ N13Mumford.f K - V ^ 2 := by
  obtain ⟨a, ha⟩ := D.curve_dvd
  change N13Mumford.f K - D.v ^ 2 = D.u * a at ha
  obtain ⟨b, hb⟩ := hV
  refine ⟨a - b * (V + D.v), ?_⟩
  calc
    N13Mumford.f K - V ^ 2 =
        (N13Mumford.f K - D.v ^ 2) -
          (V - D.v) * (V + D.v) := by ring
    _ = D.u * a - (D.u * b) * (V + D.v) := by
          rw [ha, hb]
    _ = D.u * (a - b * (V + D.v)) := by ring
theorem plusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (plusLift D) ^ 2 :=
  curve_dvd_of_congr D (plusLift D) (plusLift_congr D)
theorem minusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (minusLift D) ^ 2 :=
  curve_dvd_of_congr D (minusLift D) (minusLift_congr D)
def plusFactor : K[X] :=
  Classical.choose (plusLift_curve_dvd D)
theorem plusFactor_spec :
    N13Mumford.f K - (plusLift D) ^ 2 =
      D.u * plusFactor D :=
  Classical.choose_spec (plusLift_curve_dvd D)
def minusFactor : K[X] :=
  Classical.choose (minusLift_curve_dvd D)
theorem minusFactor_spec :
    N13Mumford.f K - (minusLift D) ^ 2 =
      D.u * minusFactor D :=
  Classical.choose_spec (minusLift_curve_dvd D)
/-! ## Degree bounds -/
theorem mod_natDegree_lt
    (p : K[X]) (hpos : 0 < D.u.natDegree) :
    (p % D.u).natDegree < D.u.natDegree := by
  by_cases hr : p % D.u = 0
  · rw [hr]
    simp
    exact hpos
  · exact natDegree_lt_natDegree hr
      (degree_mod_lt p D.u_monic.ne_zero)
theorem mod_eq_zero_of_natDegree_eq_zero
    (p : K[X]) (hzero : D.u.natDegree = 0) :
    p % D.u = 0 := by
  have hu : D.u = 1 :=
    eq_one_of_monic_natDegree_zero D.u_monic hzero
  rw [hu]
  simp
theorem plusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (plusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (sqrtInfinity - D.v) hpos
theorem minusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (minusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (-sqrtInfinity - D.v) hpos
theorem plusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    plusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero
theorem minusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    minusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero
theorem plusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (plusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := plusRemainder_natDegree_lt D hpos
    omega
theorem minusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (minusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := minusRemainder_natDegree_lt D hpos
    omega
theorem plusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (plusLift D) 3 := by
  unfold plusLift
  exact sqrtInfinity_isMonicOfDegree.sub
    (by have := plusRemainder_natDegree_le_one D hdeg; omega)
theorem neg_minusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (-minusLift D) 3 := by
  have hmonic :
      IsMonicOfDegree
        (sqrtInfinity + minusRemainder D : K[X]) 3 :=
    sqrtInfinity_isMonicOfDegree.add_right
      (by have := minusRemainder_natDegree_le_one D hdeg; omega)
  convert hmonic using 1
  unfold minusLift
  ring
theorem adaptedNumerator_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_add_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)
theorem adaptedNumeratorNeg_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_sub_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)
theorem plusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (plusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusLift, plusRemainder_eq_zero D hzero]
    simp only [sub_zero]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (plusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * plusRemainder D -
          (plusRemainder D) ^ 2 by
      unfold plusLift
      ring]
    exact adaptedNumerator_natDegree_le
      (plusRemainder D) hdeg (plusRemainder_natDegree_lt D hpos)
theorem minusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (minusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusLift, minusRemainder_eq_zero D hzero]
    simp only [sub_zero, neg_sq]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (minusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * minusRemainder D -
          (minusRemainder D) ^ 2 by
      unfold minusLift
      ring]
    exact adaptedNumeratorNeg_natDegree_le
      (minusRemainder D) hdeg (minusRemainder_natDegree_lt D hpos)
/-! ## Leading terms at the two infinities -/
omit [CharZero K] in
theorem evalPoly_coeff_neg_three_eq_zero
    (p : K[X]) (hdeg : p.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K p).coeff (-3 : ℤ) = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · by_contra hcoeff
    have horder :
        (N13BranchNorm.evalPoly K p).order ≤ (-3 : ℤ) :=
      HahnSeries.order_le_of_coeff_ne_zero hcoeff
    rw [N13BranchNorm.evalPoly_order K p hp] at horder
    omega
theorem wSeries_coeff_zero :
    (N13Infinity.wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K
    (N13Infinity.sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]
theorem ySeries_coeff_neg_three :
    (N13Infinity.ySeries K).coeff (-3 : ℤ) = 1 := by
  simp only [N13Infinity.ySeries, N13Infinity.parameter,
    HahnSeries.inv_single, inv_one,
    HahnSeries.single_pow, one_pow]
  rw [HahnSeries.coeff_single_mul]
  norm_num
  exact wSeries_coeff_zero (K := K)
theorem evalPlusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [plusLift, map_sub, HahnSeries.coeff_sub,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (plusRemainder D) (by
      exact (plusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num
theorem linearFunction_neg_eq_ySubClass
    (V : K[X]) :
    N13BranchNorm.linearFunction K (-V) 1 =
      ySubClass (N13Mumford.model K) V := by
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring
/-! ## Exact orders of the principal Cantor corrections -/
theorem plusNormNumerator_eq :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 =
      -(D.u * plusFactor D) := by
  simp only [N13BranchNorm.normNumerator, neg_sq, one_pow, one_mul]
  rw [← plusFactor_spec D]
  ring
/-! ## The two class-preserving balancing steps -/
abbrev LowDegree :
    Type u :=
  LowDegreeSemi (N13Mumford.model K)
/-! ## A well-founded measure for the two balance walls -/
def lowerDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat (-E.toSemi.nInf)
def upperDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat
    ((E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2)
def imbalance (E : LowDegree (K := K)) : ℕ :=
  lowerDefect E + upperDefect E
/-! ## Structural infinity balancing -/
def toBalanced
    (E : LowDegree (K := K))
    (hzero : 0 ≤ E.toSemi.nInf)
    (hupper :
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2) :
    N13Mumford.Mumford K where
  u := E.toSemi.u
  v := E.toSemi.v
  nInf := Int.toNat E.toSemi.nInf
  u_monic := E.toSemi.u_monic
  deg_u := E.degree_le_two
  v_reduced := E.toSemi.v_reduced
  curve_dvd := E.toSemi.curve_dvd
  infinity_bound := by
    have hn :
        ((Int.toNat E.toSemi.nInf : ℕ) : ℤ) =
          E.toSemi.nInf :=
      Int.toNat_of_nonneg hzero
    omega
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
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair
namespace DiskPair
variable (P : DiskPair)
theorem u_natDegree :
    P.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C P.x₀).ne_zero
      (monic_X_sub_C P.x₁).ne_zero]
  simp
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
abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Smooth integral Mumford data whose graph has the selected nonspecial
special fibre. -/
structure NearBaseMumford
    extends N13GeneralizedMumfordReduction.SmoothMumford₂ where
  reduce_u :
    N13GeneralizedMumfordReduction.reducePoly u =
      (X ^ 2 + X : K[X])
  reduce_v :
    N13GeneralizedMumfordReduction.reducePoly v = 0
namespace NearBaseMumford
variable (D : NearBaseMumford)
theorem mem_maximal_iff_reduceBase_eq_zero
    (a : R₂) :
    a ∈ maximal ↔
      N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  constructor
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) := by
      rw [PadicInt.ker_toZMod]
      exact ha
    exact RingHom.mem_ker.mp hker
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) :=
      RingHom.mem_ker.mpr ha
    rw [PadicInt.ker_toZMod] at hker
    exact hker
theorem isUnit_of_reduceBase_eq_one
    {a : R₂}
    (ha :
      N13GeneralizedMumfordReduction.reduceBase a = 1) :
    IsUnit a := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  apply (mem_maximal_iff_reduceBase_eq_zero (a - 1)).2
  rw [map_sub, ha, map_one, sub_self]
theorem u_eval_zero_mem :
    D.u.eval 0 ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
theorem derivative_eval_zero_isUnit :
    IsUnit (D.u.derivative.eval 0) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
/-- The root of `u` in the residue disk of zero. -/
theorem exists_root_zeroDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic 0 D.u_eval_zero_mem
      (D.derivative_eval_zero_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx
/-- The two Hensel roots, selected in their distinct residue disks. -/
def x₀ : R₂ :=
  Classical.choose D.exists_root_zeroDisk
theorem x₀_spec :
    D.u.eval D.x₀ = 0 ∧ D.x₀ ∈ maximal :=
  Classical.choose_spec D.exists_root_zeroDisk
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
/-- The quotient in the generalized Mumford equation after replacing
`v` by its monic remainder modulo `u`. -/
def normalizedW (D : SmoothMumford₂) : R₂[X] :=
  D.w -
      graphQuotient D *
        (2 * D.v +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
    D.u * graphQuotient D ^ 2
end
end MazurProof.N13AbelCompatibleGraphRecover
end

end

-- ===== FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery =====
section
-- ===== FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery =====
section
/-!
# Recovering the integral N13 graph from the concrete two-fibre basis

The literal basis `{1,x}` turns multiplication by `x` into a monic
characteristic polynomial of degree two.  Expressing the quotient class of
`y` in that basis then recovers the canonical contraction literally as a
generalized Mumford graph ideal.
-/
open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13ConcreteGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13ConcreteGraphRecovery.instFactPrimeOfNatNat_fLT
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
end
end MazurProof.N13ConcreteGraphRecovery
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
abbrev RationalRing : Type := N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
end
end MazurProof.N13GenericQuotientLocalization
end

end

-- ===== FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis =====
section
-- ===== FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis =====
section
open Module
open Polynomial
open scoped TensorProduct
/-!
# Coordinate bases for finite quadratic contractions

For a finite canonical contraction of a quadratic N13 Mumford quotient,
the special fibre is a two-dimensional algebra generated by the literal
coordinates `x` and `y`.  Thus either `{1,x}` or `{1,y}` is a basis on the
special fibre.  Finite flat lifting gives the same literal alternative
over the two-adic integers.
-/
namespace MazurProof.N13ContractQuotientXYBasis
noncomputable section
universe uF uK uA uι
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.instFactPrimeOfNatNat_fLT
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.baseSpecialAlgebra
end
end MazurProof.N13ContractQuotientXYBasis
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
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField
open N13GeneralizedMumfordIntegral
/-- The odd resultant scalar in the Jacobian certificate is a unit in the
integral coordinate ring. -/
theorem thirteen_isUnit :
    IsUnit (13 : IntegralRing) := by
  have h : IsUnit (13 : R₂) := by
    rw [PadicInt.isUnit_iff]
    exact
      PadicInt.norm_natCast_eq_one_iff.mpr
        (by norm_num)
  convert h.map (algebraMap R₂ IntegralRing) using 1
  exact
    (map_natCast (algebraMap R₂ IntegralRing) 13).symm
/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/
end
end MazurProof.N13IntegralGraphJacobian
end

end

-- ===== FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery =====
section
-- ===== FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery =====
section
/-!
# Recovering an integral semigraph from a rank-two quotient basis

The graph-recovery algebra does not need a selected special divisor until
one asks for a particular vertical smoothness certificate.  A literal
integral quotient basis `{1,x}` already recovers a monic quadratic
generalized Mumford semigraph and identifies its graph ideal with the
canonical contraction.

This is the special-class-independent core needed for arbitrary proper
specialization.
-/
open Module
open Polynomial
namespace MazurProof.N13RankTwoSemiGraphRecovery
noncomputable section
abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model
end
end MazurProof.N13RankTwoSemiGraphRecovery
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
abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model
namespace VerticalGraph
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
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField
open N13GeneralizedMumfordIntegral
open N13RankTwoVerticalGraphRecovery
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
abbrev RationalRing : Type := N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type := N13IntegralGraphJacobian.FunctionField
abbrev Model : SexticMumford.Model N13IntegralModelContraction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M
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
@[simp] theorem h_coeff_one :
    h.coeff 1 = pi * (70 + 34 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num
@[simp] theorem h_coeff_two :
    h.coeff 2 = pi ^ 2 * (1 + 2 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num
/-- Translation preserves the computed discriminant; here this is verified
directly from the cubic formula. -/
theorem h_discr : h.discr = pi ^ 2 := by
  rw [Polynomial.discr_of_degree_eq_three h_degree]
  rw [h_coeff_zero, h_coeff_one, h_coeff_two, h_coeff_three]
  ext <;> norm_num [pi, i, pow_two, pow_succ]
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFactorization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFactorization =====
section
/-!
# Gaussian factorization of the N13 sextic

The N13 sextic is the norm of a cubic over the Gaussian rationals.  This is
the structural input for a Gaussian two-descent.
-/
open Polynomial
namespace MazurProof.N13GaussianFactorization
noncomputable section
/-- The Gaussian unit `i`. -/
def gaussianI : GaussianQ := ⟨0, 1⟩
@[simp] theorem gaussianI_sq : gaussianI * gaussianI = -1 := by
  ext <;> simp [gaussianI, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
end
end MazurProof.N13GaussianFactorization
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
/-- Twice the order-four torsion unit. -/
def Z : ℚ[X] := 2 * X ^ 5 + 7 * X ^ 4 + 9 * X ^ 3 + X ^ 2 + 4 * X + 3
/-- Twice the first fundamental unit. -/
def E₁ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 3 * X ^ 3 - 3 * X
/-- Twice the second fundamental unit. -/
def E₂ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1
def zeta : SexticAlgebra := halfOfPoly Z
def e1 : SexticAlgebra := halfOfPoly E₁
def e2 : SexticAlgebra := halfOfPoly E₂
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
/-- The integral N13 sextic is irreducible by its irreducible reduction
modulo three. -/
theorem fInt_irreducible : Irreducible fInt := by
  apply fInt_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3)) fInt
  simpa [fModThree] using fModThree_irreducible
/-- The sextic defining the N13 Mumford model is irreducible over `ℚ`. -/
theorem n13Mumford_f_irreducible :
    Irreducible (N13Mumford.f ℚ) := by
  rw [← fInt_map_rat]
  exact
    fInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      fInt_irreducible
/-- The same irreducibility statement in the notation used by the fake
square-class target. -/
theorem squareclass_f_irreducible :
    Irreducible N13SexticSquareclass.f := by
  simpa [N13SexticSquareclass.f] using n13Mumford_f_irreducible
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
def gaussianI : Lg :=
  algebraMap K Lg
    (algebraMap GI K N13GaussianGlobalArithmetic.i)
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
abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ
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
abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ
abbrev R : Type :=
  N13Mumford.CoordinateRing ℚ
abbrev F : Type :=
  N13Mumford.FunctionField ℚ
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
abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ
abbrev LowRep : Type :=
  SexticMumford.LowDegreeSemi M
/-- The low-degree semirepresentative of the identity. -/
def zeroLow : LowRep where
  toSemi := (SexticMumford.zero M).toSemi
  degree_le_two := (SexticMumford.zero M).deg_u
end
end MazurProof.N13LowDegreeKummerHom
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerNorm =====
section
/-!
# The square norm of an N13 Mumford Kummer value

For a Mumford pair `(u,v)`, the relation

`f - v² = u w`

implies structurally that

`Norm(u(θ)) = Res(f,u) = Res(u,v)²`.

This is the global norm condition used by the weak two-descent.  The proof
uses functorial identities of the resultant; it neither splits `u` nor
separates its possible degrees.
-/
open Polynomial
namespace MazurProof.N13MumfordKummerNorm
noncomputable section
abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep
/-- The canonical rational square root supplied by the Mumford congruence. -/
def normRoot (D : LowRep) : ℚ :=
  D.toSemi.u.resultant D.toSemi.v
end
end MazurProof.N13MumfordKummerNorm
end

end

-- ===== FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic =====
section
/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
/-!
# Basic

Material destined for Mathlib.
-/
section
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R
end
end

end

-- ===== FLT.Mathlib.RingTheory.Valuation.ValuationSubring =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Mathlib.RingTheory.Valuation.ValuationSubring =====
section
/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
-/
/-!
# Valuation Subring

Material destined for Mathlib.
-/
section
variable {F : Type*} [Field F]
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩
end
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
-- shortcut instances for next def: needed after mathlib #34045
-- dirty hack because of v4.29
namespace adicCompletion
-- IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
-- shortcut instance for next theorem: needed after mathlib #34045
variable {K} in
open scoped Multiplicative in
theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  rw [ValuationSubring.isUnit_iff_valued_eq_one, ← WithZero.coe_one, ← ofAdd_zero, hπ]
  apply ne_of_lt
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega
end adicCompletion
end IsDedekindDomain.HeightOneSpectrum
end
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
theorem residueCubic_irreducible : Irreducible residueCubic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, residueCubic_natDegree]
    omega
  · intro x
    fin_cases x
    · simp only [Polynomial.IsRoot, residueCubic, eval_add, eval_pow, eval_X,
        eval_one]
      change (1 : ZMod 2) ≠ 0
      decide
    · simp only [Polynomial.IsRoot, residueCubic, eval_add, eval_pow, eval_X,
        eval_one]
      change (1 : ZMod 2) ≠ 0
      decide
instance residueCubicIrreducibleFact :
    Fact (Irreducible residueCubic) :=
  ⟨residueCubic_irreducible⟩
instance instCharPF8OfNatNat : CharP F8 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2
theorem alpha_relation :
    alpha ^ 3 + alpha + 1 = 0 := by
  change AdjoinRoot.mk residueCubic (X ^ 3 + X + 1) = 0
  rw [← residueCubic, AdjoinRoot.mk_self]
theorem charTwo : (2 : F8) = 0 :=
  CharP.cast_eq_zero F8 2
theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  have hm : alpha ^ 3 + alpha = 0 := by rw [h]; norm_num
  have hone : (1 : F8) = 0 := by
    linear_combination alpha_relation - hm
  exact one_ne_zero hone
theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have hr := alpha_relation
  rw [h] at hr
  have hone : (1 : F8) = 0 := by
    linear_combination hr - charTwo
  exact one_ne_zero hone
theorem alpha_sq_add_one_ne_zero : alpha ^ 2 + 1 ≠ 0 := by
  intro h
  have hm : alpha ^ 3 + alpha = 0 := by
    calc
      alpha ^ 3 + alpha = alpha * (alpha ^ 2 + 1) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hone : (1 : F8) = 0 := by
    linear_combination alpha_relation - hm
  exact one_ne_zero hone
theorem alpha_sq_add_alpha_add_one_ne_zero :
    alpha ^ 2 + alpha + 1 ≠ 0 := by
  intro h
  have hfac : alpha ^ 2 * (alpha - 1) = 0 := by
    linear_combination alpha_relation - h
  rcases mul_eq_zero.mp hfac with ha | ha
  · exact (pow_ne_zero 2 alpha_ne_zero) ha
  · exact alpha_ne_one (sub_eq_zero.mp ha)
/-! ## The four generator jets -/
abbrev JetUnit : Type :=
  (DualNumber F8)ˣ
/-! ## Structural collapse of the candidate space -/
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
/-- The residue of the cubic generator in the first-jet quotient. -/
def thetaDual : DualNumber F8 :=
  inl alpha
/-- The image of the Gaussian unit `i` under `i ↦ 1 + ε`. -/
def gaussianIDual : DualNumber F8 :=
  (1, 1)
/-! ## `ℚ₂` and `ℤ₂` adapters -/
end
end MazurProof.N13LocalDlogRegimes
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
/-- The Gaussian unit inside the relative maximal order. -/
def relativeI : RelativeO :=
  algebraMap GI RelativeO N13GaussianGlobalArithmetic.i
end
end MazurProof.N13GaussianGlobalReductionTwo
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
def relativeZeta : RelativeO :=
  N13GaussianGlobalReductionTwo.relativeI
/-! ## The global first-jet logarithm -/
/-! ## Structural generation of all unit squareclasses -/
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam =====
section
/-!
# The normalized and actual N13 fake squareclasses

The integral Kummer representative differs from the actual Mumford value by
a nonzero rational scalar.  The fake squareclass quotient kills precisely
such scalars, so the two values have the same fake squareclass.

The only technical seam is that the Gaussian--sextic equivalence and the
current sextic field presentation were compiled under definitionally
different rational algebra instances.  Uniqueness of a ring homomorphism out
of `ℚ` identifies the two scalar maps without unfolding either presentation.
-/
namespace MazurProof.N13GaussianNormalizedSquareclassSeam
noncomputable section
open N13GaussianNormalizationOrderTransport
abbrev LowRep := N13LowDegreeKummerHom.LowRep
end
end MazurProof.N13GaussianNormalizedSquareclassSeam
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
def cuspPoint : Cusp13 →
    SexticMumford.CurvePoint (N13Mumford.model ℚ) :=
  N13Mumford.cuspPoint
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
abbrev M := N13Mumford.model ℚ
def infinityHalf : Mumford M where
  u := halfU
  v := halfV
  nInf := 0
  u_monic := halfU_monic
  deg_u := halfU_natDegree.le
  v_reduced := by
    rw [mod_eq_self_iff halfU_monic.ne_zero]
    have hv : halfV.natDegree = 1 := by
      unfold halfV
      compute_degree!
      all_goals norm_num [Polynomial.coeff_one]
    rw [degree_eq_natDegree (by
      intro h
      have := congrArg (fun p : ℚ[X] => p.coeff 1) h
      norm_num [halfV, Polynomial.coeff_one] at this),
      degree_eq_natDegree halfU_monic.ne_zero,
      hv, halfU_natDegree]
    norm_num
  curve_dvd := by
    exact ⟨X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X - 2,
      half_curve_factor⟩
  infinity_bound := by simp [halfU_natDegree]
def halfFunction : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ (-N13GaussianFactorization.A) 1
theorem halfFunction_ne_zero : halfFunction ≠ 0 := by
  intro h
  have hY := congrArg (coeffY M) h
  simp [halfFunction, N13BranchNorm.linearFunction] at hY
def halfFunctionUnit : (N13Mumford.FunctionField ℚ)ˣ :=
  Units.mk0
    (algebraMap (N13Mumford.CoordinateRing ℚ)
      (N13Mumford.FunctionField ℚ) halfFunction)
    (by simpa using (IsFractionRing.injective
      (N13Mumford.CoordinateRing ℚ)
      (N13Mumford.FunctionField ℚ)).ne halfFunction_ne_zero)
end
end MazurProof.N13InfinityHalf
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
abbrev M :=
  N13Mumford.model ℚ
end
end MazurProof.N13KummerKernelAssembly
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
abbrev LowRep := N13LowDegreeKummerHom.LowRep
abbrev JetUnit := (DualNumber F8)ˣ
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
abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ
end
end MazurProof.N13MumfordKummerHom
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
abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep
/-- The exponent carried by the oriented infinity coordinate. -/
def orientationExponent (D : LowRep) : ℤ :=
  D.toSemi.nInf - 1
/-! ## The two oriented base classes -/
/-! ## The full lift of the actual structural Kummer map -/
end
end MazurProof.N13MumfordOrientedFullKummer
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
abbrev M : SexticMumford.Model ℚ :=
  N13LowDegreeKummerHom.M
abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep
/-! ## Unfolding the full-gauge fibre -/
/-! ## The canonical polynomial square-root witness -/
theorem sextic_f_monic :
    N13SexticSquareclass.f.Monic := by
  exact N13Mumford.f_monic (K := ℚ)
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
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
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
/-!
# Base change of oriented Picard classes for smooth sextics

An injective coefficient map carrying one sextic equation to another induces
maps on the affine coordinate rings, their fraction fields, and invertible
fractional ideals.  If the distinguished infinity orders are compatible,
the resulting map on oriented fractional ideals descends to an additive map
of the concrete oriented Picard groups.

The construction is algebraic: extension of fractional ideals and a quotient
universal property.  It does not use a relative Picard scheme.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- Coefficient extension on the affine sextic coordinate ring. -/
def coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    CoordinateRing M →+* CoordinateRing M' :=
  AdjoinRoot.map (mapPoly ι) (curvePoly M) (curvePoly M')
    (target_curve_dvd ι hM)
end
end MazurProof.SexticMumford.OrientedBaseChange
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
abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField
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
abbrev RationalRing : Type :=
  N13IntegralFiberDetection.RationalRing
abbrev FunctionField : Type :=
  N13IntegralFiberDetection.FunctionField
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
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField
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
namespace Data
variable {G : Type u} {S : Type v} [AddCommGroup G]
end Data
abbrev SpecialSet : Type :=
  N13AbelFiberTwoModel.PicTwoSetModel
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
/-- Recover the named rational cusp from its special base point and sheet. -/
def cuspOfCoordinate : BasePoint × K → Cusp13
  | (Sum.inr _, y) =>
      if y = 0 then .infinityPlus else .infinityMinus
  | (Sum.inl x, y) =>
      if x = 0 then
        if y = 0 then .zeroPlus else .zeroMinus
      else
        if y = 0 then .negOneMinus else .negOnePlus
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
abbrev SpecialSet : Type :=
  N13ReductionClassifier.SpecialSet
abbrev RationalCurvePoint : Type :=
  SexticMumford.CurvePoint (N13Mumford.model ℚ)
namespace CompatibleReduction
def affineX? :
    RationalCurvePoint → Option ℚ
  | .infinityPlus => none
  | .infinityMinus => none
  | .affine x _ _ => some x
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
abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)
theorem sexticY_onCurve (P : IntegralPoint) :
    sexticY P ^ 2 =
      (N13Mumford.model Q₂).f.eval (P.1.1 : Q₂) := by
  have hs :=
    N13GoodModelTwo.completed_square_identity
      (P.1.1 : Q₂) (P.1.2 : Q₂)
  have hzero :
      (P.1.2 : Q₂) ^ 2 +
          N13GoodModelTwo.h (P.1.1 : Q₂) * (P.1.2 : Q₂) -
        N13GoodModelTwo.rhs (P.1.1 : Q₂) = 0 :=
    sub_eq_zero.mpr (goodEquation_Q₂ P)
  rw [hzero] at hs
  change
    sexticY P ^ 2 =
      (N13Mumford.f Q₂).eval (P.1.1 : Q₂)
  calc
    sexticY P ^ 2 =
        N13GoodModelTwo.completedSextic (P.1.1 : Q₂) := by
      simpa [sexticY] using hs
    _ = (N13Mumford.f Q₂).eval (P.1.1 : Q₂) := by
      simp [N13GoodModelTwo.completedSextic, N13Mumford.f]
def curvePoint (P : IntegralPoint) :
    SexticMumford.CurvePoint Model :=
  .affine (P.1.1 : Q₂) (sexticY P) (sexticY_onCurve P)
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
/-- Formal Laurent series in the infinity parameter. -/
abbrev Laurent : Type u :=
  LaurentSeries R
/-- Formal power series on the infinity chart. -/
abbrev Power : Type u :=
  PowerSeries R
/-- An overlap function in the basis `1,v`. -/
abbrev Overlap : Type u :=
  Laurent (R := R) × Laurent (R := R)
/-- The two missing Laurent coefficients. -/
abbrev Obstruction : Type u :=
  Fin 2 → R
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
/-- Laurent coefficients in the infinity parameter. -/
abbrev Laurent : Type u :=
  LaurentPolynomial R
/-- An overlap function in the basis `1,v`. -/
abbrev Overlap : Type u :=
  Laurent (R := R) × Laurent (R := R)
/-- The two missing Laurent coefficients. -/
abbrev Obstruction : Type u :=
  Fin 2 → R
section Field
variable {F : Type u} [Field F]
end Field
end
end MazurProof.N13CechLaurentCore
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialCechObstruction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCechObstruction =====
section
/-!
# The special-fibre Čech obstruction at the N13 base divisor

Put `t = 1/x` and `v = y/x³` on the infinity chart.  For the structure
sheaf, the two classes missing from the affine and infinity chart images
are represented by

`v t⁻², v t⁻¹`.

The two simple principal parts at `(0,0)` and `(1,0)` map to `(1,0)` and
`(1,1)` in this obstruction basis.  The resulting triangular matrix has
determinant one.  This is the explicit special-fibre Čech form of the
nonspeciality of the divisor `(0,0)+(1,0)`.

The polynomial identities below are the cleared-denominator transition
calculation.  They use the actual infinity-chart coefficient
`1+t²+t³`; no point enumeration or certificate table is involved.
-/
namespace MazurProof.N13SpecialCechObstruction
noncomputable section
/-- Coefficients of the two missing Čech classes
`v t⁻², v t⁻¹`. -/
abbrev Obstruction : Type :=
  Fin 2 → K
/-! ## The two-chart Laurent obstruction -/
open LaurentPolynomial
open scoped LaurentPolynomial
/-- Laurent coefficients in the infinity parameter `t`. -/
abbrev Laurent : Type :=
  LaurentPolynomial K
end
end MazurProof.N13SpecialCechObstruction
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
abbrev Power : Type :=
  N13CechLaurentSeriesCore.Power (R := R₂)
abbrev Laurent : Type :=
  N13CechLaurentSeriesCore.Laurent (R := R₂)
/-- The Laurent monomial `tⁿ`. -/
def tPow (n : ℤ) : Laurent :=
  HahnSeries.single n 1
@[simp] theorem tPow_zero :
    tPow 0 = 1 := rfl
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
abbrev Laurent₂ : Type :=
  N13CechLaurentSeriesCore.Laurent (R := R₂)
abbrev LaurentBar : Type :=
  N13CechLaurentSeriesCore.Laurent (R := K)
abbrev Overlap₂ : Type :=
  N13CechLaurentSeriesCore.Overlap (R := R₂)
abbrev OverlapBar : Type :=
  N13CechLaurentSeriesCore.Overlap (R := K)
/-- The identity formal function. -/
def oneOverlap
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Overlap (R := R) :=
  (1, 0)
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
abbrev Laurent : Type :=
  N13FormalLineBundleCech.Laurent₂
abbrev IntegralAffineRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)
/-! ## Restriction of the actual affine coordinate ring -/
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
abbrev Power : Type :=
  PowerSeries R₂
abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent
/-- The coefficient of `v` in the formal infinity equation. -/
def hPower : Power :=
  1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3
/-- The right-hand side of the formal infinity equation. -/
def rhsPower : Power :=
  PowerSeries.X + PowerSeries.X ^ 2
/-! ## Normal form on the complete chart -/
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
abbrev Power : Type :=
  N13FormalInfinityChart.Power
/-- Send an ordinary polynomial in `t` to the corresponding power series. -/
def baseToPower : Base →+* Power :=
  Polynomial.eval₂RingHom
    (algebraMap R₂ Power) PowerSeries.X
@[simp] theorem baseToPower_hBase :
    baseToPower hBase =
      N13FormalInfinityChart.hPower := by
  simp [baseToPower, hBase, N13FormalInfinityChart.hPower]
@[simp] theorem baseToPower_rhsBase :
    baseToPower rhsBase =
      N13FormalInfinityChart.rhsPower := by
  simp [baseToPower, rhsBase, N13FormalInfinityChart.rhsPower]
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
abbrev AffineCurve : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)
def xClass : AffineCurve :=
  N13GeneralizedMumfordIntegral.xClass (R := R₂) X
def yClass : AffineCurve :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)
abbrev AffineOverlap : Type :=
  Localization.Away xClass
/-! ## The reverse chart map -/
def xAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap xClass
def tAffineOverlap : AffineOverlap :=
  IsLocalization.Away.invSelf xClass
def yAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap yClass
def coefficientToAffineOverlap : R₂ →+* AffineOverlap :=
  (algebraMap AffineCurve AffineOverlap).comp
    ((AdjoinRoot.of
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))).comp
        (Polynomial.C : R₂ →+* R₂[X]))
def infinityVImage : AffineOverlap :=
  tAffineOverlap ^ 3 * yAffineOverlap
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
abbrev Affine :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev AffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap
open AlgebraicGeometry
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
abbrev AffineCurve :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev AffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap
theorem affine_xClass_ne_zero :
    N13OrdinaryCurveOverlap.xClass ≠ 0 := by
  intro h
  have h0 := congrArg
    (N13GeneralizedMumfordIntegral.coeff0
      (R := N13OrdinaryCurveOverlap.R₂)) h
  simp [N13OrdinaryCurveOverlap.xClass] at h0
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
/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/
abbrev Model : SexticMumford.Model N13ProperCurveReduction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M
    (K := N13ProperCurveReduction.Q₂)
end
end MazurProof.N13IntegralInfinityPointSpread
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
theorem reflect_X_pow
    (N n : ℕ)
    (h : n ≤ N) :
    ((X : R₂[X]) ^ n).reflect N = X ^ (N - n) := by
  simpa [revAt_le h] using
    (reflect_monomial N n (R := R₂))
theorem reflect_hBase :
    N13IntegralInfinityChart.hBase.reflect 3 =
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) := by
  simp [N13IntegralInfinityChart.hBase,
    N13GeneralizedMumfordIntegral.hPoly, reflect_add]
theorem reflect_rhsBase :
    N13IntegralInfinityChart.rhsBase.reflect 6 =
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) := by
  have hX :
      (X : R₂[X]).reflect 6 = X ^ 5 := by
    simpa using reflect_X_pow 6 1 (by norm_num)
  have hX2 :
      ((X : R₂[X]) ^ 2).reflect 6 = X ^ 4 := by
    simpa using reflect_X_pow 6 2 (by norm_num)
  rw [N13IntegralInfinityChart.rhsBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    reflect_add, hX, hX2]
abbrev GenericModel : SexticMumford.Model
    N13TwoAdicCoordinateBaseChange.Q₂ :=
  N13GoodSexticCoordinateEquiv.M
    (K := N13TwoAdicCoordinateBaseChange.Q₂)
end
end MazurProof.N13IntegralInfinityGraphTwoChart
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
/-- The integral two-adic coefficient ring of the good N13 model. -/
abbrev R₂ : Type :=
  N13FiniteContractIdealInvertible.R₂
/-- The two-adic coefficient field of the generic N13 model. -/
abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂
/-- The good sextic model used by the canonical Mumford contraction. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13FiniteContractIdealInvertible.Model
/-- The canonical function field used for affine fractional ideals. -/
abbrev AffineFunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13IntegralInfinityPointSpread.Model
theorem pointY_onCurve
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    pointY x y ^ 2 = (N13Mumford.model Q₂).f.eval x := by
  have hs :=
    N13GoodModelTwo.completed_square_identity x y
  have hzero :
      y ^ 2 + N13GoodModelTwo.h x * y -
        N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hxy
  rw [hzero] at hs
  change
    pointY x y ^ 2 =
      (N13Mumford.f Q₂).eval x
  calc
    pointY x y ^ 2 =
        N13GoodModelTwo.completedSextic x := by
      simpa [pointY] using hs
    _ = (N13Mumford.f Q₂).eval x := by
      simp [N13GoodModelTwo.completedSextic, N13Mumford.f]
def curvePoint
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.CurvePoint Model :=
  .affine x (pointY x y) (pointY_onCurve x y hxy)
end
end MazurProof.N13EscapingDegreeOneSpread
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
abbrev OrdinaryAffine :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev OrdinaryAffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap
end
end MazurProof.N13OverlapReductionCompatibility
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
/-- The good sextic N13 model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂
/-- The set-valued special Picard model obtained from the Abel fibres. -/
abbrev SpecialPic : Type :=
  N13AbelFiberTwoModel.PicTwoSetModel
namespace Data
end Data
end
end MazurProof.N13TwoChartPicardRealization
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
abbrev A := N13OrdinaryCurveOverlap.AffineCurve
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
abbrev Model : SexticMumford.Model K := N13Mumford.model K
/-- If the affine degree is d, the raw order is nInf - 1. Relative to
2 infinity-plus, the two effective infinity multiplicities are nInf + 1
and 1 - d - nInf. These inequalities make both nonnegative. -/
def EffectiveChamber (E : N13Mumford.SemiMumford K) : Prop :=
  E.u.natDegree ≤ 2 ∧ -1 ≤ E.nInf ∧
    (E.u.natDegree : ℤ) + E.nInf ≤ 1
/-- Coefficients for an actual effective infinity completion of the repaired
affine graph; no natural-number truncation changes their integer values. -/
def positiveMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (E.nInf + 1)
def negativeMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (1 - (E.u.natDegree : ℤ) - E.nInf)
end
end MazurProof.N13EffectiveInfinityRepair
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
/-- The generic sextic model. -/
abbrev Model :=
  N13CanonicalContractionQuotient.Model
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
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
abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev AffineFunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField
/-- Weighted reflection of the redundant monic reciprocal equation. -/
def affineReciprocal (u : R₂[X]) : AffineCurve :=
  N13GeneralizedMumfordIntegral.xClassHom (u.reflect 2)
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13EscapingDegreeOneSpread.Model
end
end MazurProof.N13AllPointAffineSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13ReciprocalQuadraticReflection =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ReciprocalQuadraticReflection =====
section
/-!
# Reflection of the reciprocal N13 quadratic

For a monic quadratic

`u(X) = X² + u₁X + u₀`

with `u₀ ≠ 0`, its monic reciprocal equation is

`m(T) = T² + (u₁/u₀)T + u₀⁻¹`.

Reflecting `m` at weight two gives exactly `u₀⁻¹ u`.  Consequently an
integral reciprocal equation produces an integral affine weighted closure
whose generic horizontal generator differs from the original Mumford
generator by a nonzero scalar.  This is the horizontal equality needed in
the reciprocal two-chart branch.
-/
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13ReciprocalQuadraticReflection.instFactPrimeOfNatNat_fLT
abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model
end
end MazurProof.N13ReciprocalQuadraticReflection
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model
abbrev RationalRing : Type :=
  N13CanonicalContractionQuotient.RationalRing
def genericIdeal
    (D : SexticMumford.Mumford Model) :
    Ideal RationalRing :=
  N13CanonicalContractionQuotient.graphIdeal D.toSemi
abbrev GenericQuotient
    (D : SexticMumford.Mumford Model) : Type :=
  RationalRing ⧸ genericIdeal D
def xbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  Ideal.Quotient.mk (genericIdeal D)
    (SexticMumford.xClass Model X)
def goodYbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  Ideal.Quotient.mk (genericIdeal D)
    (N13GoodSexticCoordinateEquiv.goodYInSextic (K := Q₂))
def coefficientToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    R₂ →+* GenericQuotient D :=
  (algebraMap Q₂ (GenericQuotient D)).comp
    N13TwoAdicCoordinateBaseChange.coeffMap
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model
abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve
abbrev GenericQuotient
    (D : SexticMumford.Mumford Model) : Type :=
  N13ReciprocalInfinityContraction.GenericQuotient D
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
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
abbrev CoordinateRing : Type u :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R)
end
end MazurProof.N13InfinityNormCarrier
end

end

-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite =====
section
/-!
# Finiteness on the affine chart of an irreducible N13 quadratic

If the horizontal quadratic has integral affine coefficients, its monic
equation belongs to the canonical contraction.  The rank-two polynomial
normal form then makes the contracted quotient finite.  Vertical
saturation already makes the same quotient flat.

Combined with the proper-chart theorem, this leaves only the reciprocal
integral chart as the non-affine alternative.
-/
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticFinite
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticFinite.instFactPrimeOfNatNat_fLT
abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model
end
end MazurProof.N13IrreducibleQuadraticFinite
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
abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model
end
end MazurProof.N13IrreducibleQuadraticSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpecialClass =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpecialClass =====
section
/-!
# Special classes of integral affine N13 point lines

An integral point on the good two-adic affine chart has a literal monic graph
ideal and, by finite-support closure, an honest proper two-chart line.
Coefficientwise reduction sends that affine ideal exactly to the linear graph
of the reduced point on the special curve.

The special Abel model has degree two, so a reduced affine point is normalized
by adjoining the fixed positive-infinity anchor once.  This normalization is
kept explicit: the affine ideal alone cannot see it because the positive
infinity point line is trivial on the affine chart.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- Integral affine points of the good N13 model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint
/-- The set-valued special Picard model used by the N13 endgame. -/
abbrev SpecialSet : Type :=
  N13RationalPointEndgame.SpecialSet
end
end MazurProof.N13IntegralAffinePointSpecialClass
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
/-- Integral affine points of the good two-adic model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpread =====
section
/-!
# Proper two-chart spreads for every quadratic N13 graph

Every two-adic affine point has a proper point line.  Integral points use the
finite-support closure of their monic affine graph, while nonintegral points
use the explicit infinity-chart line.  Tensoring two such point lines gives
proper spreads for split quadratic graphs, including the tangent
repeated-root case.

A monic quadratic is either split or irreducible.  Combining the point-line
tensor construction with the irreducible quadratic closure therefore gives
an honest proper two-chart line for every balanced quadratic Mumford graph.
-/
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13QuadraticTwoChartSpread.instFactPrimeOfNatNat_fLT
/-- The two-adic coefficient field of the generic N13 model. -/
abbrev Q₂ : Type :=
  N13AllPointAffineSpread.Q₂
/-- The good sextic N13 model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13AllPointAffineSpread.Model
end
end MazurProof.N13QuadraticTwoChartSpread
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralPointPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralPointPicardRealization =====
section
/-!
# Picard realization of integral degree-one N13 points

An integral affine point has a proper two-chart closure whose two special
ideals are the canonical ideals of its coefficientwise reduction.  Adjoining
the positive-infinity line once places that point in the degree-two special
Abel model without changing its generic affine ideal.

The original point is affine, so its Mumford representative has `nInf = 0`.
Consequently the oriented generic exponent is `-1`, exactly as in the
escaping degree-one branch.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralPointPicardRealization.instFactPrimeOfNatNat_fLT
/-- Integral affine points of the good two-adic N13 model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint
end
end MazurProof.N13IntegralPointPicardRealization
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
abbrev K : Type := N13IntegralFractionalHull.FunctionField
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction =====
section
/-!
# Special restriction of split quadratic N13 lines

The valuation-independent point line chooses the ordinary affine closure for
an integral horizontal coordinate and the infinity-chart closure for an
escaping coordinate.  Both branches have already been identified with the
canonical chart pair of their reduced special point.

This file packages that case split once.  Tensoring the resulting point-line
equalities then identifies every split quadratic line, including a repeated
root, with the canonical chart pair of its literal degree-two special
divisor.  These are equalities of both chart ideals; no Picard orientation is
inferred from them.
-/
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SplitQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The two-adic coefficient field of the good N13 model. -/
abbrev Q₂ : Type :=
  N13QuadraticTwoChartSpread.Q₂
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end

end

-- ===== FLT.Assumptions.MazurProof.N13SplitQuadraticPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SplitQuadraticPicardRealization =====
section
/-!
# Picard realization of split quadratic N13 graphs

The split and repeated-root constructors already produce a proper line with
the exact generic quadratic Mumford ideal and the exact two chart ideals of a
literal special divisor.  Marking that line by the representative's oriented
exponent `nInf - 1` therefore fills every field of the two-fibre Picard
realization.

This file performs only that semantic packaging.  In particular, it does not
alter the vanishing-ideal convention or infer a divisor sign from support.
-/
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13SplitQuadraticPicardRealization.instFactPrimeOfNatNat_fLT
/-- The good sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model
end
end MazurProof.N13SplitQuadraticPicardRealization
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuadraticPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticPicardRealization =====
section
/-!
# Picard realization of every quadratic N13 graph

The finite irreducible branch now has a literal special divisor, while the
reciprocal branch is complete for both horizontal and vertical rank-two
recovery.  Combining those two cases gives complete two-fibre Picard data
for every irreducible quadratic Mumford representative.

A nonirreducible monic quadratic factors into two linear terms.  Distinct
roots use the existing secant realization and a repeated root uses the
existing tangent realization.  Thus every balanced quadratic representative
has exact generic raw data, its standard oriented generic Picard class, and
the canonical two-chart ideals of a literal effective special divisor.
-/
open Polynomial
namespace MazurProof.N13QuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13QuadraticPicardRealization.instFactPrimeOfNatNat_fLT
/-- The good sextic N13 model. -/
abbrev Model :=
  N13TwoChartPicardRealization.Model
end
end MazurProof.N13QuadraticPicardRealization
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityPointPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityPointPicardRealization =====
section
/-!
# Picard realization of the two N13 infinity points

The positive infinity point is the Abel--Jacobi base point.  Two copies of
its proper point line therefore realize the identity class and reduce to the
doubled special anchor.  Tensoring the negative infinity line with the
positive anchor realizes the difference of the two infinity points and
retains both special sheets.

These are the two projective cases missing from the existing affine-point
realizations.  Both constructions use literal chart ideals and the standard
oriented Mumford representatives.
-/
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityPointPicardRealization.instFactPrimeOfNatNat_fLT
/-- The two-adic N13 sextic model. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model
end
end MazurProof.N13InfinityPointPicardRealization
end

end

-- ===== FLT.Assumptions.MazurProof.N13EffectiveGraphData =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13EffectiveGraphData =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Actual chart constructions for an effective degree-two semirepresentative.
The degree-one negative marking uses the negative infinity point line; the
constant negative marking uses two copies of that line. A repaired quadratic
uses the residual graph, rather than the original balanced graph.

The raw/class conclusions below are proved from the displayed constructors.
Their generic formal-branch marking and integral-comparison theorems are
separate obligations, not consequences asserted from affine saturation.
-/
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
attribute [local instance] MazurProof.N13EffectiveGraphData.instFactPrimeOfNatNat_fLT
/-- The same affine graph in the existing balanced graph-constructor API.
Its temporary orientation is not used as the effective divisor's marking. -/
def balancedGraph (E : N13Mumford.SemiMumford Q₂) (hd : E.u.natDegree ≤ 2) :
    N13Mumford.Mumford Q₂ where
  u := E.u
  v := E.v
  nInf := 0
  u_monic := E.u_monic
  deg_u := hd
  v_reduced := E.v_reduced
  curve_dvd := E.curve_dvd
  infinity_bound := by simpa using hd
end
end MazurProof.N13EffectiveGraphData
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityBranches =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityBranches =====
section
/-!
# The two Hensel branches at infinity for N13

The formal-infinity equation

`v² + (1 + X² + X³)v - (X + X²) = 0`

reduces modulo `X` to `v(v + 1)`.  Both roots of the special fibre are
simple.  This file lifts the root `0` by X-adic Hensel, obtains the conjugate
root from the quadratic equation, and proves that their difference is a
unit.  These are the structural inputs for splitting the complete
infinity-chart algebra by two-point evaluation.
-/
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13FormalInfinityBranches.instFactPrimeOfNatNat_fLT
abbrev Power : Type :=
  N13FormalInfinityChart.Power
end
end MazurProof.N13FormalInfinityBranches
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
abbrev Power : Type :=
  N13FormalInfinityChart.Power
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
abbrev Power : Type :=
  N13FormalInfinityChart.Power
abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent
open N13FormalInfinityBranches
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
abbrev CoordinateRing : Type u :=
  N13Mumford.CoordinateRing K
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
/-- The rational branch of the good coordinate `v=t³y` reducing to zero. -/
def rationalBranchZero : RationalLaurent :=
  algebraMap Q₂ RationalLaurent (1 / 2) *
    (N13Infinity.wSeries Q₂ - hInfinityQ)
end
end MazurProof.N13TwoAdicInfinityCompatibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13InverseInfinityData =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InverseInfinityData =====
section
/-!
# Special divisor of the nInf = 2 degree-zero witness

The split quadratic u = X(X+1), v = 1 has roots x = 0, -1 with good ordinates 0 and 1; its literal reduced
special divisor is s(zeroPlus, negOnePlus) = C + A (cf. N13CuspCARelation: AJ13 C + AJ13 A = -AJ13 T).
This corrects the D + B divisor guessed in ChatGPT answer Q8689.
-/
namespace MazurProof.N13InverseInfinityData
noncomputable section
attribute [local instance] MazurProof.N13InverseInfinityData.instFactPrimeOfNatNat_fLT
open N13SplitQuadraticSpecialRestriction
abbrev Q₂ : Type := N13SplitQuadraticSpecialRestriction.Q₂
end
end MazurProof.N13InverseInfinityData
end

end

-- ===== FLT.Assumptions.MazurProof.N13ProjectiveModel =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ProjectiveModel =====
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace MazurProof.N13Arithmetic
/-- Rational affine points on the sextic model. -/
abbrev AffinePoint13 :=
  {xy : ℚ × ℚ // N13CurveModel.C13SexticEq xy.1 xy.2}
end MazurProof.N13Arithmetic
end

end

-- ===== FLT.Assumptions.MazurProof.N13Jacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Jacobian =====
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-!
Rational points on the N13 sextic curve and the Abel-Jacobi map.
-/
/-!
Point types and cusp definitions are in N13ProjectiveModel.lean.
This module provides the Abel-Jacobi map and divisor arithmetic.
-/
/-!
For the smooth two-infinity sextic, a projective Cartier divisor is encoded
by its invertible fractional ideal on the affine chart together with its two
orders at the omitted infinity points.  This carrier uses arbitrary
invertible fractional ideals, not merely the subgroup generated by rational
points.
-/
abbrev RatFun13 := N13Mumford.FunctionField ℚ
/-! The two affine points above `X=0`. -/
/-!
On the affine chart the ideals of C and D are respectively
`(X,Y-1)` and `(X,Y+1)`; their product is the principal ideal `(X)`.
-/
/-! Exact pole orders at the two infinity branches. -/
end MazurProof.N13Arithmetic
end
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
abbrev M13 : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ
/-! ## Exact order at the positive infinity branch -/
def z13 : N13Mumford.SemiMumford ℚ :=
  (SexticMumford.zero M13).toSemi
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
abbrev P := N13FormalInfinityChart.Power
theorem span_pair_unit_right {R : Type*} [CommRing R] (x y : R) (hy : IsUnit y) :
    Ideal.span ({x, y} : Set R) = ⊤ := by
  rcases hy with ⟨u, rfl⟩
  rw [Ideal.eq_top_iff_one]
  have hu : (u : R) ∈ Ideal.span ({x, (u : R)} : Set R) :=
    Ideal.subset_span (by simp)
  have hh := Ideal.mul_mem_left (Ideal.span ({x, (u : R)} : Set R)) (↑(u⁻¹) : R) hu
  simpa using hh
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
abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent
end
end MazurProof.N13OrdinaryCompletionCompatibility
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
abbrev A := N13OrdinaryCurveOverlap.AffineCurve
abbrev AO := N13OrdinaryCurveOverlap.AffineOverlap
end
end MazurProof.N13OverlapBranchCompatibility
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
abbrev Affine := N13IntegralFractionalHull.IntegralRing
abbrev CommonField := N13IntegralFractionalHull.FunctionField
end N13Charts
end
end MazurProof.N13PrimitiveVerticalPresentation
end

end

-- ===== FLT.Assumptions.MazurProof.N13PrincipalBranchBalance =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13PrincipalBranchBalance =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The affine principal relation between TWO products of Mumford graph ideals
forces the missing sum of the positive and negative infinity orders. The
proof multiplies by the hyperelliptic conjugate, extracts an affine unit,
and proves that the conjugation-fixed unit is a scalar. It uses no global
specialization compatibility or desired additive code equation.
-/
namespace MazurProof.N13PrincipalBranchBalance
noncomputable section
open Polynomial SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
abbrev M := N13Mumford.model K
abbrev R := N13Mumford.CoordinateRing K
abbrev F := N13Mumford.FunctionField K
end
end MazurProof.N13PrincipalBranchBalance
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
abbrev R := N13IntegralFractionalHull.RationalRing
abbrev F := N13IntegralFractionalHull.FunctionField
open N13InfinityChartMarking hiding QP
open N13EffectiveInfinityRepair
end
end MazurProof.N13PrincipalBranchIdeals
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
abbrev P := N13FormalInfinityChart.Power
abbrev beta := N13IntegralInfinityChart.baseToPower
theorem beta_eq_coe (p : R₂[X]) : beta p = (p : P) := by
  simpa [beta, N13IntegralInfinityChart.baseToPower] using p.eval₂_C_X_eq_coe
end
end MazurProof.N13InfinityBranchJets
end

end

-- ===== FLT.Assumptions.MazurProof.N13MarkedQuadraticExistence =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MarkedQuadraticExistence =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Retain the infinity-marking certificate on the same quadratic witness.
The case constructions are the pinned finite, split and reciprocal source
proofs, augmented by the actual branch-ideal proofs; no existing file changes.
This supplies no integral principal-comparison or global chooser theorem.
-/
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13MarkedQuadraticExistence.instFactPrimeOfNatNat_fLT
abbrev Model := N13TwoChartPicardRealization.Model
end
end MazurProof.N13MarkedQuadraticExistence
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
abbrev SpecialSet : Type :=
  N13RationalPointEndgame.SpecialSet
abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint
namespace Data
variable {Line : Type u}
end Data
end
end MazurProof.N13SpreadRationalPointReduction
end

end

-- ===== FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization =====
section
/-!
# Two-fibre Picard realization of every rational N13 curve point

The projective N13 curve has two infinity points and an affine chart.  The
two infinity points are realized by their integral chart lines.  An affine
rational point is first transported to the good two-adic model and then
realized by the integral or escaping point line according to the valuation
of its first coordinate.

The package below records both identifications needed for specialization:
its generic class is the rational Abel--Jacobi class after base change to
`ℚ₂`, and its special class is the anchored Abel class of the point's proper
reduction.  Thus this file proves pointwise existence of honest two-fibre
data; it does not postulate a specialization map on arbitrary Picard classes.
-/
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13RationalCurvePointPicardRealization.instFactPrimeOfNatNat_fLT
/-- Rational points of the projective N13 sextic. -/
abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint
/-!
## The two points at infinity

The chosen positive point at infinity is the Abel--Jacobi base point, whereas
the negative point contributes the distinguished infinity Mumford class.  The
existing integral chart lines realize these two classes and specialize to the
anchor and cusp, respectively.
-/
/-!
## Affine rational points

The sextic coordinates over `ℚ` are first sent to the good two-adic model by
the completion-of-the-square coordinate change.  The valuation of `x` then
selects one of the two proper integral chart constructions.  In either case we
compare the resulting degree-one Mumford representative componentwise with
the base change of the original rational point representative.
-/
/-!
## Literal generic ideals

The preceding constructions identify generic Picard classes.  Global spread
existence needs the stronger statement that the affine ideal itself is the
Mumford ideal obtained by coefficient extension.  The following two lemmas
expose that stronger invariant for the integral and escaping branches.
-/
/-!
## Relation-first spread lines

A spread line remembers the rational Picard class it represents in addition
to its two-fibre geometric realization.  This makes the eventual reduction
classifier a statement about equality of concrete specializations, while the
pointwise constructions above supply Abel--Jacobi compatibility directly.
-/
end
end MazurProof.N13RationalCurvePointPicardRealization
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
abbrev P := PowerSeries K
def powerReduce : N13FormalInfinityChart.Power →+* P := PowerSeries.map PadicInt.toZMod
def h : P := 1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3
def rhs : P := PowerSeries.X + PowerSeries.X ^ 2
theorem reduce_h : powerReduce N13FormalInfinityChart.hPower = h := by
  simp [powerReduce, N13FormalInfinityChart.hPower, h]
theorem reduce_rhs : powerReduce N13FormalInfinityChart.rhsPower = rhs := by
  simp [powerReduce, N13FormalInfinityChart.rhsPower, rhs]
def beta : K[X] →+* P := Polynomial.eval₂RingHom PowerSeries.C PowerSeries.X
theorem beta_eq_coe (p : K[X]) : beta p = (p : P) := by
  simpa [beta] using p.eval₂_C_X_eq_coe
end
end MazurProof.N13SpecialInfinityBranchJets
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialComparisonFactorPair =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialComparisonFactorPair =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Every degree-four special comparison supplies an actual affine factor pair
whose product is a monic polynomial of degree at most eight. The factors
represent the same numerator/denominator as the input comparison, after
clearing only the explicit rational-point fibre polynomials. This removes
arbitrary affine denominators without assuming a principal-code law.
-/
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
abbrev R := N13GoodCoordinateRingTwo.CoordinateRing
end
end MazurProof.N13SpecialComparisonFactorPair
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
abbrev R := N13GoodCoordinateRingTwo.CoordinateRing
def linear (p q : K[X]) : R := xClass p + xClass q * yClass
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
abbrev P := PowerSeries K
def includeSeries : P →+* L := HahnSeries.ofPowerSeries ℤ K
end
end MazurProof.N13SpecialLaurentBranches
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
abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent
abbrev LaurentBar : Type :=
  N13FormalLineBundleCech.LaurentBar
/-! ## Reduction of polynomial restrictions -/
/-! ## The near-base transition -/
abbrev NearBaseMumford : Type :=
  N13TwoAdicAbelChartRecover.NearBaseMumford
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
abbrev Laurent : Type :=
  N13MumfordFormalTransition.Laurent
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair
end
end MazurProof.N13MumfordFormalTransitionJet
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
/-- Evaluate the left variables at `z` and the right variables at `w`. -/
def evalPair
    (coord : K → Fin 2 → R₂) (z w : K) :
    BiPoly →+* R₂ :=
  eval₂Hom (RingHom.id R₂)
    (Sum.elim (coord z) (coord w))
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
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
end DoublingData
namespace Data
end Data
namespace RationalKernelDoublingData
end RationalKernelDoublingData
namespace RationalKernelData
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
/-- Ordered pairs in the two distinguished two-adic residue disks. -/
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair
/-- The balanced N13 Mumford model over the two-adic field. -/
abbrev Model₂ : SexticMumford.Model ℚ_[2] :=
  N13ConcreteGraphRecovery.Model
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
open Polynomial N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13KernelGraphContraction.instFactPrimeOfNatNat_fLT
abbrev R := N13IntegralModelContraction.RationalRing
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
open Polynomial N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13KernelBasePic.instFactPrimeOfNatNat_fLT
abbrev basePair : N13TwoAdicAbelChartPic.DiskPair :=
  N13TwoAdicAbelChartData.basePair
end
end MazurProof.N13KernelBasePic
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet =====
section
/-!
# Denominator-free centered doubling jets for N13

Let `u_B = X² + X` be the fixed Abel-chart base polynomial and let `u_P`
be the monic quadratic of a disk pair.  The square of the centered transition
`u_P / u_B` has a canonical first-order monic normalization

`u_square = 2 * u_P - u_B`.

Cross-multiplication gives the exact error

`u_P² - u_B * u_square = (u_P - u_B)²`.

Thus its constant and linear deviations are the doubled disk coordinates
modulo the square of the moving coordinate ideal.  These identities are the
denominator-free polynomial core of the missing first-jet doubling theorem;
identifying the chosen representative of the doubled Picard class with this
normalization remains a separate step.
-/
open Polynomial
namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
attribute [local instance] MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT
/-- The two-adic coefficient domain of the integral N13 model. -/
abbrev R₂ : Type := ℤ_[2]
/-- A pair of Hensel-selected points in the two distinguished Abel disks. -/
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair
/-! ## A curve-compatible linearized double -/
/-! ## Quadratic Hensel expansions of the selected ordinates -/
/-! ## Reduction from cross-multiplied normalization to coordinate doubling -/
end
end MazurProof.N13MumfordCenteredDoublingJet
end

end

-- ===== FLT.Assumptions.MazurProof.N13CenteredPrincipalNumerator =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CenteredPrincipalNumerator =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Extract the actual principal multiplier for the selected centered double,
with zero order on both infinity sheets. Clearing u(P)^2 gives a nonzero
regular numerator lying in BOTH the base/double ideal and the squared
conjugate ideal. The normalized Hermite numerator is not identified here.
-/
namespace MazurProof.N13CenteredPrincipalNumerator
noncomputable section
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
abbrev M := N13Mumford.model K
abbrev R := N13Mumford.CoordinateRing K
abbrev F := N13Mumford.FunctionField K
abbrev DiskPair := N13TwoAdicAbelChartData.DiskPair
abbrev B := N13TwoAdicAbelChartData.basePair
end
end MazurProof.N13CenteredPrincipalNumerator
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
def goodP (n : R) : K[X] := coeff0 M n + coeffY M n * N13GeneralizedMumfordIntegral.hPoly
def goodQ (n : R) : K[X] := 2 * coeffY M n
end
end MazurProof.N13GoodCenteredNumerator
end

end

-- ===== FLT.Assumptions.MazurProof.N13CenteredHermiteFirstOrder =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CenteredHermiteFirstOrder =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

A concrete Hermite numerator calculation. If uBase*A+b*y vanishes twice
on the conjugates of an actual disk pair, where A is monic quadratic and
b is linear, its coefficients are forced to the centered-square values
modulo the moving coordinate ideal squared. Constructing such a normalized
numerator for the actual principal comparison remains a separate goal.
-/
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
abbrev DiskPair := N13TwoAdicAbelChartData.DiskPair
def x (P : DiskPair) : Fin 2 → R₂ := ![P.x₀, P.x₁]
def oppositeY (P : DiskPair) : Fin 2 → R₂ :=
  ![-N13GoodModelTwo.h P.x₀ - P.y₀,
    -N13GoodModelTwo.h P.x₁ - P.y₁]
def I (P : DiskPair) : Ideal R₂ :=
  N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P
end
end MazurProof.N13CenteredHermiteFirstOrder
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralHermiteNumerator =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralHermiteNumerator =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Construct the monic Hermite numerator directly over Z2. Its four linear
equations have an invertible residue matrix for every actual disk pair;
the tangent slopes need only be integral. This discharges existence of the
four equations used in CenteredHermiteFirstOrder. Identification with the
principal comparison and its residual divisor is a separate obligation.
-/
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13IntegralHermiteNumerator.instFactPrimeOfNatNat_fLT
def rightSide (P : DiskPair) : Fin 4 → R₂ :=
  ![-(P.x₀ ^ 2 + P.x₀) * P.x₀ ^ 2,
    -(P.x₁ ^ 2 + P.x₁) * P.x₁ ^ 2,
    -(2 * P.x₀ + 1) * P.x₀ ^ 2 - (P.x₀ ^ 2 + P.x₀) * (2 * P.x₀),
    -(2 * P.x₁ + 1) * P.x₁ ^ 2 - (P.x₁ ^ 2 + P.x₁) * (2 * P.x₁)]
end
end MazurProof.N13IntegralHermiteNumerator
end

end

-- ===== FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Use the actual implicit tangent slopes on the conjugate sheets. The
constructed numerator's norm has uBase as an explicit factor. Its residual
is divisible by u(P)^2 even when P shares an x-coordinate with the base
divisor: cancellation is by the unit conjugate ordinate, never by uBase(x).
-/
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13HermiteResidualDivisibility.instFactPrimeOfNatNat_fLT
theorem vertical_derivative_unit (P : DiskPair) (j : Fin 2) :
    IsUnit (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) := by
  have h₀ : IsUnit (2 * P.y₀ + N13GoodModelTwo.h P.x₀) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.y₀_spec.2 using 1 <;> ring
  have h₁ : IsUnit (2 * P.y₁ + N13GoodModelTwo.h P.x₁) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk P.x₁_add_one_mem)
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.y₁_spec.2 using 1 <;> ring
  fin_cases j
  · convert h₀.neg using 1 <;> dsimp [x, oppositeY, N13GoodModelTwo.h] <;> ring
  · convert h₁.neg using 1 <;> dsimp [x, oppositeY, N13GoodModelTwo.h] <;> ring
def slope (P : DiskPair) (j : Fin 2) : R₂ :=
  (5 * x P j ^ 4 + 4 * x P j ^ 3 -
    (3 * x P j ^ 2 + 1) * oppositeY P j) *
      (↑((vertical_derivative_unit P j).unit⁻¹) : R₂)
end
end MazurProof.N13HermiteResidualDivisibility
end

end

-- ===== FLT.Assumptions.MazurProof.N13ActualHermiteEquations =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ActualHermiteEquations =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Transport the actual conjugate graph through completion of the square and
evaluate its squared ideal in the actual opposite-sheet dual-number jets.
This proves the four Hermite equations for the SAME principal numerator
already extracted from the selected centered double.
-/
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13ActualHermiteEquations.instFactPrimeOfNatNat_fLT
def V (P : DiskPair) : K[X] :=
  -N13GeneralizedMumfordIntegral.hPoly - N13TwoAdicMumfordTransport.mapPoly P.v
end
end MazurProof.N13ActualHermiteEquations
end

end


