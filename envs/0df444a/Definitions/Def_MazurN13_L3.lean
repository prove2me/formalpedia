-- Prove2me | Definitions.Def_MazurN13_L3
-- name    : MazurN13_L3
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-09T06:01:28.087242+00:00
-- url     : https://prove2.me/theorems/f80d59ea-9045-40a4-98aa-18f2af7ec613
-- title:
--   Mazur order 13 (Huang FLT port): definitions, layer 3
-- statement:
--   Layer 3 of 12 of the definitions used by a machine-checked Lean proof of the case $N=13$ of Mazur's torsion theorem (no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$). It collects the definitions, structures, instances and small structural lemmas of Xiang Huang's development whose dependencies are available at this layer; larger lemmas they rely on are separate platform theorems, imported here as already-proved results. Layer $k$ imports layer $k-1$.
--
--   Port notes: only API-drift fixes (transparency options, renamed lemmas); local notations expanded and `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_EvenSexticNormPair_forget_eq_one_iff_eq_one_or_eq_sign
import Theorems.Thm_MazurProof_N13BranchLeading_branch_min_order
import Theorems.Thm_MazurProof_N13BranchNorm_branch_product
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_formalCurvePoly_natDegree
import Theorems.Thm_MazurProof_N13GaussianFractionField_gaussianBasis_apply
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_g_mul_conj
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_h_coeff_zero
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_pi_prime
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_toSextic_ySubClass
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_affine_curve_eq
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointResidual_eval
import Theorems.Thm_MazurProof_N13IntegralModelContraction_goodRing_isLocalization
import Theorems.Thm_MazurProof_N13Mumford_f_monic
import Theorems.Thm_MazurProof_N13Mumford_principal_between_balanced_of_constant
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_minusYSub_plus_coeff_neg_three
import Theorems.Thm_MazurProof_N13MumfordKummerNorm_resultant_f_u_eq_normRoot_sq
import Theorems.Thm_MazurProof_N13MumfordKummerRelation_mumfordFakeClass_eq_of_principal_relation
import Theorems.Thm_MazurProof_N13SexticIrreducible_fInt_monic
import Theorems.Thm_MazurProof_N13SexticSquareclass_compressed_scaled_identity_in_algebra
import Theorems.Thm_MazurProof_N13SexticSquareclass_e2_mul_primeA_mul_primeQ
import Theorems.Thm_MazurProof_N13SexticSquareclass_zeta_mul_e1_mul_primeA
import Theorems.Thm_MazurProof_N13SpecialCuspReduction_cuspCoordinate_cuspOfCoordinate
import Theorems.Thm_MazurProof_N13SpecialCuspReduction_cuspOfCoordinate_cuspCoordinate
import Theorems.Thm_MazurProof_N13SpecialGraphDivisor_graphDivisor_eq_special_of_mumfordIdeal_eq
import Theorems.Thm_MazurProof_N13SpecialGraphDivisor_u_eq_base_and_dvd_v_of_graphDivisor_eq
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisorCharts_yClass_relation
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_injective
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_diskPair_u_dvd
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_diskPair_u_dvd_v_sub
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_u_natDegree
import Theorems.Thm_MazurProof_PowerBasisDiscriminant_norm_aeval_eq_resultant
import Theorems.Thm_MazurProof_RamifiedDlog_fst_ne_zero
import Theorems.Thm_MazurProof_SexticMumford_degreeStep_class
import Theorems.Thm_MazurProof_SexticMumford_ker_mumfordEval
import Theorems.Thm_MazurProof_SexticMumford_primitivePart_fractional_isUnit
import Theorems.Thm_MazurProof_SexticMumford_primitivePart_isPrimitive
import Theorems.Thm_MazurProof_SexticMumford_ySubClass_ne_zero
import Theorems.Thm_NumberField_Units_dirichletCoordinatesHom_injective
import Theorems.Thm_NumberField_Units_dirichletCoordinatesHom_surjective
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_toGood_comp_toSextic
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_toSextic_comp_toGood
import Theorems.Thm_MazurProof_N13SmallMumfordRigidity_principal_is_constant

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
/-- The coordinate-ring isomorphism induced by completion of the square. -/
def coordinateRingEquiv :
    GoodRing (K := K) ≃+* SexticRing (K := K) where
  toFun := toSextic (K := K)
  invFun := toGood (K := K)
  left_inv z := by
    have h :=
      DFunLike.congr_fun (toGood_comp_toSextic (K := K)) z
    simpa using h
  right_inv z := by
    have h :=
      DFunLike.congr_fun (toSextic_comp_toGood (K := K)) z
    simpa using h
  map_mul' := map_mul (toSextic (K := K))
  map_add' := map_add (toSextic (K := K))
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
/-- Completion of the square maps each generalized Mumford graph ideal
exactly onto the corresponding sextic Mumford graph ideal. -/
theorem map_mumfordIdeal (u v : K[X]) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u (completedGraph v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    SexticMumford.mumfordIdeal, Ideal.map_span, Set.image_pair,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    toSextic_ySubClass]
  exact span_pair_mul_right_unit _ _ _ invTwo_isUnit
/-- The exact transport theorem with the sextic graph polynomial reduced
modulo `u`, as required by the standard Mumford representation. -/
theorem map_mumfordIdeal_reduced (u v : K[X]) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u
        (reducedCompletedGraph u v) := by
  rw [map_mumfordIdeal]
  exact sextic_mumfordIdeal_eq_of_dvd_sub _ _ _
    (dvd_sub_mod (completedGraph v) u)
/-- The reduced standard semirepresentative has exactly the transported
generalized graph ideal. -/
theorem map_mumfordIdeal_toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K))
        (toSexticSemi D nInf).u
        (toSexticSemi D nInf).v := by
  simpa only [toSexticSemi_u, toSexticSemi_v] using
    map_mumfordIdeal_reduced D.u D.v
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
/-- Completion of the square transports every integral generalized graph
ideal, independently of a vertical Bézout witness. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChangeSemi D).u (baseChangeSemi D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemiOfSemi D nInf).u
        (sexticSemiOfSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChangeSemi D) nInf
/-- The two-adic sextic graph ideal is exactly the image of the generalized
graph ideal under completion of the square. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChange D).u (baseChange D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemi D nInf).u
        (sexticSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChange D) nInf
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
/-- Coefficient extension maps an integral graph ideal onto the
coefficient-extended graph ideal. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := Q₂) (mapPoly u) (mapPoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    Ideal.map_span, Set.image_pair, extend_xClass,
    extend_ySubClass]
/-- An integral smooth graph ideal becomes exactly the standard reduced
sextic Mumford graph attached by `sexticSemi`. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi
      D nInf
/-- The same coordinate transport theorem for arbitrary integral
semigraphs. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemiOfSemi
      D nInf
end
end MazurProof.N13TwoAdicCoordinateBaseChange
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
/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford M) :
    CoordinateRing M ⧸ mumfordIdeal M D.u D.v ≃+*
      MumfordResidue M D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval M D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective M D))
@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford M) (z : CoordinateRing M) :
    mumfordQuotientEquiv M D
        (Ideal.Quotient.mk (mumfordIdeal M D.u D.v) z) =
      mumfordEval M D z := by
  simp [mumfordQuotientEquiv]
/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford M) :
    (CoordinateRing M ⧸ mumfordIdeal M D.u D.v) ≃ₐ[K]
      MumfordResidue M D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv M D)
    (by
      intro r
      change
        mumfordQuotientEquiv M D
            (Ideal.Quotient.mk
              (mumfordIdeal M D.u D.v) (xClass M (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])
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
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
local instance goodRingLocalization :
    IsLocalization verticalScalars GoodRing :=
  goodRing_isLocalization
attribute [local instance] MazurProof.N13IntegralModelContraction.integralRationalAlgebra
/-- Completion of the square is an equivalence over the integral model. -/
def goodToSextic :
    GoodRing ≃ₐ[IntegralRing] RationalRing where
  __ :=
    N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := Q₂)
  commutes' _ := rfl
/-- The standard sextic generic-fibre coordinate ring is the same vertical
localization. -/
theorem rationalRing_isLocalization :
    IsLocalization verticalScalars RationalRing :=
  IsLocalization.isLocalization_of_algEquiv
    verticalScalars goodToSextic
local instance rationalRingLocalization :
    IsLocalization verticalScalars RationalRing :=
  rationalRing_isLocalization
/-- Extending the canonical contraction recovers the generic-fibre ideal
exactly. -/
theorem map_contractIdeal
    (J : Ideal RationalRing) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (contractIdeal J) =
      J := by
  exact IsLocalization.map_under
    verticalScalars RationalRing J
end
end MazurProof.N13IntegralModelContraction
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis =====
section
/-!
# The literal basis of a quadratic sextic Mumford quotient

For a monic degree-two Mumford polynomial `u`, graph evaluation identifies
the affine quotient by `(u,Y-v)` with `K[X]/(u)`.  Transporting the canonical
power basis gives the literal quotient basis `{1,x}`.
-/
open Module
open Polynomial
namespace MazurProof.SexticMumfordQuotientBasis
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)
/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K
      (SexticMumford.CoordinateRing M ⧸
        SexticMumford.mumfordIdeal M D.u D.v) :=
  (residueBasis M D hdeg).map
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm.toLinearEquiv
end
end MazurProof.SexticMumfordQuotientBasis
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
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.integralRationalAlgebra
/-- The quotient map from a canonical contraction to its generic ideal. -/
def genericQuotientMap (J : Ideal RationalRing) :
    IntegralRing ⧸ N13IntegralModelContraction.contractIdeal J →+*
      RationalRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13IntegralModelContraction.contractIdeal J)
    J
    (N13IntegralModelContraction.map_contractIdeal J)
@[simp] theorem genericQuotientMap_mk
    (J : Ideal RationalRing) (a : IntegralRing) :
    genericQuotientMap J
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal J) a) =
      Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) :=
  rfl
end
end MazurProof.N13CanonicalContractionQuotient
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
/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis :
    Basis (Fin 2) k (A ⧸ specialIdeal) :=
  residueBasis.map
    quotientAlgEquiv.symm.toLinearEquiv
end
end MazurProof.N13SpecialQuotientBasis
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
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra
theorem integralToRational_injective :
    Function.Injective integralToRational := by
  exact
    (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := N13IntegralModelContraction.Q₂)).injective.comp
      N13TwoAdicCoordinateBaseChange.extendCoordinate_injective
local instance integralRingDomain : IsDomain IntegralRing :=
  integralToRational_injective.isDomain integralToRational
local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization
def nonZeroDivisors_le_comap :
    IntegralRing⁰ ≤
      RationalRing⁰.comap integralToRational :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    integralToRational integralToRational_injective
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
attribute [local instance] MazurProof.N13IntegralGraphContraction.integralRationalAlgebra
local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
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
theorem mumfordIdeal_eq_special_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_graphDivisor_eq D hdeg hgraph
  calc
    mumfordIdeal D.u D.v = mumfordIdeal D.u 0 :=
      mumfordIdeal_eq_zero_of_dvd D.u D.v hv
    _ = N13SpecialQuotientBasis.specialIdeal := by
      simp [N13SpecialQuotientBasis.specialIdeal,
        N13SpecialQuotientBasis.specialData_u,
        N13SpecialQuotientBasis.specialData_v, hu]
/-- The complete special-fibre bridge: an Abel-compatible quadratic
Mumford graph has the fixed literal graph ideal. -/
theorem mumfordIdeal_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_graphDivisor_eq D hdeg
    (graphDivisor_eq_special_of_abel_eq G D hdeg habel)
/-- Set-valued Abel compatibility is already enough to identify the fixed
special graph ideal. -/
theorem mumfordIdeal_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel
/-- For quadratic special graphs, the intrinsic Abel class and the literal
graph ideal carry exactly the same information at the selected regular
class. -/
theorem setAbel_eq_iff_mumfordIdeal_eq_special
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal := by
  constructor
  · exact mumfordIdeal_eq_special_of_setAbel_eq D hdeg
  · intro hideal
    exact congrArg N13AbelFiberTwoModel.abel
      (graphDivisor_eq_special_of_mumfordIdeal_eq
        D hdeg hideal)
end
end MazurProof.N13SpecialGraphDivisor
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphReduction =====
section
/-!
# Abel-compatible reduction of integral N13 Mumford graphs

Coefficientwise reduction of a smooth integral generalized Mumford graph is
again a special-fibre Mumford graph.  If its effective degree-two divisor
has the selected set-valued Abel class, special Abel rigidity identifies the
literal reduced graph ideal with `(X²+X,Y)`.

Combining this with exact contraction of integral sextic graphs gives the
representative-level special-ideal equality required by the two-fibre graph
recovery theorem.  The remaining geometric input is now only the existence
of an integral representative and its Abel compatibility.
-/
open Polynomial
namespace MazurProof.N13SpecialGraphReduction
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphReduction.instFactPrimeOfNatNat_fLT
/-- For an integral quadratic graph, mapped-ideal equality is equivalent to
the intrinsic special-fibre Abel equality. -/
theorem setAbel_eq_iff_map_mumfordIdeal_eq_special
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (reduceSmoothMumford_u_natDegree D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal := by
  rw [N13GeneralizedMumfordReduction.map_smoothMumfordIdeal]
  exact
    N13SpecialGraphDivisor.setAbel_eq_iff_mumfordIdeal_eq_special
      (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
      (reduceSmoothMumford_u_natDegree D hdeg)
end
end MazurProof.N13SpecialGraphReduction
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
theorem branch_orders_add (p q : K[X])
    (hnorm : normNumerator K p q ≠ 0) :
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
        (N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q)).order =
      -((normNumerator K p q).natDegree : ℤ) := by
  have hproduct :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q) ≠ 0 := by
    rw [branch_product]
    exact evalPoly_ne_zero K hnorm
  have hplus :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) ≠ 0 :=
    right_ne_zero_of_mul hproduct
  calc
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
          (N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order =
        (N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order :=
      (HahnSeries.order_mul hplus hminus).symm
    _ = (evalPoly K (normNumerator K p q)).order := by
      rw [branch_product]
    _ = -((normNumerator K p q).natDegree : ℤ) :=
      evalPoly_order K _ hnorm
end
end MazurProof.N13BranchNorm
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
/-! ## Fractional invertibility -/
/-! ## Oriented primitive representatives -/
namespace IntegralOrientedRep
variable (O : InfinityOrder M)
def primitivePartUnit (R : IntegralOrientedRep M) : InvFrac M :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit
@[simp] theorem coe_primitivePartUnit
    (R : IntegralOrientedRep M) :
    (R.primitivePartUnit M :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      primitivePart M R.ideal (contentGenerator M R.ideal) :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit_spec
/-- Divide the integral ideal by its polynomial content and adjust the
stored orientation by the exact `ordPlus` of that principal factor. -/
def primitivePartRep (R : IntegralOrientedRep M) :
    IntegralOrientedRep M where
  ideal := primitivePart M R.ideal (contentGenerator M R.ideal)
  unit := R.primitivePartUnit M
  coe_unit := coe_primitivePartUnit M R
  atInfinity :=
    R.atInfinity -
      Multiplicative.toAdd (O.ordPlus (R.contentUnit M))
@[simp] theorem primitivePartRep_ideal
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).ideal =
      primitivePart M R.ideal (contentGenerator M R.ideal) := rfl
@[simp] theorem primitivePartRep_atInfinity
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).atInfinity =
      R.atInfinity -
        Multiplicative.toAdd (O.ordPlus (R.contentUnit M)) := rfl
theorem primitivePartRep_isPrimitive
    (R : IntegralOrientedRep M) :
    IdealIsPrimitive M (R.primitivePartRep M O).ideal :=
  primitivePart_isPrimitive M R.ideal
end IntegralOrientedRep
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
@[simp] theorem reduceDegree_class
    (D : SemiMumford M) :
    semiMumfordClass M O (reduceDegree M O D).toSemi =
      semiMumfordClass M O D := by
  rw [reduceDegree]
  split_ifs with hsmall
  · rfl
  · rw [reduceDegree_class, degreeStep_class]
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
/-! ## Degree bounds -/
/-! ## Leading terms at the two infinities -/
theorem branch_order_lower_bounds_of_natDegree_three
    (V : K[X]) (hV : V.natDegree = 3) :
    (-3 : ℤ) ≤
        (N13Infinity.coordinateToLaurent K
          (ySubClass (N13Mumford.model K) V)).order ∧
      (-3 : ℤ) ≤
        (N13InfinityMinus.coordinateToLaurentMinus K
          (ySubClass (N13Mumford.model K) V)).order := by
  have hlinear := linearFunction_neg_eq_ySubClass (K := K) V
  have hmin := N13BranchLeading.branch_min_order K (-V) 1
    (by
      rw [hlinear]
      exact ySubClass_ne_zero (N13Mumford.model K) V)
  rw [hlinear] at hmin
  have hpole :
      N13BranchLeading.poleDegree K (-V) 1 = 3 := by
    simp [N13BranchLeading.poleDegree, hV]
  rw [hpole] at hmin
  constructor <;> omega
theorem plusYSub_minus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (plusLift D)
      (plusLift_isMonicOfDegree D hdeg).natDegree_eq).2
  have hupper :
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [plusYSub_minus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower
theorem minusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (minusLift D)
      (by
        rw [← natDegree_neg]
        exact (neg_minusLift_isMonicOfDegree D hdeg).natDegree_eq)).1
  have hupper :
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (minusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [minusYSub_plus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower
/-! ## Exact orders of the principal Cantor corrections -/
theorem plusYSub_branch_orders_add :
    (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (plusLift D))).order +
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order =
      -((D.u.natDegree + (plusFactor D).natDegree : ℕ) : ℤ) := by
  have hsum := N13BranchNorm.branch_orders_add K
    (-(plusLift D)) 1 (plusNormNumerator_ne_zero D)
  rw [linearFunction_neg_eq_ySubClass] at hsum
  rw [plusNormNumerator_natDegree D] at hsum
  exact hsum
theorem plusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (plusLift D))).order =
        3 - (D.u.natDegree : ℤ) -
          ((plusFactor D).natDegree : ℤ) := by
  have hsum := plusYSub_branch_orders_add D
  have hminus := plusYSub_minus_order D hdeg
  omega
theorem plusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (plusLift D) (plusFactor D) (plusFactor_ne_zero D))) =
      3 - (D.u.natDegree : ℤ) := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    plusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring
theorem minusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (minusLift D) (minusFactor D) (minusFactor_ne_zero D))) =
      (minusFactor D).natDegree - 3 := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    minusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring
/-! ## The two class-preserving balancing steps -/
@[simp] theorem plusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (plusStep D).nInf =
      D.nInf + (D.u.natDegree : ℤ) - 3 := by
  rw [plusStep, cantorNextSemi_nInf, plusCorrection_order D hdeg]
  ring
@[simp] theorem minusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (minusStep D).nInf =
      D.nInf + 3 - (minusFactor D).natDegree := by
  rw [minusStep, cantorNextSemi_nInf, minusCorrection_order D hdeg]
  ring
theorem minusStep_nInf_gt
    (E : LowDegree (K := K)) :
    E.toSemi.nInf < (minusStep E.toSemi).nInf := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_nInf E.toSemi E.degree_le_two]
  omega
theorem minusStep_upper_wall
    (E : LowDegree (K := K)) (_hn : E.toSemi.nInf < 0) :
    ((minusStep E.toSemi).u.natDegree : ℤ) +
        (minusStep E.toSemi).nInf ≤ 2 := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_natDegree,
    minusStep_nInf E.toSemi E.degree_le_two]
  omega
theorem plusStep_lower_wall
    (E : LowDegree (K := K))
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    0 ≤ (plusStep E.toSemi).nInf := by
  rw [plusStep_nInf E.toSemi E.degree_le_two]
  omega
theorem plusStep_upper_excess_lt
    (E : LowDegree (K := K)) :
    ((plusStep E.toSemi).u.natDegree : ℤ) +
          (plusStep E.toSemi).nInf - 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2 := by
  have he :=
    plusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [plusStep_natDegree,
    plusStep_nInf E.toSemi E.degree_le_two]
  omega
/-! ## A well-founded measure for the two balance walls -/
theorem imbalance_minusStepLow_lt
    (E : LowDegree (K := K)) (hn : E.toSemi.nInf < 0) :
    imbalance (minusStepLow E) < imbalance E := by
  have hgt := minusStep_nInf_gt E
  have hnewUpper := minusStep_upper_wall E hn
  have holdUpper :
      upperDefect E = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    have hd := E.degree_le_two
    omega
  have hnextUpper :
      upperDefect (minusStepLow E) = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    exact sub_nonpos.mpr hnewUpper
  rw [imbalance, imbalance, holdUpper, hnextUpper,
    Nat.add_zero, Nat.add_zero]
  apply (Int.toNat_lt_toNat (by omega)).2
  change -(minusStep E.toSemi).nInf < -E.toSemi.nInf
  omega
theorem imbalance_plusStepLow_lt
    (E : LowDegree (K := K))
    (hn : 0 ≤ E.toSemi.nInf)
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    imbalance (plusStepLow E) < imbalance E := by
  have hnewLower := plusStep_lower_wall E hhigh
  have hexcess := plusStep_upper_excess_lt E
  have holdLower :
      lowerDefect E = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    omega
  have hnextLower :
      lowerDefect (plusStepLow E) = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    exact neg_nonpos.mpr hnewLower
  rw [imbalance, imbalance, holdLower, hnextLower,
    Nat.zero_add, Nat.zero_add]
  apply (Int.toNat_lt_toNat (by omega)).2
  exact hexcess
/-! ## Structural infinity balancing -/
def balanceInfinity
    (E : LowDegree (K := K)) :
    N13Mumford.Mumford K :=
  if hn : E.toSemi.nInf < 0 then
    balanceInfinity (minusStepLow E)
  else if hhigh :
      2 < (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf then
    balanceInfinity (plusStepLow E)
  else
    toBalanced E (le_of_not_gt hn) (le_of_not_gt hhigh)
termination_by imbalance E
decreasing_by
  · exact imbalance_minusStepLow_lt E hn
  · exact imbalance_plusStepLow_lt E (le_of_not_gt hn) hhigh
end
end MazurProof.N13MumfordInfinityBalance
end

end

-- ===== FLT.Assumptions.MazurProof.N13SmallMumfordRigidity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SmallMumfordRigidity =====
section
/-!
# Rigidity of balanced Mumford representatives on `X₁(13)`

For balanced representatives, a principal relation clears to two affine
factors whose product has degree at most four.  The two-infinity pole-order
argument forces both factors into the polynomial subring.  Ideal
contraction then identifies the monic `u`-polynomials, so the principal
function is constant and the balanced representatives agree.

Together with structural infinity balancing, this gives the full unique
Mumford normal form and hence the Abel--Jacobi embedding of the curve,
without coefficient enumeration.
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13SmallMumfordRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford
theorem eq_of_class_eq
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (hclass :
      classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₁ =
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₂) :
    D₁ = D₂ := by
  obtain ⟨α, hIdeal, hInf⟩ :=
    (classOf_eq_iff (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) D₁ D₂).mp hclass
  obtain ⟨c, hα⟩ :=
    principal_is_constant K D₁ D₂ α hIdeal hInf
  exact N13Mumford.principal_between_balanced_of_constant
    K c hα hIdeal hInf
theorem classOf_injective :
    Function.Injective
      (classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)) := by
  intro D₁ D₂
  exact eq_of_class_eq K D₁ D₂
end
end MazurProof.N13SmallMumfordRigidity
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
namespace DiskPair
variable (P : DiskPair)
/-- Distinct pairs in the two residue disks give distinct Picard classes.
The proof is global normal-form rigidity followed by faithfulness of
coefficient extension. -/
theorem pic_injective :
    Function.Injective DiskPair.pic := by
  intro P Q hPQ
  have hM : P.mumford = Q.mumford :=
    N13SmallMumfordRigidity.classOf_injective Q₂ hPQ
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  apply Polynomial.map_injective
    N13TwoAdicMumfordTransport.coeffMap
    (IsFractionRing.injective
      N13TwoAdicMumfordTransport.R₂ Q₂)
  simpa only [mumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply] using
    congrArg SexticMumford.Mumford.u hM
theorem centeredPic_injective :
    Function.Injective centeredPic := by
  intro P Q hPQ
  apply pic_injective
  exact sub_left_injective hPQ
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
namespace NearBaseMumford
variable (D : NearBaseMumford)
/-- The recovered disk pair has exactly the original monic quadratic. -/
theorem diskPair_u :
    D.diskPair.u = D.u := by
  exact
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      D.diskPair.u_monic D.u_monic D.diskPair_u_dvd
      (by rw [D.u_natDegree, D.diskPair_u_natDegree])).symm
theorem u_dvd_v_sub_diskPair_v :
    D.u ∣ D.v - D.diskPair.v := by
  rw [← D.diskPair_u]
  exact D.diskPair_u_dvd_v_sub
/-- The recovered disk pair cuts out exactly the original integral graph
ideal. -/
theorem mumfordIdeal_diskPair :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        D.diskPair.u D.diskPair.v := by
  rw [D.diskPair_u]
  exact mumfordIdeal_eq_of_dvd_sub
    D.u D.v D.diskPair.v D.u_dvd_v_sub_diskPair_v
/-- Completion of the square carries the original graph and the recovered
disk graph to the same standard sextic Mumford ideal. -/
theorem sextic_mumfordIdeal_diskPair :
    SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v := by
  rw [
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.toSmoothMumford₂ 0,
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.diskPair.smoothMumford 0]
  exact congrArg
    (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
    D.mumfordIdeal_diskPair
theorem sextic_mumfordIdealUnit_diskPair :
    SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0) := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v :
      FractionalIdeal
        (N13Mumford.CoordinateRing Q₂)⁰
        (N13Mumford.FunctionField Q₂)) =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v
  rw [D.sextic_mumfordIdeal_diskPair]
/-- Recovery is compatible with the actual oriented Picard class. -/
theorem pic_eq_diskPair_pic :
    D.pic =
      N13TwoAdicAbelChartPic.DiskPair.pic D.diskPair := by
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicAbelChartPic.DiskPair.mumford D.diskPair)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0)
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · exact D.sextic_mumfordIdealUnit_diskPair
  · rfl
theorem centeredPic_eq_diskPair_centeredPic :
    D.centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic D.diskPair := by
  rw [centeredPic,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic,
    D.pic_eq_diskPair_pic]
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
/-- Abel compatibility of the special fibre makes the normalized integral
graph a literal near-base graph. -/
def normalizedNearBase
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree
              D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    N13TwoAdicAbelChartRecover.NearBaseMumford where
  toSmoothMumford₂ := normalizeSmoothMumford D
  reduce_u := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    exact
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).1
  reduce_v := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    have hdvd :
        N13GeneralizedMumfordReduction.reducePoly D.u ∣
          N13GeneralizedMumfordReduction.reducePoly D.v :=
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).2
    change
      N13GeneralizedMumfordReduction.reducePoly
          (D.v %ₘ D.u) = 0
    rw [N13GeneralizedMumfordReduction.reducePoly_apply,
      Polynomial.map_modByMonic
        N13GeneralizedMumfordReduction.reduceBase D.u_monic]
    exact
      (Polynomial.modByMonic_eq_zero_iff_dvd
        (D.u_monic.map
          N13GeneralizedMumfordReduction.reduceBase)).2 hdvd
/-- The representative-level mapped-ideal equality is an equivalent and
often more convenient input than the set-valued Abel equality. -/
def normalizedNearBaseOfMappedSpecial
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal) :
    N13TwoAdicAbelChartRecover.NearBaseMumford :=
  normalizedNearBase D hdeg
    ((N13SpecialGraphReduction.setAbel_eq_iff_map_mumfordIdeal_eq_special
      D hdeg).2 hmap)
/-- Hensel recovery directly from the literal mapped special ideal. -/
def recoveredDiskPairOfMappedSpecial
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal) :
    N13TwoAdicAbelChartData.DiskPair :=
  (normalizedNearBaseOfMappedSpecial D hdeg hmap).diskPair
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
attribute [local instance] MazurProof.N13GenericQuotientLocalization.integralRationalAlgebra
local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization
end
end MazurProof.N13GenericQuotientLocalization
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
local instance integralRingDomain :
    IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRationalAlgebra
open N13GeneralizedMumfordIntegral
/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/
end
end MazurProof.N13IntegralGraphJacobian
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
local instance integralRingDomain :
    IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
attribute [local instance] MazurProof.N13VerticalGraphJacobian.integralRationalAlgebra
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
local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
attribute [local instance] MazurProof.N13FiniteContractIdealInvertible.integralRationalAlgebra
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
theorem pi_span_prime :
    (Ideal.span ({pi} : Set GI)).IsPrime :=
  (Ideal.span_singleton_prime pi_ne_zero).mpr pi_prime
/-- The translated cubic is Eisenstein at the unique displayed ramified
Gaussian prime. -/
theorem h_eisenstein :
    h.IsEisensteinAt (Ideal.span ({pi} : Set GI)) := by
  apply h_monic.isEisensteinAt_of_mem_of_notMem pi_span_prime.ne_top
  · intro n hn
    rw [h_natDegree] at hn
    interval_cases n
    · rw [h_coeff_zero, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_one, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_two, Ideal.mem_span_singleton]
      exact ⟨pi * (1 + 2 * i), by ring⟩
  · intro hmem
    rw [h_coeff_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨d, hd⟩
    apply pi_not_dvd_constantQuotient
    refine ⟨d, ?_⟩
    apply mul_left_cancel₀ pi_ne_zero
    calc
      pi * (231 + 94 * i) = pi ^ 2 * d := hd
      _ = pi * (pi * d) := by ring
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
/-- The trace discriminant of a power basis is the polynomial discriminant
of its minimal polynomial. -/
theorem discr_basis_eq_minpoly_discr
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L) :
    Algebra.discr K B.basis =
      (minpoly K B.gen).discr := by
  rw [Algebra.discr_powerBasis_eq_norm K B]
  rw [norm_aeval_eq_resultant B]
  let f := minpoly K B.gen
  have hfmonic : f.Monic :=
    minpoly.monic B.isIntegral_gen
  have hderiv :
      f.derivative.natDegree ≤ f.natDegree - 1 :=
    Polynomial.natDegree_derivative_le f
  have hpad :
      f.resultant f.derivative =
        f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
    symm
    calc
      f.resultant f.derivative f.natDegree (f.natDegree - 1) =
          f.resultant f.derivative f.natDegree
            (f.derivative.natDegree +
              ((f.natDegree - 1) - f.derivative.natDegree)) := by
        rw [Nat.add_sub_of_le hderiv]
      _ = f.coeff f.natDegree ^
            ((f.natDegree - 1) - f.derivative.natDegree) *
          f.resultant f.derivative f.natDegree
            f.derivative.natDegree := by
        rw [Polynomial.resultant_add_right_deg
          f f.derivative f.natDegree f.derivative.natDegree
          ((f.natDegree - 1) - f.derivative.natDegree) le_rfl]
      _ = f.resultant f.derivative := by
        rw [Polynomial.coeff_natDegree, hfmonic.leadingCoeff]
        simp
  rw [hpad]
  have hdeg : 0 < (minpoly K B.gen).degree := by
    rw [B.degree_minpoly]
    simpa using B.dim_pos
  rw [Polynomial.resultant_deriv hdeg]
  rw [(minpoly.monic B.isIntegral_gen).leadingCoeff, mul_one]
  rw [B.natDegree_minpoly, ← B.finrank]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp
/-- For an integral power-basis generator over an integrally closed base,
the basis discriminant is the image of its integral minimal-polynomial
discriminant. -/
theorem powerBasis_discr_eq_map_discr
    {R K L : Type*}
    [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (hBint : IsIntegral R B.gen)
    (h : R[X])
    (hmin : minpoly R B.gen = h) :
    Algebra.discr K B.basis =
      algebraMap R K h.discr := by
  rw [discr_basis_eq_minpoly_discr B]
  have hminK :
      minpoly K B.gen =
        h.map (algebraMap R K) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hBint, hmin]
  have hhmonic : h.Monic := by
    rw [← hmin]
    exact minpoly.monic hBint
  have hnat : h.natDegree = B.dim := by
    rw [← hhmonic.natDegree_map (algebraMap R K)]
    rw [← hminK]
    exact B.natDegree_minpoly
  have hdeg : 0 < h.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hnat]
    exact B.dim_pos
  rw [hminK]
  exact discr_map_of_monic_of_degree_pos
    (algebraMap R K) hhmonic hdeg
/-- Literal rational `AdjoinRoot` specialization of the norm--resultant
identity. -/
theorem norm_aeval_adjoinRoot_eq_resultant
    {f : ℚ[X]}
    (hf : f.Monic)
    (hirr : Irreducible f)
    (q : ℚ[X]) :
    Algebra.norm ℚ
        (Polynomial.aeval (AdjoinRoot.root f) q) =
      f.resultant q := by
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let B : PowerBasis ℚ (AdjoinRoot f) :=
    AdjoinRoot.powerBasis hf.ne_zero
  letI : Module.Finite ℚ (AdjoinRoot f) :=
    B.finite
  have h := norm_aeval_eq_resultant B q
  have hmin : minpoly ℚ B.gen = f := by
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hf
  rw [hmin] at h
  exact h
end
end MazurProof.PowerBasisDiscriminant
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianCubicField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianCubicField =====
section
/-!
# The global N13 Gaussian cubic field

We form the fraction field `K = Frac(ℤ[i])` and adjoin a root of the
translated Gaussian cubic.  Its Eisenstein property proves irreducibility,
while the discriminant--Eisenstein criterion identifies the monogenic
Gaussian order with the full relative integral closure.

This file contains no class-group computation and no integral-basis search.
-/
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
/-- Eisenstein gives irreducibility already over `ℤ[i]`. -/
theorem h_irreducible : Irreducible h :=
  h_eisenstein.irreducible pi_span_prime h_monic.isPrimitive
    (by rw [h_natDegree]; norm_num)
/-- Gauss's lemma transports the structural Eisenstein proof to the
Gaussian fraction field. -/
theorem hK_irreducible : Irreducible hK := by
  exact
    h_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      h_irreducible
@[reducible] def hKIrreducibleFact :
    Fact (Irreducible hK) :=
  ⟨hK_irreducible⟩
/-- Exported opt-in field structure for downstream arithmetic files. -/
@[reducible] noncomputable def cubicField : Field L := by
  letI := hKIrreducibleFact
  infer_instance
local instance instFactIrreduciblePolynomialKHK : Fact (Irreducible hK) :=
  hKIrreducibleFact
local instance fieldL : Field L :=
  AdjoinRoot.instField
/-- The relative power basis `1, α, α²`. -/
def powerBasis : PowerBasis K L :=
  AdjoinRoot.powerBasis hK_monic.ne_zero
local instance finiteKL : Module.Finite K L :=
  powerBasis.finite
local instance separableKL : Algebra.IsSeparable K L :=
  inferInstance
@[simp] theorem powerBasis_gen :
    powerBasis.gen = alpha := by
  rfl
theorem powerBasis_dim :
    powerBasis.dim = 3 := by
  rw [powerBasis, AdjoinRoot.powerBasis_dim]
  rw [hK, h_monic.natDegree_map]
  exact h_natDegree
/-- The relative field basis `(1, α, α²)` with fixed index `Fin 3`. -/
def relativeFieldBasis : Basis (Fin 3) K L :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)
@[simp] theorem relativeFieldBasis_apply (j : Fin 3) :
    relativeFieldBasis j = alpha ^ (j : ℕ) := by
  rw [relativeFieldBasis, Basis.reindex_apply,
    powerBasis.basis_eq_pow]
  have hindex :
      (((finCongr powerBasis_dim).symm j) : ℕ) =
        (j : ℕ) := rfl
  rw [hindex, powerBasis_gen]
/-- The shifted generator is integral over the Gaussian integers. -/
theorem alpha_integral : IsIntegral GI alpha := by
  refine ⟨h, h_monic, ?_⟩
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  change h.eval₂ (algebraMap GI L) alpha = 0
  rw [hmap]
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root hK
/-! ## The relative integral basis -/
local instance faithfulGIL : FaithfulSMul GI L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply IsFractionRing.injective GI K
  apply (algebraMap K L).injective
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  rw [hmap] at hxy
  exact hxy
/-! ## Discriminant of the relative integral basis -/
local instance integralClosureLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (integralClosure GI L) (nonZeroDivisors GI)) L :=
  IsIntegralClosure.isLocalization
    GI K L (integralClosure GI L)
end
end MazurProof.N13GaussianCubicField
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
/-! ## The integral basis `(1,i)` -/
/-! ## Cofinality of ordinary integer denominators -/
/-! ## The localized rational basis -/
/-! ## Power basis, minimal polynomial, and discriminant -/
/-- The rational basis `(1,i)` is the power basis generated by `i`. -/
def gaussianPowerBasis : PowerBasis ℚ K where
  gen := iK
  dim := 2
  basis := gaussianBasis
  basis_eq_pow := by
    intro j
    fin_cases j
    · simp
    · simpa using gaussianBasis_one
@[simp] theorem gaussianPowerBasis_gen :
    gaussianPowerBasis.gen = iK := rfl
@[simp] theorem gaussianPowerBasis_dim :
    gaussianPowerBasis.dim = 2 := rfl
@[simp] theorem gaussianPowerBasis_basis :
    gaussianPowerBasis.basis = gaussianBasis := rfl
theorem minpoly_iK :
    minpoly ℚ iK = gaussianMinpoly := by
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly ℚ iK
  · exact gaussianMinpoly_monic
  · exact aeval_gaussianMinpoly
  · have hdeg :
        (minpoly ℚ iK).degree =
          ((2 : ℕ) : WithBot ℕ) := by
      simpa only [gaussianPowerBasis_gen,
        gaussianPowerBasis_dim] using
        (PowerBasis.degree_minpoly gaussianPowerBasis)
    rw [gaussianMinpoly_degree, hdeg]
@[simp] theorem trace_iK :
    Algebra.trace ℚ K iK = 0 := by
  have h :=
    PowerBasis.trace_gen_eq_nextCoeff_minpoly gaussianPowerBasis
  simpa only [gaussianPowerBasis_gen, minpoly_iK,
    gaussianMinpoly_nextCoeff, neg_zero] using h
/-- The discriminant of the structural Gaussian basis `(1,i)`. -/
theorem discr_gaussianBasis :
    Algebra.discr ℚ gaussianBasis = -4 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, gaussianBasis_zero,
    gaussianBasis_one, one_mul, mul_one, iK_mul_self,
    trace_one_gaussian, trace_iK, trace_neg_one_gaussian]
  norm_num
/-- The integral Gaussian basis has the same discriminant `-4`.
This follows by localizing the basis, not by recomputing its trace matrix. -/
theorem discr_gaussianIntBasis :
    Algebra.discr ℤ gaussianIntBasis = -4 := by
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.discr_localizationLocalization
    ℤ (nonZeroDivisors ℤ) K gaussianIntBasis]
  exact discr_gaussianBasis
end
end MazurProof.N13GaussianFractionField
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
/-- The two local representatives differ by a rational scalar and a square. -/
theorem survivor_mul_square :
    survivor * squareFactor ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  rw [survivor, squareFactor, e2_mul_primeA_mul_primeQ,
    zeta_mul_e1_mul_primeA]
  exact compressed_scaled_identity_in_algebra
end
end MazurProof.N13SexticSquareclass
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
local instance fieldLg : Field Lg :=
  N13GaussianCubicField.cubicField
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLs
local instance finiteKL : Module.Finite K Lg :=
  N13GaussianCubicField.powerBasis.finite
local instance finiteQL : Module.Finite ℚ Lg :=
  Module.Finite.trans K Lg
def gaussianTheta : Lg :=
  N13GaussianCubicField.alpha + 9
theorem alpha_root_h :
    eval₂ (algebraMap GI Lg)
      N13GaussianCubicField.alpha
      N13GaussianGlobalArithmetic.h = 0 := by
  have hmap :
      algebraMap GI Lg =
        (algebraMap K Lg).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K Lg
  rw [hmap, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root N13GaussianCubicField.hK
/-! ## Integrality of the structural generators -/
theorem gaussianI_integral :
    IsIntegral ℤ gaussianI := by
  have hi :
      IsIntegral ℤ
        (algebraMap GI Lg
          N13GaussianGlobalArithmetic.i) :=
    N13GaussianFractionField.i_integral.algebraMap
  simpa only [gaussianI,
    IsScalarTower.algebraMap_apply GI K Lg] using hi
theorem lg_natCast_integral (n : ℕ) :
    IsIntegral ℤ (n : Lg) := by
  have h :
      IsIntegral ℤ
        (algebraMap ℤ Lg (n : ℤ)) :=
    isIntegral_algebraMap
  rw [map_natCast (algebraMap ℤ Lg) n] at h
  exact h
theorem gaussianTheta_integral :
    IsIntegral ℤ gaussianTheta := by
  have ha :
      IsIntegral ℤ N13GaussianCubicField.alpha :=
    isIntegral_trans
      N13GaussianCubicField.alpha
      N13GaussianCubicField.alpha_integral
  exact ha.add (lg_natCast_integral 9)
end
end MazurProof.N13GaussianFieldEquiv
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
attribute [local instance] MazurProof.N13MumfordKummerRelation.sexticAlgebraField
/-- The raw fake-Kummer value depends only on the oriented Picard class.
The infinity equality in `classOf_eq_iff` is not needed after extracting
the finite principal-ideal relation. -/
theorem mumfordFakeClass_eq_of_classOf_eq
    (O : InfinityOrder M)
    (D₁ D₂ : N13Mumford.Mumford ℚ)
    (h :
      classOf M O D₁ = classOf M O D₂) :
    N13MumfordKummerValue.mumfordFakeClass D₁ =
      N13MumfordKummerValue.mumfordFakeClass D₂ := by
  obtain ⟨α, hIdeal, -⟩ :=
    (classOf_eq_iff M O D₁ D₂).mp h
  exact mumfordFakeClass_eq_of_principal_relation
    D₁ D₂ α hIdeal
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
/-- Equality of original oriented classes gives equality of fake values.
Only the finite principal-ideal component is consumed by the existing
principal-relation theorem. -/
theorem lowFakeClass_eq_of_class_eq
    (D₁ D₂ : LowRep)
    (h : lowClass D₁ = lowClass D₂) :
    lowFakeClass D₁ = lowFakeClass D₂ := by
  obtain ⟨alpha, hIdeal, -⟩ :=
    (semiMumfordClass_eq_iff M O D₁.toSemi D₂.toSemi).mp h
  apply
    N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation
      (asMumford D₁) (asMumford D₂) alpha
  simpa only [mumfordIdealUnit_asMumford] using hIdeal
end
end MazurProof.N13LowDegreeKummerHom
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
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField
/-- The forgetting kernel has exactly the two displayed alternatives; the
theorem does not require proving that those alternatives are distinct. -/
theorem forget_eq_one_iff (z : FullTarget) :
    forget z = 1 ↔ z = 1 ∨ z = signClass := by
  exact
    EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
      normUnits scalarUnits normUnits_scalarUnits
      (-1 : ℚˣ) minusOne_sq ratUnit_sq_eq_one z
end
end MazurProof.N13FullNormPair
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
/-- The actual low-degree Kummer value has rational square norm. -/
theorem norm_uTheta_eq_normRoot_sq (D : LowRep) :
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
      normRoot D ^ 2 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :=
    PowerBasisDiscriminant.norm_aeval_adjoinRoot_eq_resultant
      (N13Mumford.f_monic (K := ℚ))
      N13SexticIrreducible.n13Mumford_f_irreducible
      D.toSemi.u
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        (N13Mumford.f ℚ).resultant D.toSemi.u := by
      rw [N13MumfordKummerValue.uTheta_eq_mk]
      change
        Algebra.norm ℚ
            (AdjoinRoot.mk (N13Mumford.f ℚ) D.toSemi.u) =
          (N13Mumford.f ℚ).resultant D.toSemi.u
      rw [← AdjoinRoot.aeval_eq]
      exact hnorm
    _ = normRoot D ^ 2 :=
      resultant_f_u_eq_normRoot_sq D
theorem normRoot_ne_zero (D : LowRep) :
    normRoot D ≠ 0 := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr
      (N13MumfordKummerValue.uTheta_ne_zero
        (N13LowDegreeKummerHom.asMumford D))
  intro hzero
  apply hnorm
  calc
    Algebra.norm ℚ
        (N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D)) =
        normRoot D ^ 2 :=
      norm_uTheta_eq_normRoot_sq D
    _ = 0 := by rw [hzero]; simp
/-- The chosen square root of the norm, as a rational unit. -/
def normRootUnit (D : LowRep) : ℚˣ :=
  Units.mk0 (normRoot D) (normRoot_ne_zero D)
@[simp] theorem normRootUnit_val (D : LowRep) :
    (normRootUnit D : ℚ) = normRoot D :=
  rfl
end
end MazurProof.N13MumfordKummerNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerNormalization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerNormalization =====
section
/-!
# Global primitive normalization of N13 Kummer values

A rational Mumford polynomial need not have integral coefficients.  We clear
all denominators simultaneously over `ℤ`, remove the polynomial content, and
evaluate the resulting primitive polynomial at the integral Gaussian-cubic
generator `α + 9`.

The resulting element lies in the actual absolute ring of integers and
differs from the original Kummer value by one nonzero rational scalar.
Primitivity and the degree bound are retained, and the norm of the integral
representative remains a rational square.  Thus denominator clearing is
separated cleanly from the subsequent ideal factorization.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizationMonoid
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
/-- The integral point corresponding to the sextic generator. -/
def integralTheta : integralClosure ℤ L :=
  ⟨gaussianTheta, gaussianTheta_integral⟩
/-- Evaluate an integral polynomial inside the actual absolute ring of
integers. -/
def integralEval (U : ℤ[X]) :
    integralClosure ℤ L :=
  aeval integralTheta U
@[simp] theorem coe_integralEval (U : ℤ[X]) :
    ((integralEval U : integralClosure ℤ L) : L) =
      eval₂ (algebraMap ℤ L) gaussianTheta U := by
  change
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
      eval₂ (algebraMap ℤ L) gaussianTheta U
  have h :=
    Polynomial.hom_eval₂ U
      (algebraMap ℤ (integralClosure ℤ L))
      (Subalgebra.val (integralClosure ℤ L)).toRingHom
      integralTheta
  have hmaps :
      (Subalgebra.val
          (integralClosure ℤ L)).toRingHom.comp
          (algebraMap ℤ (integralClosure ℤ L)) =
        algebraMap ℤ L :=
    RingHom.ext_int _ _
  calc
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
        eval₂
          ((Subalgebra.val
              (integralClosure ℤ L)).toRingHom.comp
            (algebraMap ℤ (integralClosure ℤ L)))
          ((Subalgebra.val
            (integralClosure ℤ L)) integralTheta) U :=
      h
    _ =
        eval₂ (algebraMap ℤ L) gaussianTheta U := by
      rw [hmaps]
      rfl
end
end MazurProof.N13GlobalKummerNormalization
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerIdealSquare =====
section
/-!
# The branch ideal of an N13 Mumford relation is a square

The identity behind the good-prime part of the two-descent is

`(u(θ), v(θ))² = (u(θ))`.

It follows without factoring `u`, splitting into its possible degrees, or
computing valuations.  If `f - v² = u w`, then any prime containing both
`u(θ)` and `w(θ)` also contains `v(θ)` and hence `f'(θ)`.  Thus, wherever
`f'(θ)` is a unit, `u(θ)` and `w(θ)` are coprime.  Bézout and
`u(θ)w(θ) = -v(θ)²` then give the displayed ideal identity.

For N13 we implement "away from the different" literally: start with the
integral monogenic order and invert `f'(θ)`.  No discriminant expansion or
prime-ideal table enters the proof.
-/
open Polynomial
namespace MazurProof.N13MumfordKummerIdealSquare
noncomputable section
variable {R : Type*} [CommRing R]
/-! The N13 monogenic order with its different inverted. -/
def integralTheta : IntegralOrder :=
  AdjoinRoot.root N13SexticIrreducible.fInt
end
end MazurProof.N13MumfordKummerIdealSquare
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
local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField
/-! ## The principal-ideal endpoint -/
end
end MazurProof.N13GlobalKummerIdealSquare
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNumberField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNumberField =====
section
/-!
# The absolute N13 number field

The N13 Gaussian cubic is a degree-three extension of the quadratic
Gaussian field.  Combining the structural bases in the two stages gives
the six-element rational basis

`1, α, α², i, iα, iα²`.

This is a tower-basis construction; no embeddings or field elements are
enumerated.
-/
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L
/- The subtype algebras otherwise prefer transitive `Subalgebra.algebra`
instances.  For a tower starting at `ℤ`, use the unique canonical integer
algebra structures so their modules are definitionally the usual `zsmul`
modules carried by the explicit bases. -/
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraGI
local instance intAlgebraRelativeIntegers :
    Algebra ℤ (integralClosure GI L) :=
  Ring.toIntAlgebra (integralClosure GI L)
local instance intAlgebraAbsoluteIntegers :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)
/-- The relative `K`-basis `(1, α, α²)`, with a fixed index type. -/
def relativeBasis : Basis (Fin 3) K L :=
  N13GaussianCubicField.powerBasis.basis.reindex
    (finCongr N13GaussianCubicField.powerBasis_dim)
/-- The absolute tower basis
`1, α, α², i, iα, iα²`, indexed base-first. -/
def absoluteBasis : Basis (Fin 2 × Fin 3) ℚ L :=
  N13GaussianFractionField.gaussianBasis.smulTower
    relativeBasis
instance finiteKL : Module.Finite K L :=
  N13GaussianCubicField.powerBasis.finite
instance finiteQL : Module.Finite ℚ L :=
  Module.Finite.trans K L
instance numberFieldL : NumberField L :=
  NumberField.of_module_finite K L
@[simp] theorem finrank_Q_L :
    Module.finrank ℚ L = 6 := by
  rw [Module.finrank_eq_card_basis absoluteBasis]
  simp
/-! ## The absolute ring of integers -/
/-- Change only the proof that an element of `L` is integral.  Since the
underlying carrier map is the identity, this is an algebra equivalence. -/
def relativeToAbsoluteAlgEquiv :
    integralClosure GI L ≃ₐ[ℤ] integralClosure ℤ L where
  toFun x := ⟨x.1, isIntegral_trans x.1 x.2⟩
  invFun x := ⟨x.1, x.2.tower_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
/-- The linear equivalence underlying the carrier-preserving algebra
equivalence. -/
def relativeToAbsoluteLinearEquiv :
    integralClosure GI L ≃ₗ[ℤ] integralClosure ℤ L :=
  relativeToAbsoluteAlgEquiv.toAddEquiv.toIntLinearEquiv
/- Mathlib packages the ring of integers as a separate definition rather
than exposing the integral-closure subtype directly.  This carrier-preserving
equivalence is the explicit bridge between the two presentations. -/
def integralClosureToRingOfIntegersRingEquiv :
    integralClosure ℤ L ≃+*
      NumberField.RingOfIntegers L :=
  (NumberField.RingOfIntegers.equiv
    (integralClosure ℤ L)).symm
/-- The carrier-preserving bridge respects the canonical integer algebra
structures. -/
def integralClosureToRingOfIntegersAlgEquiv :
    integralClosure ℤ L ≃ₐ[ℤ]
      NumberField.RingOfIntegers L :=
  AlgEquiv.ofRingEquiv
    (f := integralClosureToRingOfIntegersRingEquiv)
    (fun z => by simp)
/-! ## Absolute discriminant -/
end
end MazurProof.N13GaussianNumberField
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
local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField
local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L
local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O
local instance charZeroL : CharZero L :=
  charZero_of_injective_algebraMap
    (algebraMap ℚ L).injective
local instance charZeroCompletion
    (P : HeightOneSpectrum O) :
    CharZero (P.adicCompletion L) :=
  charZero_of_injective_algebraMap
    (algebraMap L (P.adicCompletion L)).injective
abbrev LocalIntegers
    (P : HeightOneSpectrum O) : Type :=
  P.adicCompletionIntegers L
/-- Map an integral polynomial into the integer ring of the completion. -/
def localPolynomial
    (P : HeightOneSpectrum O) (p : ℤ[X]) :
    (LocalIntegers P)[X] :=
  p.map (algebraMap ℤ (LocalIntegers P))
/-- The integral sextic branch point inside the local integer ring. -/
def localTheta
    (P : HeightOneSpectrum O) :
    LocalIntegers P :=
  algebraMap O (LocalIntegers P) integralTheta
def localF
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P N13SexticIrreducible.fInt
end
end MazurProof.N13GlobalKummerSimpleRootParity
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
local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField
local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L
local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O
local instance charZeroL : CharZero L :=
  charZero_of_injective_algebraMap
    (algebraMap ℚ L).injective
local instance charZeroCompletion
    (P : HeightOneSpectrum O) :
    CharZero (P.adicCompletion L) :=
  charZero_of_injective_algebraMap
    (algebraMap L (P.adicCompletion L)).injective
end
end MazurProof.N13GlobalKummerAwayDifferentParity
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianSignature =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianSignature =====
section
/-!
# The signature of the N13 number field

The Gaussian unit embeds into the N13 cubic and still squares to `-1`.
Consequently there is no real embedding, so the sextic field is totally
complex.  The signature and Dirichlet unit rank then follow from the
structural degree computation.
-/
open Algebra Module
namespace MazurProof.N13GaussianSignature
noncomputable section
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
@[simp] theorem iL_mul_self :
    iL * iL = -1 := by
  rw [iL, ← map_mul,
    N13GaussianFractionField.iK_mul_self,
    map_neg, map_one]
/-- A real embedding would send `iL` to a real square root of `-1`. -/
theorem no_ringHom_to_real (φ : L →+* ℝ) : False := by
  have hsq : φ iL * φ iL = (-1 : ℝ) := by
    simpa only [map_mul, map_neg, map_one] using
      congrArg φ iL_mul_self
  nlinarith [sq_nonneg (φ iL)]
/-- Every infinite place of the N13 field is complex. -/
instance isTotallyComplexL :
    NumberField.IsTotallyComplex L where
  isComplex v := by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    exact no_ringHom_to_real
      (NumberField.InfinitePlace.embedding_of_isReal
        (K := L) hv)
@[simp] theorem nrComplexPlaces_eq_three :
    NumberField.InfinitePlace.nrComplexPlaces L = 3 := by
  have hsignature :
      Module.finrank ℚ L =
        2 * NumberField.InfinitePlace.nrComplexPlaces L :=
    NumberField.IsTotallyComplex.finrank L
  rw [N13GaussianNumberField.finrank_Q_L] at hsignature
  omega
end
end MazurProof.N13GaussianSignature
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
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L
abbrev O : Type :=
  NumberField.RingOfIntegers L
/-- The integral sextic generator in the Gaussian-cubic presentation. -/
def theta : L :=
  N13GaussianCubicField.alpha + 9
theorem alpha_root_h :
    eval₂ (algebraMap GI L)
      N13GaussianCubicField.alpha
      N13GaussianGlobalArithmetic.h = 0 := by
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  rw [hmap, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root N13GaussianCubicField.hK
theorem theta_root_g :
    eval₂ (algebraMap GI L) theta
      N13GaussianGlobalArithmetic.g = 0 := by
  have h := alpha_root_h
  rw [N13GaussianGlobalArithmetic.h,
    Polynomial.eval₂_comp] at h
  simpa only [theta, eval₂_add, eval₂_X,
    eval₂_ofNat, map_ofNat] using h
theorem theta_root_n13F :
    eval₂ (algebraMap GI L) theta
      N13GaussianGlobalArithmetic.n13F = 0 := by
  rw [← N13GaussianGlobalArithmetic.g_mul_conj,
    Polynomial.eval₂_mul, theta_root_g, zero_mul]
theorem theta_root_rat :
    eval₂ (algebraMap ℚ L) theta
      (N13SexticIrreducible.fInt.map
        (algebraMap ℤ ℚ)) = 0 := by
  rw [N13SexticIrreducible.fInt_map_rat]
  simpa [N13Mumford.f,
    N13GaussianGlobalArithmetic.n13F] using
    theta_root_n13F
theorem theta_root_fInt :
    eval₂ (algebraMap ℤ L) theta
      N13SexticIrreducible.fInt = 0 := by
  simpa only [eval₂_map,
    IsScalarTower.algebraMap_eq ℤ ℚ L] using
    theta_root_rat
theorem theta_integral :
    IsIntegral ℤ theta :=
  ⟨N13SexticIrreducible.fInt,
    N13SexticIrreducible.fInt_monic,
    theta_root_fInt⟩
/-- The sextic generator as an element of Mathlib's ring-of-integers wrapper. -/
def thetaO : O :=
  ⟨theta, theta_integral⟩
@[simp] theorem coe_thetaO :
    (thetaO : L) = theta :=
  rfl
@[simp] theorem aeval_thetaO_fInt :
    aeval thetaO N13SexticIrreducible.fInt = 0 := by
  apply NumberField.RingOfIntegers.ext
  change
    algebraMap O L
      (aeval thetaO N13SexticIrreducible.fInt) = 0
  rw [aeval_def, Polynomial.hom_eval₂]
  simpa only [coe_thetaO,
    IsScalarTower.algebraMap_eq ℤ O L] using
      theta_root_fInt
/-! ## Minkowski's bound -/
/-! ## Excluding small prime ideals -/
theorem quotient_card_eq_absNorm
    (P : Ideal O) [Fintype (O ⧸ P)] :
    Fintype.card (O ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_eq_fintype_card]
/-- A prime ideal of norm `q` would make the image of `thetaO` a root of
the N13 sextic in a field with `q` elements. -/
theorem no_prime_absNorm_eq_of_noRoot
    {q : ℕ}
    (hq0 : q ≠ 0)
    (hNoRoot : NoRootAtCard q)
    (P : Ideal O)
    (hP : P.IsPrime)
    (hP0 : P ≠ ⊥)
    (hN : Ideal.absNorm P = q) :
    False := by
  letI : P.IsMaximal := hP.isMaximal hP0
  letI : Field (O ⧸ P) := Ideal.Quotient.field P

  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [hN]
    exact hq0

  letI : Finite (O ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp hN0
  letI : Fintype (O ⧸ P) :=
    Fintype.ofFinite _

  have hcard : Fintype.card (O ⧸ P) = q := by
    rw [quotient_card_eq_absNorm, hN]

  let quot : O →+* (O ⧸ P) :=
    Ideal.Quotient.mk P
  let t : O ⧸ P :=
    quot thetaO

  have hcast :
      quot.comp (algebraMap ℤ O) =
        Int.castRingHom (O ⧸ P) := by
    ext z
    simp [quot]

  have ht :
      eval₂ (Int.castRingHom (O ⧸ P)) t
        N13SexticIrreducible.fInt = 0 := by
    calc
      eval₂ (Int.castRingHom (O ⧸ P)) t
            N13SexticIrreducible.fInt =
          quot
            (eval₂ (algebraMap ℤ O) thetaO
              N13SexticIrreducible.fInt) := by
        simpa only [t, hcast] using
          (Polynomial.hom_eval₂
            N13SexticIrreducible.fInt
            (algebraMap ℤ O) quot thetaO).symm
      _ = quot 0 := by
        rw [show
          eval₂ (algebraMap ℤ O) thetaO
              N13SexticIrreducible.fInt = 0 by
            simpa only [aeval_def] using
              aeval_thetaO_fInt]
      _ = 0 := map_zero quot

  exact (hNoRoot (k := O ⧸ P) hcard t) ht
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
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L
/-- The integral-closure presentation used by normalization is canonically
ring-equivalent to Mathlib's ring-of-integers presentation used by the
class-number proof.  The only apparent discrepancy is the chosen
`ℤ`-algebra instance; integer ring homomorphisms are unique. -/
def integralClosureEquivClassNumberOrder :
    O ≃+* N13GaussianClassNumberOne.O where
  toFun x :=
    ⟨x.1, isIntegralElem_int_of x.2⟩
  invFun x :=
    ⟨x.1, isIntegralElem_int_of x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' x y := Subtype.ext (show (x + y).1 = x.1 + y.1 from rfl)
  map_mul' x y := Subtype.ext (show (x * y).1 = x.1 * y.1 from rfl)
end
end MazurProof.N13GlobalKummerPID
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianDifferentSupport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianDifferentSupport =====
section
/-!
# Structural support of the N13 derivative

The two exceptional Gaussian factors are kept as literal algebraic
integers in the absolute maximal order:

* `A = 1 - i θ² - (1 + i) θ`,
* `Q = 2 - 3i`.

The Gaussian cubic relation gives the two short identities

`f'(θ) = 4 · i θ² (θ + 1) · A²`

and

`13 = (i - θ) · A³ · Q`.

All factors omitted from these displayed powers are exhibited as units.
Thus the different support and the ramification indices are read from
factorizations in the maximal order, rather than from a factor table or a
finite residue-field enumeration.
-/
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField
local instance numberFieldL : NumberField L :=
  N13GaussianNumberField.numberFieldL
local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L
local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O
local instance intAlgebraO : Algebra ℤ O :=
  Ring.toIntAlgebra O
/-- The explicit absolute integral basis, transported across the
carrier-preserving equivalence with Mathlib's ring-of-integers wrapper. -/
def classNumberOrderToOIntLinearEquiv :
    N13GaussianClassNumberOne.O ≃ₗ[ℤ] O :=
  N13GlobalKummerPID.integralClosureEquivClassNumberOrder.symm.toAddEquiv.toIntLinearEquiv
/-- The same carrier-preserving equivalence, now recording compatibility
with the unique integer algebra structures. -/
def OToClassNumberOrderAlgEquiv :
    O ≃ₐ[ℤ] N13GaussianClassNumberOne.O :=
  AlgEquiv.ofRingEquiv
    (f := N13GlobalKummerPID.integralClosureEquivClassNumberOrder)
    (fun z => by simp)
/-- The Gaussian unit in the absolute maximal order. -/
def integralI : O :=
  ⟨gaussianI, gaussianI_integral⟩
@[simp] theorem coe_integralI :
    ((integralI : O) : L) = gaussianI :=
  rfl
/-- The factor of `2` defining its unique Gaussian prime. -/
def primeTwoInteger : O :=
  1 - integralI
/-- The ramification-three factor above `13`. -/
def primeAInteger : O :=
  1 - integralI * integralTheta ^ 2 -
    (1 + integralI) * integralTheta
@[simp] theorem coe_primeTwoInteger :
    ((primeTwoInteger : O) : L) = 1 - gaussianI :=
  rfl
@[simp] theorem coe_primeAInteger :
    ((primeAInteger : O) : L) =
      1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta :=
  rfl
/-- The Gaussian prime whose cube ramifies in the chosen cubic factor. -/
def gaussianPiInteger : O :=
  3 - 2 * integralI
/-- The unit quotient `A³ / (3-2i)`. -/
def primeACubeCofactor : O :=
  integralTheta *
    (-integralI * integralTheta - 1 - 2 * integralI)
/-- Principal ideals of the three displayed carriers. -/
def primeTwoIdeal : Ideal O :=
  Ideal.span ({primeTwoInteger} : Set O)
def primeAIdeal : Ideal O :=
  Ideal.span ({primeAInteger} : Set O)
/-! ## Norms and the ramified prime -/
/-! ## The residue-degree-three prime

Primality of `Q` is not inferred from its composite norm.  Instead we
descend to the Gaussian prime `(2-3i)`.  The relative cubic is irreducible
there: in the thirteen-element residue field, Frobenius and a quadratic
Bézout identity exclude roots. -/
local instance dedekindRelativeO :
    IsDedekindDomain RelativeO :=
  integralClosure.isDedekindDomain GI K L
local instance torsionFreeGIL :
    Module.IsTorsionFree GI L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · left
      have hinj :
          Function.Injective (algebraMap GI L) := by
        rw [IsScalarTower.algebraMap_eq GI K L]
        exact
          (algebraMap K L).injective.comp
            (IsFractionRing.injective GI K)
      apply hinj
      simpa using hr
    · exact Or.inr hx
local instance torsionFreeRelativeO :
    Module.IsTorsionFree GI RelativeO :=
  Subalgebra.instIsTorsionFree (integralClosure GI L)
/-- Forget whether integrality was first recorded over `ℤ[i]` or directly
over `ℤ`.  Both subtypes have the same elements of the ambient field. -/
def relativeToORingEquiv :
    RelativeO ≃+* O where
  toFun x :=
    ⟨x.1, isIntegral_trans x.1 x.2⟩
  invFun x :=
    ⟨x.1, x.2.tower_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
/-! ## The unique prime above two -/
/-! ## Height-one carriers and support of the different -/
open IsDedekindDomain
/-! ## Square norm and the two remaining parity bits -/
end
end MazurProof.N13GaussianDifferentSupport
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
attribute [local instance] MazurProof.RamifiedDlog.dualNumberUnitsIsMulCommutative
theorem dlog_mul (z w : (DualNumber k)ˣ) :
    dlog (z * w) = dlog z + dlog w := by
  simp only [dlog, Units.val_mul, fst_mul, DualNumber.snd_mul]
  field_simp [fst_ne_zero z, fst_ne_zero w]
  ring
/-- The ramified logarithm as a homomorphism from multiplicative units to
the additive residue field. -/
def dlogHom : (DualNumber k)ˣ →* Multiplicative k where
  toFun z := Multiplicative.ofAdd (dlog z)
  map_one' := by simp
  map_mul' z w := by
    exact congrArg Multiplicative.ofAdd (dlog_mul z w)
@[simp] theorem dlogHom_apply (z : (DualNumber k)ˣ) :
    dlogHom z = Multiplicative.ofAdd (dlog z) := rfl
end
end MazurProof.RamifiedDlog
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
/-- The cubic generator inside the order. -/
def theta : Order :=
  AdjoinRoot.root cubicPolynomial
/-! ## The two nested power bases -/
/-! ## Direct reduction to the dual-number ring -/
/-! ## Exactness of the first-jet quotient -/
/-! ## Compatibility with the N13 descent generators -/
/-- The first fundamental unit in the integral Gaussian presentation. -/
def e1Order : Order :=
  1 - theta ^ 2 + (i - 1) * theta
/-- The second fundamental unit in the integral Gaussian presentation. -/
def e2Order : Order :=
  1 + i * theta ^ 2 + (1 + 2 * i) * theta
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
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraGI
abbrev O := NumberField.RingOfIntegers L
local instance intAlgebraRelativeO : Algebra ℤ RelativeO :=
  Ring.toIntAlgebra RelativeO
local instance intAlgebraAbsoluteO :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)
/-- Carrier-preserving identification of the relative integral closure
with Mathlib's absolute ring of integers. -/
def relativeToRingOfIntegers :
    RelativeO ≃+* O :=
  N13GaussianNumberField.relativeToAbsoluteAlgEquiv.toRingEquiv.trans
    N13GaussianNumberField.integralClosureToRingOfIntegersRingEquiv
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
/-- Bundled multiplicative form of Dirichlet's unique unit coordinates. -/
noncomputable def dirichletMulEquiv :
    torsion K ×
        Multiplicative (Fin (rank K) → ℤ) ≃*
      (NumberField.RingOfIntegers K)ˣ :=
  MulEquiv.ofBijective (dirichletCoordinatesHom K)
    ⟨dirichletCoordinatesHom_injective K,
      dirichletCoordinatesHom_surjective K⟩
end NumberField.Units
namespace MazurProof.N13GaussianUnitSquareclasses
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
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
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField
local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraGI
abbrev O := NumberField.RingOfIntegers L
local instance intAlgebraRelativeO : Algebra ℤ RelativeO :=
  Ring.toIntAlgebra RelativeO
local instance intAlgebraAbsoluteO :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)
/-! ## Literal units of the relative and absolute maximal orders -/
/-! ## The global first-jet logarithm -/
/-! ## Structural generation of all unit squareclasses -/
/-- Literal quotient of maximal-order units by the range of squaring. -/
abbrev UnitModSq :=
  Oˣ ⧸ (powMonoidHom 2 : Oˣ →* Oˣ).range
/-- The canonical squareclass map. -/
def unitClassHom : Oˣ →* UnitModSq :=
  QuotientGroup.mk'
    (powMonoidHom 2 : Oˣ →* Oˣ).range
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end

end

-- ===== FLT.Assumptions.MazurProof.N13CandidateCollapse =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CandidateCollapse =====
section
/-!
# Structural collapse of the N13 fake-descent candidates

The first ramified logarithm reduces the sixteen binary exponent vectors to
`(0,0,s,s)`.  The remaining nonzero vector represents
`e₂ * a * q`, which differs from the rational scalar `13` by a square.

This file joins those two facts without a sixteen-row table.  It does not
assert that every global fake-Selmer class belongs to the candidate
envelope, nor that every local image lies in the first-jet kernel; those are
the two remaining arithmetic semantic bridges.
-/
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
theorem survivor_isUnit : IsUnit survivor := by
  have hprod : IsUnit (survivor * squareFactor ^ 2) := by
    rw [survivor_mul_square]
    exact scalarThirteen_isUnit
  exact ((Commute.all survivor (squareFactor ^ 2)).isUnit_mul_iff.mp hprod).1
theorem squareFactor_isUnit : IsUnit squareFactor := by
  have hprod : IsUnit (survivor * squareFactor ^ 2) := by
    rw [survivor_mul_square]
    exact scalarThirteen_isUnit
  have hsq :
      IsUnit (squareFactor ^ 2) :=
    ((Commute.all survivor (squareFactor ^ 2)).isUnit_mul_iff.mp hprod).2
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hsq
theorem e2_isUnit : IsUnit e2 := by
  have h := survivor_isUnit
  rw [survivor] at h
  exact ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
    (by simpa [mul_assoc] using h)).1
theorem primeA_isUnit : IsUnit primeA := by
  have h := survivor_isUnit
  rw [survivor] at h
  have hrest :
      IsUnit (primeA * primeQ) :=
    ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all primeA primeQ).isUnit_mul_iff.mp hrest).1
theorem primeQ_isUnit : IsUnit primeQ := by
  have h := survivor_isUnit
  rw [survivor] at h
  have hrest :
      IsUnit (primeA * primeQ) :=
    ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all primeA primeQ).isUnit_mul_iff.mp hrest).2
theorem zeta_isUnit : IsUnit zeta := by
  have h := squareFactor_isUnit
  rw [squareFactor] at h
  exact ((Commute.all zeta (e1 * primeA)).isUnit_mul_iff.mp
    (by simpa [mul_assoc] using h)).1
theorem e1_isUnit : IsUnit e1 := by
  have h := squareFactor_isUnit
  rw [squareFactor] at h
  have hrest :
      IsUnit (e1 * primeA) :=
    ((Commute.all zeta (e1 * primeA)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all e1 primeA).isUnit_mul_iff.mp hrest).1
def primeAUnit : Lˣ := primeA_isUnit.unit
def primeQUnit : Lˣ := primeQ_isUnit.unit
end
end MazurProof.N13CandidateCollapse
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport =====
section
/-!
# Transport of the named N13 units

The unit squareclass computation is carried out in the maximal order of the
Gaussian cubic presentation, while the fake-descent candidates use the sextic
presentation.  This file gives the literal carrier-preserving map between the
two and proves that the three named units agree under it.

Consequently the structural maximal-order unit decomposition transports to the
same three units appearing in `N13CandidateCollapse`, without enumerating the
eight unit squareclasses.
-/
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldLg : Field Lg :=
  AdjoinRoot.instField
abbrev O := NumberField.RingOfIntegers Lg
/-- The maximal-order carrier embedded into its Gaussian cubic fraction
field.  It is written explicitly to avoid choosing between definitionally
different `Algebra O Lg` instances. -/
def orderToGaussian : O →+* Lg :=
  (Subalgebra.val
      (integralClosure N13GaussianGlobalArithmetic.GI Lg)).toRingHom.comp
    N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm.toRingHom
def orderUnitsToGaussian : Oˣ →* Lgˣ :=
  Units.map orderToGaussian.toMonoidHom
end
end MazurProof.N13GaussianNamedUnitTransport
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
abbrev On : Type := N13GaussianNamedUnitTransport.O
attribute [local instance] MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- The compiled equivalence between the normalization order and the
maximal-order presentation carrying the named-unit theorem. -/
abbrev normalizationOrderEquiv : Oi ≃+* On :=
  N13GlobalKummerPID.integralClosureEquivClassNumberOrder
end
end MazurProof.N13GaussianNormalizationOrderTransport
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
/-- Evaluation of an integral polynomial at the order generator. -/
def thetaEval (U : Z2[X]) : Order :=
  U.eval₂ (algebraMap Z2 Order) theta
end
end MazurProof.N13GaussianLowDegree
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
abbrev On := N13GaussianNamedUnitSquareclasses.O
local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact
@[reducible] local instance fieldLg :
    Field N13GaussianCubicField.L :=
  AdjoinRoot.instField
/-! ## The global integral evaluation in the explicit order -/
/-! ## The same named-unit word globally and locally -/
/-! ## Group-level capstone -/
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
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
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLs
local instance fieldLg : Field Lg :=
  N13GaussianCubicField.cubicField
end
end MazurProof.N13FullNormPairGaussian
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
attribute [local instance] MazurProof.N13IntegralFiberDetection.integralRationalAlgebra
local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization
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
attribute [local instance] MazurProof.N13SpecialProductLift.integralRationalAlgebra
local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
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
local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
attribute [local instance] MazurProof.N13IntegralGraphSpread.integralRationalAlgebra
end
end MazurProof.N13IntegralGraphSpread
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
/-- The six named cusps are exactly the three special base points times
the two sheets. -/
def cuspCoordinateEquiv : Cusp13 ≃ BasePoint × K where
  toFun := cuspCoordinate
  invFun := cuspOfCoordinate
  left_inv := cuspOfCoordinate_cuspCoordinate
  right_inv := cuspCoordinate_cuspOfCoordinate
end
end MazurProof.N13SpecialCuspReduction
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
theorem formalCurvePoly_degree :
    formalCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree formalCurvePoly_monic.ne_zero,
    formalCurvePoly_natDegree]
  norm_num
/-! ## Restriction of the actual affine coordinate ring -/
end
end MazurProof.N13FormalCurveOverlap
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
instance affineCurve_isDomain : IsDomain AffineCurve :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational
instance affineOverlap_isDomain : IsDomain AffineOverlap :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      affine_xClass_ne_zero)
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
theorem pointU_dvd_pointResidual (P : IntegralInfinityPoint) :
    pointU P ∣ pointResidual P := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointResidual P) (a := P.1.1)
  simpa [pointU, pointResidual_eval] using h
def pointW (P : IntegralInfinityPoint) : Base :=
  Classical.choose (pointU_dvd_pointResidual P)
theorem pointResidual_eq_mul_pointW (P : IntegralInfinityPoint) :
    pointResidual P = pointU P * pointW P :=
  Classical.choose_spec (pointU_dvd_pointResidual P)
def pointSemiGraph (P : IntegralInfinityPoint) :
    GeneralizedGraphIdealCore.SemiGraph
      N13IntegralInfinityChart.hBase
      N13IntegralInfinityChart.rhsBase where
  u := pointU P
  v := pointV P
  w := pointW P
  curve_eq := pointResidual_eq_mul_pointW P
/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/
def affineGraphData (P : IntegralInfinityPoint) :
    N13IntegralGraphJacobian.GraphData where
  u := affineU P
  v := affineV P
  w := affineW P
  curve_eq := affine_curve_eq P
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
/-- Weighted reflection turns the infinity semigraph equation into the
affine semigraph equation. -/
theorem affine_curve_eq
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3)
    (hw : D.w.natDegree ≤ 4) :
    affineV D ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV D -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
      affineU D * affineW D := by
  have hvv :
      (D.v ^ 2).reflect 6 =
        D.v.reflect 3 * D.v.reflect 3 := by
    simpa [pow_two] using
      (reflect_mul D.v D.v hv hv)
  have hhv :
      (N13IntegralInfinityChart.hBase * D.v).reflect 6 =
        N13IntegralInfinityChart.hBase.reflect 3 *
          D.v.reflect 3 := by
    simpa using
      (reflect_mul
        N13IntegralInfinityChart.hBase D.v
        hBase_natDegree_le hv)
  have huw :
      (D.u * D.w).reflect 6 =
        D.u.reflect 2 * D.w.reflect 4 := by
    simpa using
      (reflect_mul D.u D.w hu hw)
  calc
    affineV D ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV D -
          N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
        (D.v ^ 2).reflect 6 +
          (N13IntegralInfinityChart.hBase * D.v).reflect 6 -
          N13IntegralInfinityChart.rhsBase.reflect 6 := by
            rw [hvv, hhv, reflect_hBase, reflect_rhsBase]
            simp [affineV, pow_two]
    _ =
        (D.v ^ 2 +
            N13IntegralInfinityChart.hBase * D.v -
            N13IntegralInfinityChart.rhsBase).reflect 6 := by
          rw [reflect_sub, reflect_add]
    _ = (D.u * D.w).reflect 6 := by rw [D.curve_eq]
    _ = affineU D * affineW D := by
          rw [huw]
          rfl
def affineGraphData
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3)
    (hw : D.w.natDegree ≤ 4) :
    N13IntegralGraphJacobian.GraphData where
  u := affineU D
  v := affineV D
  w := affineW D
  curve_eq := affine_curve_eq D hu hv hw
end
end MazurProof.N13IntegralInfinityGraphTwoChart
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
attribute [local instance] MazurProof.N13IntegralInfinityGraphSaturation.integralRationalAlgebra
local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      N13IntegralModelContraction.RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization
end
end MazurProof.N13IntegralInfinityGraphSaturation
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
attribute [local instance] MazurProof.N13PrimitiveAffineComparison.instAlgebraAR
local instance instIsLocalizationIntegralRingVerticalScalarsR : IsLocalization N13IntegralModelContraction.verticalScalars R :=
  N13IntegralModelContraction.rationalRing_isLocalization
end
end MazurProof.N13PrimitiveAffineComparison
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
theorem conjugate_root :
    curvePoly.eval₂ xClassHom (-xClass hPoly - yClass) = 0 := by
  simp only [curvePoly, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, xClassHom_apply]
  linear_combination yClass_relation
def conjugate : R →+* R := AdjoinRoot.lift xClassHom (-xClass hPoly - yClass) conjugate_root
open N13SpecialComparisonFactorPair hiding xClass R
end
end MazurProof.N13SpecialAffineNorm
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
attribute [local instance] MazurProof.N13KernelGraphContraction.instAlgebraAR
local instance instIsLocalizationIntegralRingVerticalScalarsR : IsLocalization N13IntegralModelContraction.verticalScalars R :=
  N13IntegralModelContraction.rationalRing_isLocalization
end
end MazurProof.N13KernelGraphContraction
end

end


