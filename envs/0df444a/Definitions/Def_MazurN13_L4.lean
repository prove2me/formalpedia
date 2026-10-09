-- Prove2me | Definitions.Def_MazurN13_L4
-- name    : MazurN13_L4
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-09T07:05:49.005716+00:00
-- url     : https://prove2.me/theorems/17d4b5cf-d73a-482d-8593-8ae5ef411943
-- title:
--   Mazur order 13 (Huang FLT port): definitions, layer 4
-- statement:
--   Layer 4 of 12 of the definitions used by a machine-checked Lean proof of the case $N=13$ of Mazur's torsion theorem (no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$). It collects the definitions, structures, instances and small structural lemmas of Xiang Huang's development whose dependencies are available at this layer; larger lemmas they rely on are separate platform theorems, imported here as already-proved results. Layer $k$ imports layer $k-1$.
--
--   Port notes: only API-drift fixes (transparency options, renamed lemmas); local notations expanded and `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof

import Mathlib
import Definitions.Def_MazurN13_L3
import Theorems.Thm_MazurProof_N13CanonicalContractionQuotient_genericQuotientMap_comp_algebraMap
import Theorems.Thm_MazurProof_N13FormalInfinityChart_recompose
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianDifferentSupport_relativeToORingEquiv_gaussianTwo
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianI_sq
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_gaussian_cubic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
import Theorems.Thm_MazurProof_N13GaussianNamedUnitSquareclasses_relativeZeta_sq
import Theorems.Thm_MazurProof_N13GaussianNamedUnitTransport_orderToGaussian_apply
import Theorems.Thm_MazurProof_N13GaussianOrderTwo_i_sq
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_hPoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13IntegralAffinePointSpread_sexticSemi_v
import Theorems.Thm_MazurProof_N13IntegralFractionalHull_functionField_isFractionRing
import Theorems.Thm_MazurProof_N13LowDegreeKummerHom_lowFakeClass_add_of_class_add
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_curveFactor_bezout
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_scaled_pade_graph
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_isDouble_of_finiteIdealSquareRoot
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_mumfordIdeal_pade_half
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_mumfordIdeal_sq_eq_square_generator
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_balanceInfinity_class
import Theorems.Thm_MazurProof_N13MumfordKummerRelation_mumfordFakeClass_add_of_class_add
import Theorems.Thm_MazurProof_N13SpecialAffineNorm_conjugate_linear
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisorCharts_yClass_relation
import Theorems.Thm_MazurProof_PadeZeroConstantSquare_exists_monic_square_root_of_relation
import Theorems.Thm_MazurProof_SexticMumford_IntegralOrientedRep_exists_semiMumford
import Theorems.Thm_MazurProof_SexticMumford_IntegralOrientedRep_primitivePartUnit_mul_contentUnit
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_nonZeroDivisors_le_comap
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRingDomain
attribute [local instance] MazurProof.N13IntegralFractionalHull.rationalRingLocalization
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  functionField_isFractionRing
/-- Extension of fractional ideals from the integral model to its generic
affine coordinate ring. -/
def extendFractional :
    IntegralFractionalIdeal →+* RationalFractionalIdeal :=
  FractionalIdeal.extendedHom'
    FunctionField nonZeroDivisors_le_comap
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
attribute [local instance] MazurProof.N13IntegralGraphContraction.integralRingDomain
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
end
end MazurProof.N13IntegralGraphContraction
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
/-- Removing content is an exact principal equivalence in the oriented
quotient, not merely an equality of unoriented ideal classes. -/
theorem primitivePartRep_picClass
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).picClass M O =
      R.picClass M O := by
  change
    QuotientGroup.mk' (principalOriented M O).range
        ((R.primitivePartRep M O).raw M) =
      QuotientGroup.mk' (principalOriented M O).range (R.raw M)
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨principalOriented M O (R.contentUnit M),
    MonoidHom.mem_range.mpr ⟨R.contentUnit M, rfl⟩, ?_⟩
  apply Prod.ext
  · exact primitivePartUnit_mul_contentUnit M R
  · change
      Multiplicative.ofAdd
          (R.atInfinity -
            Multiplicative.toAdd
              (O.ordPlus (R.contentUnit M))) *
        O.ordPlus (R.contentUnit M) =
      Multiplicative.ofAdd R.atInfinity
    change
      R.atInfinity -
          Multiplicative.toAdd
            (O.ordPlus (R.contentUnit M)) +
        Multiplicative.toAdd
          (O.ordPlus (R.contentUnit M)) =
      R.atInfinity
    omega
end IntegralOrientedRep
/-- Every oriented Picard class has a primitive integral representative.
This closes the missing bridge between denominator clearing and Mumford
graph extraction. -/
theorem exists_primitiveIntegralRepresentative
    (O : InfinityOrder M) (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M,
      IdealIsPrimitive M R.ideal ∧ R.picClass M O = c := by
  obtain ⟨R, hR⟩ := exists_integralRepresentative M O c
  refine ⟨R.primitivePartRep M O,
    R.primitivePartRep_isPrimitive M O, ?_⟩
  exact (R.primitivePartRep_picClass M O).trans hR
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
/-- Every oriented class has a semi-Mumford representative before any
degree reduction. -/
theorem exists_semiMumfordRepresentative
    (c : ConcretePic M O) :
    ∃ D : SemiMumford M, semiMumfordClass M O D = c := by
  obtain ⟨R, hprimitive, hR⟩ :=
    exists_primitiveIntegralRepresentative M O c
  obtain ⟨D, hD, -⟩ :=
    R.exists_semiMumford M O hprimitive
  exact ⟨D, hD.trans hR⟩
/-! ## A canonical affine-degree step -/
/-- Phase I of the structural reduction: every oriented class has a
representative of affine degree at most two.  No claim about the independent
`nInf` balance is made here. -/
theorem exists_lowDegreeSemiRepresentative
    (c : ConcretePic M O) :
    ∃ D : LowDegreeSemi M,
      semiMumfordClass M O D.toSemi = c := by
  obtain ⟨D, hD⟩ := exists_semiMumfordRepresentative M O c
  exact ⟨reduceDegree M O D, (reduceDegree_class M O D).trans hD⟩
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
/-! ## Exact orders of the principal Cantor corrections -/
/-! ## The two class-preserving balancing steps -/
/-! ## A well-founded measure for the two balance walls -/
/-! ## Structural infinity balancing -/
theorem classOf_surjective :
    Function.Surjective
      (classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)) := by
  intro c
  obtain ⟨E, hE⟩ :=
    exists_lowDegreeSemiRepresentative
      (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) c
  refine ⟨balanceInfinity E, ?_⟩
  rw [← semiMumfordClass_toSemi]
  exact (balanceInfinity_class E).trans hE
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
theorem existsUnique_classOf
    (c : ConcretePic (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K)) :
    ∃! D : Mumford (N13Mumford.model K),
      classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D = c := by
  obtain ⟨D, hD⟩ :=
    N13MumfordInfinityBalance.classOf_surjective c
  refine ⟨D, hD, ?_⟩
  intro E hE
  exact classOf_injective K (hE.trans hD.symm)
instance instNormalFormData :
    NormalFormData (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) where
  existsUnique := existsUnique_classOf K
end
end MazurProof.N13SmallMumfordRigidity
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
attribute [local instance] MazurProof.N13GenericQuotientLocalization.rationalRingLocalization
/-- The generic quotient map as a two-adic algebra homomorphism. -/
def genericQuotientAlgHom (J : Ideal RationalRing) :
    (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) →ₐ[R₂]
      (RationalRing ⧸ J) where
  toRingHom :=
    N13CanonicalContractionQuotient.genericQuotientMap J
  commutes' r :=
    DFunLike.congr_fun
      (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap J)
      r
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
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRingDomain
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13VerticalGraphJacobian.integralRingDomain
attribute [local instance] MazurProof.N13VerticalGraphJacobian.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13FiniteContractIdealInvertible.integralRingDomain
attribute [local instance] MazurProof.N13FiniteContractIdealInvertible.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
end
end MazurProof.N13FiniteContractIdealInvertible
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
attribute [local instance] MazurProof.N13GaussianCubicField.instFactIrreduciblePolynomialKHK
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
attribute [local instance] MazurProof.N13GaussianCubicField.finiteKL
attribute [local instance] MazurProof.N13GaussianCubicField.separableKL
/-- Relative trace discriminant of the shifted power basis. -/
theorem powerBasis_discr :
    Algebra.discr K powerBasis.basis =
      algebraMap GI K (pi ^ 2) := by
  exact
    PowerBasisDiscriminant.powerBasis_discr_eq_map_discr
      powerBasis alpha_integral h minpoly_alpha
      |>.trans (congrArg (algebraMap GI K) h_discr)
/-! ## The relative integral basis -/
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL
/-! ## Discriminant of the relative integral basis -/
attribute [local instance] MazurProof.N13GaussianCubicField.integralClosureLocalization
theorem relativeFieldBasis_discr :
    Algebra.discr K relativeFieldBasis =
      algebraMap GI K (pi ^ 2) := by
  calc
    Algebra.discr K relativeFieldBasis =
        Algebra.discr K powerBasis.basis := by
      simpa [relativeFieldBasis] using
        (Algebra.discr_reindex K powerBasis.basis
          (finCongr powerBasis_dim))
    _ = algebraMap GI K (pi ^ 2) :=
      powerBasis_discr
end
end MazurProof.N13GaussianCubicField
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
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLs
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteKL
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteQL
def sexticToGaussian : Ls →ₐ[ℚ] Lg :=
  AdjoinRoot.liftAlgHom
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic
theorem gaussianTheta_mul_inverse :
    gaussianTheta *
        (gaussianTheta ^ 2 +
          (2 - 2 * gaussianI) * gaussianTheta +
          (-1 - 2 * gaussianI)) = 1 := by
  linear_combination gaussianTheta_gaussian_cubic
theorem gaussianTheta_add_one_mul_inverse :
    (gaussianTheta + 1) *
        (-(gaussianTheta ^ 2 +
          (1 - 2 * gaussianI) * gaussianTheta - 2)) = 1 := by
  linear_combination -gaussianTheta_gaussian_cubic
/-! ## Integrality of the structural generators -/
end
end MazurProof.N13GaussianFieldEquiv
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
/-- Phase I of structural reduction is already surjective onto the
oriented Picard group. -/
theorem lowClass_surjective :
    Function.Surjective lowClass := by
  intro P
  obtain ⟨D, hD⟩ :=
    exists_lowDegreeSemiRepresentative M O P
  exact ⟨D, hD⟩
/-- A chosen low-degree semirepresentative of an oriented Picard class. -/
def representative (P : G) : LowRep :=
  Function.surjInv lowClass_surjective P
@[simp] theorem lowClass_representative (P : G) :
    lowClass (representative P) = P :=
  Function.surjInv_eq lowClass_surjective P
/-- The N13 fake-Kummer homomorphism constructed without an infinity
balancing theorem. -/
def mumfordKummer : G →+ Target where
  toFun P := lowFakeClass (representative P)
  map_zero' := by
    have h :=
      lowFakeClass_eq_of_class_eq
        (representative 0) zeroLow
        (by rw [lowClass_representative, lowClass_zero])
    simpa using h
  map_add' P Q := by
    apply lowFakeClass_add_of_class_add
      (representative P) (representative Q)
        (representative (P + Q))
    rw [lowClass_representative, lowClass_representative,
      lowClass_representative]
@[simp] theorem mumfordKummer_apply (P : G) :
    mumfordKummer P = lowFakeClass (representative P) :=
  rfl
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
/-- The genuine full norm pair attached to a low-degree Mumford
representative. -/
def mumfordNormPair (D : LowRep) :
    N13FullNormPair.NormPair :=
  ⟨(N13MumfordKummerValue.uThetaUnit
      (N13LowDegreeKummerHom.asMumford D),
    normRootUnit D), by
    apply Units.ext
    exact norm_uTheta_eq_normRoot_sq D⟩
@[simp] theorem mumfordNormPair_fst (D : LowRep) :
    EvenSexticNormPair.fstHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      N13MumfordKummerValue.uThetaUnit
        (N13LowDegreeKummerHom.asMumford D) :=
  rfl
@[simp] theorem mumfordNormPair_snd (D : LowRep) :
    EvenSexticNormPair.sndHom N13FullNormPair.normUnits
        (mumfordNormPair D) =
      normRootUnit D :=
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
attribute [local instance] MazurProof.N13GlobalKummerNormalization.fieldL
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizationMonoid
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
/-- The primitive integral representative of a rational polynomial,
well-defined up to sign. -/
def primitiveNormalization (p : ℚ[X]) : ℤ[X] :=
  (integralNormalization p).primPart
theorem primitiveNormalization_natDegree_le
    {p : ℚ[X]} (hdeg : p.natDegree ≤ 2) :
    (primitiveNormalization p).natDegree ≤ 2 := by
  rw [primitiveNormalization,
    Polynomial.natDegree_primPart]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_contra hcoeff
  have hnU :
      n ∈ (integralNormalization p).support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hnp :
      n ∈ p.support :=
    IsLocalization.integerNormalization_support
      (nonZeroDivisors ℤ) p hnU
  have hnle :
      n ≤ 2 :=
    (Polynomial.le_natDegree_of_mem_supp n hnp).trans
      hdeg
  omega
theorem primitiveNormalization_isPrimitive
    (p : ℚ[X]) :
    (primitiveNormalization p).IsPrimitive :=
  (integralNormalization p).isPrimitive_primPart
/-- The global integral representative of a low-degree Kummer value. -/
def normalizedKummerInteger
    (D : N13LowDegreeKummerHom.LowRep) :
    integralClosure ℤ L :=
  integralEval
    (primitiveNormalization D.toSemi.u)
theorem normalizedKummerInteger_degree
    (D : N13LowDegreeKummerHom.LowRep) :
    (primitiveNormalization D.toSemi.u).natDegree ≤ 2 :=
  primitiveNormalization_natDegree_le D.degree_le_two
end
end MazurProof.N13GlobalKummerNormalization
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
attribute [local instance] MazurProof.N13GlobalKummerIdealSquare.fieldL
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Integral homogeneous Mumford data whose first polynomial is exactly the
primitive normalization used by `normalizedKummerInteger`. -/
structure ScaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) where
  scale : ℤ
  scale_ne_zero : scale ≠ 0
  v : ℤ[X]
  w : ℤ[X]
  curve :
    C (scale ^ 2) * N13SexticIrreducible.fInt -
        v ^ 2 =
      primitiveNormalization D.toSemi.u * w
theorem differentInteger_ne_zero :
    integralEval
      N13SexticIrreducible.fInt.derivative ≠ 0 := by
  have hrootQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ) = 0 := by
    simpa [N13SexticSquareclass.f] using
      gaussianTheta_root_sextic
  have hderivQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative ≠ 0 :=
    (N13Mumford.f_separable ℚ).eval₂_derivative_ne_zero
      (algebraMap ℚ L) hrootQ
  intro hzero
  apply hderivQ
  have hcoe :
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative = 0 := by
    calc
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
          N13SexticIrreducible.fInt.derivative =
        ((integralEval
          N13SexticIrreducible.fInt.derivative : O) :
            N13GlobalKummerNormalization.L) :=
              (coe_integralEval _).symm
      _ = ((0 : O) :
          N13GlobalKummerNormalization.L) := by rw [hzero]
      _ = 0 := by rfl
  have hmaps :
      (algebraMap ℚ L).comp (algebraMap ℤ ℚ) =
        algebraMap ℤ
          N13GlobalKummerNormalization.L :=
    RingHom.ext_int _ _
  calc
    eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)).derivative := by
            rw [N13SexticIrreducible.fInt_map_rat]
    _ =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.derivative.map
          (algebraMap ℤ ℚ)) := by
            rw [derivative_map]
    _ =
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative := by
            rw [eval₂_map, hmaps]
    _ = 0 := hcoe
/-! ## The principal-ideal endpoint -/
end
end MazurProof.N13GlobalKummerIdealSquare
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
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fieldL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroCompletion
/-- The local primitive quadratic attached to a low-degree representative. -/
def localU
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P
    (primitiveNormalization D.toSemi.u)
end
end MazurProof.N13GlobalKummerSimpleRootParity
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
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.numberFieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fractionRingOL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.intAlgebraO
@[simp] theorem integralI_sq :
    integralI ^ 2 = (-1 : O) := by
  apply Subtype.ext
  exact gaussianI_sq
/-- The Gaussian unit, now as an actual unit of the maximal order. -/
def integralIUnit : Oˣ where
  val := integralI
  inv := -integralI
  val_inv := by
    rw [mul_neg, ← pow_two, integralI_sq]
    simp
  inv_val := by
    rw [neg_mul, ← pow_two, integralI_sq]
    simp
/-- The sextic generator is an integral unit. -/
def integralThetaUnit : Oˣ where
  val := integralTheta
  inv :=
    integralTheta ^ 2 +
      (2 - 2 * integralI) * integralTheta +
      (-1 - 2 * integralI)
  val_inv := by
    apply Subtype.ext
    exact gaussianTheta_mul_inverse
  inv_val := by
    rw [mul_comm]
    apply Subtype.ext
    exact gaussianTheta_mul_inverse
/-- The neighboring integral element `θ + 1` is also a unit. -/
def integralThetaAddOneUnit : Oˣ where
  val := integralTheta + 1
  inv :=
    -(integralTheta ^ 2 +
      (1 - 2 * integralI) * integralTheta - 2)
  val_inv := by
    apply Subtype.ext
    exact gaussianTheta_add_one_mul_inverse
  inv_val := by
    rw [mul_comm]
    apply Subtype.ext
    exact gaussianTheta_add_one_mul_inverse
/-- The unit multiplying `A²` in the derivative. -/
def differentUnit : Oˣ :=
  integralIUnit * integralThetaUnit ^ 2 *
    integralThetaAddOneUnit
theorem primeACubeCofactor_mul_inverse :
    primeACubeCofactor * (integralI * integralTheta + 1) = 1 := by
  apply Subtype.ext
  change
    (gaussianTheta *
        (-gaussianI * gaussianTheta - 1 - 2 * gaussianI)) *
      (gaussianI * gaussianTheta + 1) = 1
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  linear_combination
    gaussianTheta_gaussian_cubic +
      (-gaussianTheta ^ 3 - 2 * gaussianTheta ^ 2) * hi
/-- The quotient `A³ / (3-2i)` is a genuine integral unit. -/
def primeACubeCofactorUnit : Oˣ where
  val := primeACubeCofactor
  inv := integralI * integralTheta + 1
  val_inv := primeACubeCofactor_mul_inverse
  inv_val := by
    rw [mul_comm]
    exact primeACubeCofactor_mul_inverse
/-! ## Norms and the ramified prime -/
/-! ## The residue-degree-three prime

Primality of `Q` is not inferred from its composite norm.  Instead we
descend to the Gaussian prime `(2-3i)`.  The relative cubic is irreducible
there: in the thirteen-element residue field, Frobenius and a quadratic
Bézout identity exclude roots. -/
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeGIL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO
/-! ## The unique prime above two -/
theorem relativeGaussianTwoIdeal_map_eq :
    relativeGaussianTwoIdeal.map relativeToORingEquiv =
      primeTwoIdeal := by
  rw [relativeGaussianTwoIdeal_eq_span,
    primeTwoIdeal, Ideal.map_span, Set.image_singleton,
    relativeToORingEquiv_gaussianTwo]
/-! ## Height-one carriers and support of the different -/
open IsDedekindDomain
/-! ## Square norm and the two remaining parity bits -/
end
end MazurProof.N13GaussianDifferentSupport
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
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraAbsoluteO
def giToOrder : GI →+* Order :=
  Zsqrtd.lift
    ⟨N13GaussianOrderTwo.i, by
      calc
        N13GaussianOrderTwo.i *
            N13GaussianOrderTwo.i =
          (-1 : Order) := by
            simpa only [pow_two] using
              N13GaussianOrderTwo.i_sq
        _ = ((-1 : ℤ) : Order) := by norm_num⟩
local instance giAlgebraOrder : Algebra GI Order :=
  giToOrder.toAlgebra
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
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraAbsoluteO
/-! ## Literal units of the relative and absolute maximal orders -/
def relativeZetaUnit : RelativeOˣ where
  val := relativeZeta
  inv := -relativeZeta
  val_inv := by
    rw [mul_neg, ← pow_two, relativeZeta_sq]
    simp
  inv_val := by
    rw [neg_mul, ← pow_two, relativeZeta_sq]
    simp
def zetaUnit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeZetaUnit
/-! ## The global first-jet logarithm -/
/-! ## Structural generation of all unit squareclasses -/
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
def zetaUnit : Lˣ := zeta_isUnit.unit
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
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The explicit maximal-order embedding is injective. -/
theorem orderToGaussian_injective :
    Function.Injective orderToGaussian := by
  intro x y hxy
  apply NumberField.RingOfIntegers.ext
  simpa only [orderToGaussian_apply] using hxy
end
end MazurProof.N13GaussianNamedUnitTransport
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
/-! ## The unconditional structural Kummer map -/
abbrev actualKummer : G →+ Target :=
  N13LowDegreeKummerHom.mumfordKummer
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
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.fieldLg
/-- The globally primitive integral Mumford polynomial, base-changed to
`ℤ₂`. -/
def globalPrimitiveZ2 (D : LowRep) : Z2[X] :=
  (N13GlobalKummerNormalization.primitiveNormalization D.toSemi.u).map
    (algebraMap ℤ Z2)
theorem globalPrimitiveZ2_natDegree_le (D : LowRep) :
    (globalPrimitiveZ2 D).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (N13GlobalKummerNormalization.normalizedKummerInteger_degree D)
/-- Global primitivity prevents all coefficients from vanishing modulo two
after base change to `ℤ₂`. -/
theorem residuePolynomial_globalPrimitiveZ2_ne_zero (D : LowRep) :
    residuePolynomial (globalPrimitiveZ2 D) ≠ 0 := by
  let U : ℤ[X] :=
    N13GlobalKummerNormalization.primitiveNormalization D.toSemi.u
  intro hzero
  have hle :
      (globalPrimitiveZ2 D).contentIdeal ≤
        RingHom.ker PadicInt.toZMod := by
    rw [Polynomial.contentIdeal_def, Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    change
      PadicInt.toZMod ((globalPrimitiveZ2 D).coeff n) = 0
    have hcoeff :=
      congrArg (fun q : (ZMod 2)[X] => q.coeff n) hzero
    simpa [residuePolynomial] using hcoeff
  have hprimitive : U.IsPrimitive :=
    N13GlobalKummerNormalization.primitiveNormalization_isPrimitive
      D.toSemi.u
  have htopU : U.contentIdeal = ⊤ :=
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top U).mp hprimitive
  have htop :
      (globalPrimitiveZ2 D).contentIdeal = ⊤ := by
    rw [globalPrimitiveZ2,
      Polynomial.contentIdeal_map_eq_map_contentIdeal, htopU,
      Ideal.map_top]
  rw [htop, PadicInt.ker_toZMod] at hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal Z2).ne_top
      (top_unique hle)
/-- The exact first jet of the globally primitive polynomial. -/
def globalPrimitiveJet (D : LowRep) : JetUnit :=
  lowDegreeJet
    (globalPrimitiveZ2 D)
    (residuePolynomial_globalPrimitiveZ2_ne_zero D)
    (Polynomial.natDegree_map_le.trans
      (globalPrimitiveZ2_natDegree_le D))
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
/-- A chosen balanced representative of each oriented Picard class. -/
def representative
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    N13Mumford.Mumford ℚ :=
  Function.surjInv hrep P
@[simp] theorem classOf_representative
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    classOf M O (representative hrep P) = P :=
  Function.surjInv_eq hrep P
/-- The fake-Kummer homomorphism obtained from any surjective balanced
Mumford representation. -/
def mumfordKummer
    (hrep : Function.Surjective (classOf M O)) :
    G →+ Target where
  toFun P :=
    N13MumfordKummerValue.mumfordFakeClass
      (representative hrep P)
  map_zero' := by
    have h :=
      N13MumfordKummerRelation.mumfordFakeClass_eq_of_classOf_eq
        O (representative hrep 0) (SexticMumford.zero M)
        (by rw [classOf_representative, classOf_zero])
    simpa using h
  map_add' P Q := by
    apply
      N13MumfordKummerRelation.mumfordFakeClass_add_of_class_add
        O (representative hrep P) (representative hrep Q)
          (representative hrep (P + Q))
    rw [classOf_representative, classOf_representative,
      classOf_representative]
@[simp] theorem mumfordKummer_apply
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    mumfordKummer hrep P =
      N13MumfordKummerValue.mumfordFakeClass
        (representative hrep P) :=
  rfl
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
/-- The full norm pair with the infinity orientation retained. -/
def orientedMumfordNormPair (D : LowRep) :
    N13FullNormPair.NormPair :=
  ⟨(N13MumfordKummerValue.uThetaUnit
      (N13LowDegreeKummerHom.asMumford D),
    orientationSignUnit D *
      N13MumfordKummerNorm.normRootUnit D), by
    change
      N13FullNormPair.normUnits
          (N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D)) =
        (orientationSignUnit D *
          N13MumfordKummerNorm.normRootUnit D) ^ 2
    rw [mul_pow, orientationSignUnit_sq, one_mul]
    exact (N13MumfordKummerNorm.mumfordNormPair D).property⟩
@[simp] theorem orientedMumfordNormPair_fst (D : LowRep) :
    EvenSexticNormPair.fstHom N13FullNormPair.normUnits
        (orientedMumfordNormPair D) =
      N13MumfordKummerValue.uThetaUnit
        (N13LowDegreeKummerHom.asMumford D) :=
  rfl
@[simp] theorem orientedMumfordNormPair_snd (D : LowRep) :
    EvenSexticNormPair.sndHom N13FullNormPair.normUnits
        (orientedMumfordNormPair D) =
      orientationSignUnit D *
        N13MumfordKummerNorm.normRootUnit D :=
  rfl
/-- The corresponding class in the full even-sextic descent target. -/
def orientedMumfordFullClass (D : LowRep) :
    N13FullNormPair.FullTarget :=
  QuotientGroup.mk'
    (EvenSexticNormPair.fullGauge
      N13FullNormPair.normUnits
      N13FullNormPair.scalarUnits
      N13FullNormPair.normUnits_scalarUnits)
    (orientedMumfordNormPair D)
/-! ## The two oriented base classes -/
/-! ## The full lift of the actual structural Kummer map -/
/-- Use exactly the same chosen low-degree representative as the existing
fake Kummer homomorphism, but retain its oriented norm root.  No
well-definedness or additivity assertion is hidden in this definition. -/
def orientedFullKummer (P : G) :
    N13FullNormPair.FullTarget :=
  orientedMumfordFullClass
    (N13LowDegreeKummerHom.representative P)
/-- Forgetting the norm root is definitionally the actual structural fake
Kummer map. -/
theorem ofMul_forget_orientedFullKummer (P : G) :
    Additive.ofMul
        (N13FullNormPair.forget
          (orientedFullKummer P)) =
      N13LowDegreeKummerHom.mumfordKummer P := by
  rfl
/-- The fake kernel has only the two full norm-pair fibres: the identity
and the distinguished sign class.  This is unconditional target algebra;
the geometric principal-genus theorem must identify the two fibres with
the double and infinity-shifted-double branches. -/
theorem structuralKummer_eq_zero_iff_full_eq_one_or_sign
    (P : G) :
    N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
      orientedFullKummer P = 1 ∨
        orientedFullKummer P =
          N13FullNormPair.signClass := by
  rw [← ofMul_forget_orientedFullKummer]
  change
    N13FullNormPair.forget (orientedFullKummer P) = 1 ↔
      orientedFullKummer P = 1 ∨
        orientedFullKummer P =
          N13FullNormPair.signClass
  exact N13FullNormPair.forget_eq_one_iff
    (orientedFullKummer P)
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
/-! ## Unfolding the full-gauge fibre -/
/-! ## The canonical polynomial square-root witness -/
/-- The degree-bounded polynomial representative of a full-gauge square
root in the sextic branch algebra. -/
def branchSquarePolynomial (β : Lˣ) : ℚ[X] :=
  AdjoinRoot.modByMonicHom
    sextic_f_monic (β : L)
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-! ## Closing the finite ideal square -/
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- The full nondegenerate Padé graph retained before passage to the
fractional-ideal quotient.  Besides the exact square root, this records the
scaled graph polynomial and its literal compatibility with the original
Mumford representative. -/
structure FinitePadeGraphRootData
    (D : LowRep) (a : ℚ[X]) where
  L₀ : ℚ[X]
  κ : ℚˣ
  curve_eq :
    N13Mumford.f ℚ - L₀ ^ 2 =
      a ^ 2 * (Polynomial.C (κ : ℚ) * D.toSemi.u)
  graph_eq :
    D.toSemi.u ∣ L₀ - D.toSemi.v
  rootData :
    PadeIdealRootData M D.toSemi a L₀
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- A uniform finite square root together with a literal graph-ideal
presentation.  `inverseOrientation = false` means that `idealRoot` itself is
the graph ideal; `true` means that its inverse is the graph ideal. -/
structure FiniteIdealGraphRootData (D : LowRep) where
  idealRoot : InvFrac M
  principalCorrection : (FunctionField M)ˣ
  square_eq :
    mumfordIdealUnit M D.toSemi *
        toPrincipalIdeal
          (CoordinateRing M) (FunctionField M)
          principalCorrection =
      idealRoot ^ 2
  graphU : ℚ[X]
  graphV : ℚ[X]
  graphU_ne_zero : graphU ≠ 0
  graphU_degree_le_two : graphU.natDegree ≤ 2
  graph_curve_dvd :
    graphU ∣ N13Mumford.f ℚ - graphV ^ 2
  inverseOrientation : Bool
  graph_eq :
    (((if inverseOrientation then idealRoot⁻¹ else idealRoot) :
        InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        (mumfordIdeal M graphU graphV :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
namespace FinitePadeGraphRootData
/-- Forget the extra Padé equations while retaining the exact graph ideal
which presents the chosen root. -/
def toFiniteIdealGraphRootData
    {D : LowRep} {a : ℚ[X]}
    (R : FinitePadeGraphRootData D a)
    (ha : a ≠ 0)
    (hdegree : a.natDegree ≤ 2) :
    FiniteIdealGraphRootData D where
  idealRoot := R.rootData.root
  principalCorrection :=
    (ySubFunctionUnit M R.L₀)⁻¹
  square_eq := R.rootData.square_eq
  graphU := a
  graphV := R.L₀
  graphU_ne_zero := ha
  graphU_degree_le_two := hdegree
  graph_curve_dvd := by
    refine
      ⟨a *
        (Polynomial.C (R.κ : ℚ) * D.toSemi.u), ?_⟩
    rw [R.curve_eq]
    ring
  inverseOrientation := true
  graph_eq := by
    simpa using R.rootData.inverseRoot_coe
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-- Construct the exact nondegenerate Padé graph together with the
fractional-ideal root whose inverse is that graph ideal. -/
def finitePadeGraphRootData
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X])
    (c b : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hb : b ≠ 0)
    (hbSq : b ^ 2 = c / (q : ℚ))
    (hgraph :
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v)
    (hc : c ≠ 0)
    (ha : a ≠ 0) :
    FinitePadeGraphRootData D a := by
  let hscaled :=
    exists_scaled_pade_graph
      D q a l c b hrelation hb hbSq hgraph hc
  let L₀ := Classical.choose hscaled
  let hκ := Classical.choose_spec hscaled
  let κ := Classical.choose hκ
  have hscaled_spec := Classical.choose_spec hκ
  have hcurve := hscaled_spec.1
  have hgraphScaled := hscaled_spec.2
  have hideal :
      mumfordIdeal M a L₀ ^ 2 *
          mumfordIdeal M D.toSemi.u D.toSemi.v =
        Ideal.span
          ({ySubClass M L₀} :
            Set (CoordinateRing M)) :=
    mumfordIdeal_pade_half
      M a D.toSemi.u D.toSemi.v L₀ κ
        hcurve hgraphScaled ha
  exact
    { L₀ := L₀
      κ := κ
      curve_eq := hcurve
      graph_eq := hgraphScaled
      rootData :=
        padeIdealRootData M D.toSemi a L₀ hideal }
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
def finiteIdealGraphRootData_of_zero_pade_scalar
    (D : LowRep) (q : ℚˣ)
    (a l : ℚ[X])
    (ha : a ≠ 0)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 =
        a ^ 2 * D.toSemi.u) :
    FiniteIdealGraphRootData D := by
  have hl : l ≠ 0 := by
    intro hl
    have hzero :
        a ^ 2 * D.toSemi.u = 0 := by
      rw [← hrelation, hl]
      simp
    exact
      (mul_ne_zero (pow_ne_zero 2 ha)
        D.toSemi.u_monic.ne_zero) hzero
  have hq :
      IsUnit (Polynomial.C (q : ℚ)) :=
    Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (Units.ne_zero q))
  let hbExists :=
    PadeZeroConstantSquare.exists_monic_square_root_of_relation
      hq hl D.toSemi.u_monic D.degree_le_two hrelation
  let b := Classical.choose hbExists
  have hbSpec := Classical.choose_spec hbExists
  have hbMonic := hbSpec.1
  have hub := hbSpec.2.2
  have hbDegree : b.natDegree ≤ 2 :=
    hbSpec.2.1.trans (by norm_num)
  let hwExists := D.toSemi.curve_dvd
  let w := Classical.choose hwExists
  have hw := Classical.choose_spec hwExists
  have hcurve :
      M.f - D.toSemi.v ^ 2 =
        b * (b * w) := by
    calc
      M.f - D.toSemi.v ^ 2 =
          D.toSemi.u * w := hw
      _ = b * (b * w) := by
        rw [hub]
        ring
  have hbezout :
      ∃ A B E : ℚ[X],
        A * b + B * (2 * D.toSemi.v) +
            E * (b * w) = 1 :=
    curveFactor_bezout
      M b (b * w) D.toSemi.v
        hbMonic.ne_zero hcurve
  have hideal :
      mumfordIdeal M b D.toSemi.v ^ 2 =
        mumfordIdeal M D.toSemi.u D.toSemi.v := by
    have hsquare :=
      mumfordIdeal_sq_eq_square_generator
        M b (b * w) D.toSemi.v
          hcurve ⟨w, rfl⟩ hbezout
    rw [← hub] at hsquare
    exact hsquare
  let J₀ :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M) :=
    (mumfordIdeal M b D.toSemi.v :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M))
  have hfrac :
      J₀ ^ 2 =
        ((mumfordIdealUnit M D.toSemi :
          InvFrac M) :
            FractionalIdeal
              (CoordinateRing M)⁰
              (FunctionField M)) := by
    dsimp only [J₀]
    simp only [coe_mumfordIdealUnit]
    rw [pow_two, ← FractionalIdeal.coeIdeal_mul,
      ← pow_two, hideal]
  let hroot :=
    SquareRootUnitLift.exists_unit_val_eq_and_sq_eq
      J₀ (mumfordIdealUnit M D.toSemi) hfrac
  let J := Classical.choose hroot
  have hJ := Classical.choose_spec hroot
  exact
    { idealRoot := J
      principalCorrection := 1
      square_eq := by
        simpa only [map_one, mul_one] using hJ.2.symm
      graphU := b
      graphV := D.toSemi.v
      graphU_ne_zero := hbMonic.ne_zero
      graphU_degree_le_two := hbDegree
      graph_curve_dvd := ⟨b * w, hcurve⟩
      inverseOrientation := false
      graph_eq := by
        change
          (J :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) =
            J₀
        exact hJ.1 }
/-- A constant monic Mumford polynomial is `1`, so its finite ideal is
already trivial. -/
def finiteIdealGraphRootData_of_natDegree_zero
    (D : LowRep)
    (hu0 : D.toSemi.u.natDegree = 0) :
    FiniteIdealGraphRootData D := by
  have huOne : D.toSemi.u = 1 :=
    D.toSemi.u_monic.natDegree_eq_zero.mp hu0
  have hvZero : D.toSemi.v = 0 := by
    have hred := D.toSemi.v_reduced
    have hmod :
        D.toSemi.v % (1 : ℚ[X]) = 0 :=
      EuclideanDomain.mod_one D.toSemi.v
    rw [huOne, hmod] at hred
    exact hred.symm
  have hunit :
      mumfordIdealUnit M D.toSemi = 1 := by
    apply Units.ext
    change
      (mumfordIdeal M D.toSemi.u D.toSemi.v :
        FractionalIdeal
          (CoordinateRing M)⁰ (FunctionField M)) = 1
    rw [huOne, hvZero,
      show mumfordIdeal M 1 0 = ⊤ from
        zero_mumfordIdeal M]
    rfl
  exact
    { idealRoot := 1
      principalCorrection := 1
      square_eq := by
        rw [hunit]
        simp
      graphU := 1
      graphV := 0
      graphU_ne_zero := one_ne_zero
      graphU_degree_le_two := by simp
      graph_curve_dvd := one_dvd _
      inverseOrientation := false
      graph_eq := by
        change
          ((⊤ : Ideal (CoordinateRing M)) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) =
            (mumfordIdeal M 1 0 :
              FractionalIdeal
                (CoordinateRing M)⁰ (FunctionField M))
        exact congrArg
          (fun I : Ideal (CoordinateRing M) ↦
            (I :
              FractionalIdeal
                (CoordinateRing M)⁰ (FunctionField M)))
          (zero_mumfordIdeal M).symm }
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Constructive generic output retained from one finite fractional-ideal
square root.  It records the exact root and principal correction together
with its literal graph presentation and the half selected by the existing
quotient proof.  No two-adic integrality assertion is included. -/
structure FiniteIdealHalfData (D : LowRep)
    extends FiniteIdealGraphRootData D where
  half : G
  half_spec :
    N13LowDegreeKummerHom.lowClass D = 2 • half
/-- Retain the graph-presented square root when selecting the half furnished by
`isDouble_of_finiteIdealSquareRoot`. -/
def finiteIdealHalfData
    (D : LowRep)
    (R : FiniteIdealGraphRootData D) :
    FiniteIdealHalfData D := by
  let hhalf :=
    isDouble_of_finiteIdealSquareRoot D
      ⟨R.idealRoot, R.principalCorrection, R.square_eq⟩
  exact
    { toFiniteIdealGraphRootData := R
      half := Classical.choose hhalf
      half_spec := Classical.choose_spec hhalf }
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
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- The generic Padé square root and the exact half selected by the current
Kummer proof, retained instead of immediately erasing them behind
surjectivity.  This still makes no claim that the generic ideal root extends
to a normalized two-adic graph lattice. -/
structure ConstructedHalfData (P : G) where
  representative : N13LowDegreeKummerHom.LowRep
  representative_spec :
    N13LowDegreeKummerHom.lowClass representative = P
  finite :
    N13MumfordFullKummerIdentityFiber.FiniteIdealHalfData representative
  double_eq :
    P = 2 • finite.half
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBaseChange =====
section
/-!
# Coefficient extension for balanced Mumford representatives

This is the model-independent coefficient extension for the balanced Mumford
data of a monic sextic.  The only curve-specific datum is the compatibility
of the two sextic equations under the coefficient map.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- Map a balanced Mumford representative along an injective coefficient map
which carries the source sextic equation to the target sextic equation. -/
def Mumford.mapCoeffs (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) : Mumford M' where
  u := D.u.map ι
  v := D.v.map ι
  nInf := D.nInf
  u_monic := D.u_monic.map ι
  deg_u := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.deg_u
  v_reduced := by
    rw [← Polynomial.map_mod ι, D.v_reduced]
  curve_dvd := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    refine ⟨q.map ι, ?_⟩
    calc
      M'.f - (D.v.map ι) ^ 2 = (M.f - D.v ^ 2).map ι := by
        simp [hM]
      _ = (D.u * q).map ι := by rw [hq]
      _ = D.u.map ι * q.map ι := by simp
  infinity_bound := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.infinity_bound
@[simp] theorem mapCoeffs_u
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).u = D.u.map ι := rfl
@[simp] theorem mapCoeffs_v
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).v = D.v.map ι := rfl
@[simp] theorem mapCoeffs_nInf
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).nInf = D.nInf := rfl
theorem Mumford.mapCoeffs_injective
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    Function.Injective (Mumford.mapCoeffs ι hι hM) := by
  intro D E hDE
  have huMap := congrArg Mumford.u hDE
  have hvMap := congrArg Mumford.v hDE
  have hn := congrArg Mumford.nInf hDE
  have hu : D.u = E.u :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_u] using huMap)
  have hv : D.v = E.v :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_v] using hvMap)
  have hn' : D.nInf = E.nInf := by
    simpa only [mapCoeffs_nInf] using hn
  cases D
  cases E
  simp_all
end
end MazurProof.SexticMumford
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
/-- The induced map between the two fraction fields. -/
def functionMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    FunctionField M →+* FunctionField M' :=
  IsLocalization.map
    (M := (CoordinateRing M)⁰) (S := FunctionField M)
    (T := (CoordinateRing M')⁰) (FunctionField M')
    (coordinateMap ι hM) (nonZeroDivisors_le_comap ι hι hM)
/-- Extension of fractional ideals along the affine coordinate-ring map. -/
def fractionalMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) →+*
      FractionalIdeal (CoordinateRing M')⁰ (FunctionField M') :=
  FractionalIdeal.extendedHom' (FunctionField M')
    (nonZeroDivisors_le_comap ι hι hM)
/-- Extension of invertible fractional ideals. -/
def invFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    InvFrac M →* InvFrac M' :=
  Units.map (fractionalMap ι hι hM).toMonoidHom
@[simp] theorem coe_invFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (I : InvFrac M) :
    ((invFracMap ι hι hM I : InvFrac M') :
        FractionalIdeal
          (CoordinateRing M')⁰ (FunctionField M')) =
      fractionalMap ι hι hM
        (I :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) :=
  rfl
/-- Extension of nonzero rational functions. -/
def functionUnitMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    (FunctionField M)ˣ →* (FunctionField M')ˣ :=
  Units.map (functionMap ι hι hM).toMonoidHom
/-- Compatibility required of the two chosen orders at infinity. -/
def InfinityCompatible
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M') : Prop :=
  ∀ α : (FunctionField M)ˣ,
    O'.ordPlus (functionUnitMap ι hι hM α) = O.ordPlus α
/-- Base change on the product of an invertible fractional ideal and its
integer infinity coordinate. -/
def orientedFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    OrientedFrac M →* OrientedFrac M' :=
  MonoidHom.prodMap (invFracMap ι hι hM)
    (MonoidHom.id (Multiplicative ℤ))
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
attribute [local instance] MazurProof.N13IntegralFiberDetection.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralFiberDetection.integralRingDomain
attribute [local instance] MazurProof.N13IntegralFiberDetection.rationalRingLocalization
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13SpecialProductLift.integralRingDomain
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13IntegralGraphSpread.integralRingDomain
attribute [local instance] MazurProof.N13IntegralGraphSpread.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
/-- Reduction of the six rational cusps identifies them bijectively with
all points of the good characteristic-two curve. -/
def specialCuspEquiv : Cusp13 ≃ SpecialCurvePoint :=
  cuspCoordinateEquiv.trans curvePointEquiv.symm
@[simp] theorem curvePointEquiv_specialCuspEquiv
    (c : Cusp13) :
    curvePointEquiv (specialCuspEquiv c) =
      cuspCoordinate c := by
  simp [specialCuspEquiv, cuspCoordinateEquiv]
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
/-- A fixed special point used to place degree-one Abel classes in the
degree-two set model.  Its choice is immaterial when comparing two points
with the same reduction. -/
def specialAnchor : SpecialCurvePoint :=
  N13SpecialCuspReduction.specialCuspEquiv .infinityPlus
/-- The set-valued special Abel class of a curve point, represented by
adjoining one fixed anchor point. -/
def specialPointClass (P : SpecialCurvePoint) : SpecialSet :=
  N13AbelFiberTwoModel.abel (s(P, specialAnchor))
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Proper curve reduction together with its compatibility with the exact
Picard classifier and with the six named rational cusps. -/
structure CompatibleReduction where
  classifier : N13ReductionClassifier.Data G SpecialSet
  reduceCurve : RationalCurvePoint → SpecialCurvePoint
  classify_abel :
    ∀ P : RationalCurvePoint,
      classifier.classify (rationalAbel P) =
        specialPointClass (reduceCurve P)
  reduce_cusp :
    ∀ c : Cusp13,
      reduceCurve (N13Mumford.cuspPoint c) =
        N13SpecialCuspReduction.specialCuspEquiv c
namespace CompatibleReduction
variable (D : CompatibleReduction)
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
def reduceCurve : RationalCurvePoint → SpecialCurvePoint
  | .infinityPlus =>
      N13SpecialCuspReduction.specialCuspEquiv .infinityPlus
  | .infinityMinus =>
      N13SpecialCuspReduction.specialCuspEquiv .infinityMinus
  | .affine X Y hcurve =>
      reduceAffine X Y (by
        rw [N13CurveModel.C13SexticEq,
          ← N13Mumford.f_eval_eq_sexticF13]
        exact hcurve)
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
/-- The transported integral linear graph is exactly the sextic Mumford
graph of the corresponding two-adic curve point. -/
theorem sexticSemiIdeal_eq_pointIdeal (P : IntegralPoint) :
    N13IntegralGraphContraction.sexticSemiIdeal
        (integralSemiGraph P) 0 =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model (curvePoint P)).u
        (SexticMumford.pointMumford Model (curvePoint P)).v := by
  unfold N13IntegralGraphContraction.sexticSemiIdeal
  rw [sexticSemi_u, sexticSemi_v]
  rfl
/-- The generic fibre of the literal integral affine point ideal is the
standard sextic point graph. -/
theorem map_pointIdeal (P : IntegralPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model (curvePoint P)).u
        (SexticMumford.pointMumford Model (curvePoint P)).v := by
  rw [pointIdeal,
    N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemiOfSemi]
  exact sexticSemiIdeal_eq_pointIdeal P
/-! ## The integral branch of the selected degree-one Padé graph -/
end
end MazurProof.N13IntegralAffinePointSpread
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
/-! ## The two-chart Laurent obstruction -/
open LaurentPolynomial
open scoped LaurentPolynomial
/-- An overlap function is written in the basis `1,v`.  The curve equation
is irrelevant for this additive Čech calculation. -/
abbrev Overlap : Type :=
  Laurent × Laurent
/-- The two Laurent coefficients not supplied by either affine chart. -/
def obstruction :
    Overlap →ₗ[K] Obstruction where
  toFun z := ![AddMonoidAlgebra.coeff z.2 (-2), AddMonoidAlgebra.coeff z.2 (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul]
  map_smul' c z := by
    funext i
    fin_cases i <;> simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul]
@[simp] theorem obstruction_apply_zero (z : Overlap) :
    obstruction z 0 = AddMonoidAlgebra.coeff z.2 (-2) := rfl
@[simp] theorem obstruction_apply_one (z : Overlap) :
    obstruction z 1 = AddMonoidAlgebra.coeff z.2 (-1) := rfl
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
abbrev Overlap : Type :=
  N13CechLaurentSeriesCore.Overlap (R := R₂)
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
/-- Multiplication in the formal curve algebra

`v² + (1+t²+t³)v = t+t²`

written in the basis `1,v`. -/
def mulOverlap
    {R : Type*} [CommRing R]
    (z w : N13CechLaurentSeriesCore.Overlap (R := R)) :
    N13CechLaurentSeriesCore.Overlap (R := R) :=
  (z.1 * w.1 + z.2 * w.2 * rhsInfinity,
    z.1 * w.2 + z.2 * w.1 -
      z.2 * w.2 * hInfinity)
@[simp] theorem oneOverlap_mul
    {R : Type*} [CommRing R]
    (z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap oneOverlap z = z := by
  apply Prod.ext <;>
    simp [mulOverlap, oneOverlap]
/-- Left multiplication by a fixed formal function is linear. -/
def leftMul
    {R : Type*} [CommRing R]
    (g : N13CechLaurentSeriesCore.Overlap (R := R)) :
    N13CechLaurentSeriesCore.Overlap (R := R) →ₗ[R]
      N13CechLaurentSeriesCore.Overlap (R := R) where
  toFun z := mulOverlap g z
  map_add' z w := by
    apply Prod.ext <;>
      simp [mulOverlap]
    <;> ring_nf
  map_smul' c z := by
    apply Prod.ext
    · change
        g.1 * (c • z.1) +
            g.2 * (c • z.2) * rhsInfinity =
          c • (g.1 * z.1 + g.2 * z.2 * rhsInfinity)
      simp only [← HahnSeries.single_zero_mul_eq_smul]
      ring
    · change
        g.1 * (c • z.2) + g.2 * (c • z.1) -
            g.2 * (c • z.2) * hInfinity =
          c •
            (g.1 * z.2 + g.2 * z.1 -
              g.2 * z.2 * hInfinity)
      simp only [← HahnSeries.single_zero_mul_eq_smul]
      ring
set_option maxHeartbeats 4000000 in
/-- An invertible formal transition function whose special fibre is the
identity transition. -/
structure NearIdentityTransition where
  transition : Overlap₂
  inverse : Overlap₂
  mul_inverse :
    mulOverlap transition inverse =
      oneOverlap
  inverse_mul :
    mulOverlap inverse transition =
      oneOverlap
  reduce_transition :
    reduceOverlap transition =
      oneOverlap
namespace NearIdentityTransition
variable (g : NearIdentityTransition)
/-- The untwisted formal line bundle. -/
def identity : NearIdentityTransition where
  transition := oneOverlap
  inverse := oneOverlap
  mul_inverse := oneOverlap_mul _
  inverse_mul := oneOverlap_mul _
  reduce_transition := reduceOverlap_one
/-- The transition displacement from the identity. -/
def deviation : Overlap₂ :=
  g.transition - oneOverlap
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
abbrev Overlap : Type :=
  N13FormalLineBundleCech.Overlap₂
/-- Read an actual formal-curve function in the basis `1,v`. -/
def toOverlap :
    FormalCurve →ₗ[Laurent] Overlap where
  toFun z := (coeff0 z, coeffV z)
  map_add' z w := by
    ext <;> simp [coeff0, coeffV, normalPoly]
  map_smul' c z := by
    ext <;> simp [coeff0, coeffV, normalPoly]
/-- Build an actual formal-curve function from its two coefficients. -/
def ofOverlap :
    Overlap →ₗ[Laurent] FormalCurve where
  toFun z :=
    algebraMap Laurent FormalCurve z.1 +
      algebraMap Laurent FormalCurve z.2 * vClass
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' c z := by
    change
      algebraMap Laurent FormalCurve (c * z.1) +
          algebraMap Laurent FormalCurve (c * z.2) * vClass =
        c •
          (algebraMap Laurent FormalCurve z.1 +
            algebraMap Laurent FormalCurve z.2 * vClass)
    simp only [map_mul, Algebra.smul_def]
    ring
/-- The normal-form coordinates of a pair are the original pair. -/
theorem toOverlap_ofOverlap
    (z : Overlap) :
    toOverlap (ofOverlap z) = z := by
  apply Prod.ext
  · change
      ((C z.1 + C z.2 * X) %ₘ formalCurvePoly).coeff 0 = z.1
    rw [(modByMonic_eq_self_iff formalCurvePoly_monic).mpr]
    · simp
    · rw [formalCurvePoly_degree]
      compute_degree <;> norm_num
  · change
      ((C z.1 + C z.2 * X) %ₘ formalCurvePoly).coeff 1 = z.2
    rw [(modByMonic_eq_self_iff formalCurvePoly_monic).mpr]
    · simp
    · rw [formalCurvePoly_degree]
      compute_degree <;> norm_num
theorem ofOverlap_injective :
    Function.Injective ofOverlap := by
  intro z w hzw
  calc
    z = toOverlap (ofOverlap z) :=
      (toOverlap_ofOverlap z).symm
    _ = toOverlap (ofOverlap w) := by rw [hzw]
    _ = w := toOverlap_ofOverlap w
/-! ## Restriction of the actual affine coordinate ring -/
end
end MazurProof.N13FormalCurveOverlap
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
/-- The ordinary infinity chart is finite free of rank two over
`ℤ₂[t]`; its power basis is `1,v`. -/
def powerBasis : PowerBasis Base InfinityCurve :=
  AdjoinRoot.powerBasis' infinityCurvePoly_monic
noncomputable instance infinityCurveModuleFree :
    Module.Free Base InfinityCurve :=
  Module.Free.of_basis powerBasis.basis
noncomputable instance infinityCurveModuleFinite :
    Module.Finite Base InfinityCurve :=
  powerBasis.finite
end
end MazurProof.N13IntegralInfinityChart
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
/-- The degree-less-than-two representative on the ordinary chart. -/
def integralNormalPoly :
    IntegralRing →ₗ[IntegralBase] IntegralBase[X] :=
  AdjoinRoot.modByMonicHom
    N13IntegralInfinityChart.infinityCurvePoly_monic
/-- Coefficients in the ordinary basis `1,v`. -/
def integralCoeff0 : IntegralRing →ₗ[IntegralBase] IntegralBase :=
  (Polynomial.lcoeff IntegralBase 0).comp integralNormalPoly
def integralCoeffV : IntegralRing →ₗ[IntegralBase] IntegralBase :=
  (Polynomial.lcoeff IntegralBase 1).comp integralNormalPoly
/-- The degree-less-than-two representative on the special chart. -/
def specialNormalPoly :
    SpecialRing →ₗ[SpecialBase] SpecialBase[X] :=
  AdjoinRoot.modByMonicHom
    N13SpecialInfinityChart.curvePoly_monic
/-- Coefficients in the special basis `1,v`. -/
def specialCoeff0 : SpecialRing →ₗ[SpecialBase] SpecialBase :=
  (Polynomial.lcoeff SpecialBase 0).comp specialNormalPoly
def specialCoeffV : SpecialRing →ₗ[SpecialBase] SpecialBase :=
  (Polynomial.lcoeff SpecialBase 1).comp specialNormalPoly
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
/-- The nonzero elements of `A` remain nonzero after localization in `B`. -/
def nonZeroDivisors_le_comap :
    A⁰ ≤ B⁰.comap (algebraMap A B) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (algebraMap A B)
      (IsLocalization.injective B
        (submonoid_le_nonZeroDivisors (A := A) (B := B) M))
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Extension of fractional ideals to the principal localization. -/
def extendFractional :
    FractionalIdeal A⁰ K →+* FractionalIdeal B⁰ K :=
  FractionalIdeal.extendedHom'
    K (nonZeroDivisors_le_comap (A := A) (B := B) M)
end
end MazurProof.N13LocalizationIdealPatch
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
attribute [local instance] MazurProof.N13TwoChartLineTensor.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
/-! ## The two rational points at infinity -/
end
end MazurProof.N13TwoChartLineTensor
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
/-- The residue field of the special curve. -/
abbrev K : Type :=
  N13GoodModelTwo.F2
/-- Finite points on the special affine chart. -/
abbrev AffinePoint : Type :=
  N13GoodModelTwo.AffinePoint K
/-- Points on the divisor at infinity. -/
abbrev InfinityPoint : Type :=
  N13GoodModelTwo.InfinityPoint K
/-- Points on the completed special curve. -/
abbrev CurvePoint : Type :=
  N13SymmetricSquareTwo.CurvePoint
/-- Effective divisors of degree two on the completed special curve. -/
abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo
/-- The point ideal of a finite special point on the ordinary affine chart. -/
def affinePointIdeal (P : AffinePoint) : Ideal SpecialAffine :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    (X - C P.1.1)
    (C P.1.2)
/-- The point ideal with coordinates `(t,v)` on the special infinity chart. -/
def infinityPointIdeal (t v : K) : Ideal SpecialInfinity :=
  Ideal.span
    {N13SpecialInfinityChart.tClass -
        algebraMap K[X] SpecialInfinity (C t),
      N13SpecialInfinityChart.vClass -
        algebraMap K[X] SpecialInfinity (C v)}
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
/-- Literal degree-two effective divisors on the completed special curve. -/
abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo
attribute [local instance] MazurProof.N13TwoChartPicardRealization.integralRationalAlgebra
/-- The common function field is the fraction field of the integral affine
coordinate ring. -/
local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
namespace Data
end Data
end
end MazurProof.N13TwoChartPicardRealization
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
/-- The infinity ideal contributed by an unordered pair of graph roots. -/
def rootInfinityIdeal
    (D : SemiMumford) :
    Sym2 K → Ideal N13SpecialDivisorCharts.SpecialInfinity :=
  Sym2.lift
    ⟨fun a b =>
        (if a = 0 then ⊤ else
          N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval a)) *
        (if b = 0 then ⊤ else
          N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval b)),
      fun a b => by
        dsimp
        rw [mul_comm]⟩
@[simp] theorem rootInfinityIdeal_mk
    (D : SemiMumford) (a b : K) :
    rootInfinityIdeal D s(a, b) =
      (if a = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval a)) *
      (if b = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval b)) :=
  rfl
end
end MazurProof.N13SpecialGraphDivisorCharts
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialVerticalDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialVerticalDivisorCharts =====
section
/-!
# Chart ideals of vertical special N13 divisors

The finite canonical fibre above `x = a` consists of the two points
`(a,0)` and `(a,1)`.  Their affine point ideals multiply to the principal
horizontal ideal `(X-a)`: the two graph factors are hyperelliptic conjugates.

This file also computes the infinity-chart ideal.  The fibre above `a = 0`
is absent from the overlap and has unit infinity ideal.  The fibre above
`a = 1` meets the infinity chart at `t = 1`, where the two ordinate ideals
again multiply to the principal ideal `(t-1)`.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
open N13GoodCoordinateRingTwo
/-- The two affine sheets above a special horizontal coordinate. -/
def verticalPoint (a y : K) :
    N13SpecialDivisorCharts.CurvePoint :=
  N13AbelFiberTwoModel.curvePointEquiv.symm
    (Sum.inl a, y)
/-- The canonical divisor above a constant infinity coordinate `t = a`.
At `a = 0` this is the base fibre at infinity; at `a = 1` it is the finite
fibre above `x = 1`. -/
def constantInfinityFibreDivisor
    (a : K) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  if a = 0 then
    N13AbelFiberTwoModel.canonicalDivisor (Sum.inr ())
  else
    N13AbelFiberTwoModel.canonicalDivisor (Sum.inl 1)
end
end MazurProof.N13SpecialVerticalDivisorCharts
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
/-- Substitute an infinity-coordinate polynomial into the special curve
while retaining `v` as the polynomial variable. -/
def verticalCurve (s : K[X]) : K[X] :=
  X ^ 2 +
    N13SpecialInfinityChart.hPoly.comp s * X -
    N13SpecialInfinityChart.rhsPoly.comp s
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialQuadraticGraphRegularity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialQuadraticGraphRegularity =====
section
/-!
# Automatic regularity of quadratic special N13 graphs

The coefficient `h=1+X²+X³` of the special affine curve is an irreducible
cubic over `F₂`.  It is therefore coprime to every monic quadratic.  This
supplies the Bézout field required by the special Mumford API for any monic
quadratic semigraph, without an additional smoothness hypothesis.

Consequently every integral monic quadratic semigraph reduces directly to
the special graph data whose canonical root divisor has the same affine
ideal.
-/
open Polynomial
namespace MazurProof.N13SpecialQuadraticGraphRegularity
noncomputable section
attribute [local instance] MazurProof.N13SpecialQuadraticGraphRegularity.instFactPrimeOfNatNat_fLT
/-- The cubic coefficient of the special affine curve is irreducible over
`F₂`: it has no root in `F₂`. -/
theorem hPoly_irreducible :
    Irreducible N13GoodCoordinateRingTwo.hPoly := by
  apply
    (N13GoodCoordinateRingTwo.hPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [N13GoodCoordinateRingTwo.hPoly_natDegree]; norm_num)
        (by rw [N13GoodCoordinateRingTwo.hPoly_natDegree])).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro a ha
  have hroot :
      N13GoodCoordinateRingTwo.hPoly.eval a = 0 :=
    (Polynomial.mem_roots
      N13GoodCoordinateRingTwo.hPoly_monic.ne_zero).mp ha
  have hone :
      N13GoodCoordinateRingTwo.hPoly.eval a = 1 := by
    simp only [N13GoodCoordinateRingTwo.hPoly,
      eval_add, eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  rw [hone] at hroot
  exact one_ne_zero hroot
/-- Every monic quadratic over the special field is coprime to the cubic
curve coefficient. -/
theorem quadratic_isCoprime_hPoly
    (u : N13GoodCoordinateRingTwo.K[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    IsCoprime u N13GoodCoordinateRingTwo.hPoly := by
  apply IsCoprime.symm
  apply (hPoly_irreducible.isCoprime_or_dvd u).resolve_right
  intro hdvd
  have hle :=
    Polynomial.natDegree_le_of_dvd hdvd hu.ne_zero
  rw [N13GoodCoordinateRingTwo.hPoly_natDegree, hdeg] at hle
  omega
/-- A monic quadratic special semigraph automatically satisfies the
Mumford Bézout regularity condition. -/
theorem quadratic_graph_bezout
    (u v w : N13GoodCoordinateRingTwo.K[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    ∃ a b c : N13GoodCoordinateRingTwo.K[X],
      a * u +
          b * (2 * v + N13GoodCoordinateRingTwo.hPoly) +
          c * w =
        1 := by
  obtain ⟨a, b, hab⟩ :=
    quadratic_isCoprime_hPoly u hu hdeg
  refine ⟨a, b, 0, ?_⟩
  have htwo :
      (2 : N13GoodCoordinateRingTwo.K[X]) = 0 :=
    CharP.cast_eq_zero N13GoodCoordinateRingTwo.K[X] 2
  rw [htwo, zero_mul, zero_add, zero_mul, add_zero]
  exact hab
/-- Coefficientwise reduction turns an integral monic quadratic semigraph
into regular special Mumford data. -/
def reduceSemiMumford
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := N13GeneralizedMumfordReduction.reducePoly D.u
  v := N13GeneralizedMumfordReduction.reducePoly D.v
  w := N13GeneralizedMumfordReduction.reducePoly D.w
  u_monic :=
    D.u_monic.map N13GeneralizedMumfordReduction.reduceBase
  curve_eq := by
    have h :=
      congrArg N13GeneralizedMumfordReduction.reducePoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      N13GeneralizedMumfordReduction.reduce_hPoly,
      N13GeneralizedMumfordReduction.reduce_rhsPoly] using h
  bezout :=
    quadratic_graph_bezout
      (N13GeneralizedMumfordReduction.reducePoly D.u)
      (N13GeneralizedMumfordReduction.reducePoly D.v)
      (N13GeneralizedMumfordReduction.reducePoly D.w)
      (D.u_monic.map N13GeneralizedMumfordReduction.reduceBase)
      (by
        rw [N13GeneralizedMumfordReduction.reducePoly_apply,
          D.u_monic.natDegree_map, hdeg])
end
end MazurProof.N13SpecialQuadraticGraphRegularity
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
/-- Substitute a polynomial for `x` in the affine curve equation while
retaining `y` as the polynomial variable. -/
def verticalCurve (s : K[X]) : K[X] :=
  X ^ 2 +
    N13GoodCoordinateRingTwo.hPoly.comp s * X -
    N13GoodCoordinateRingTwo.rhsPoly.comp s
end
end MazurProof.N13SpecialAffineVerticalGraph
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
/-- Substitute a linear expression for `t` in the infinity curve, leaving
`v` as the polynomial variable. -/
def verticalCurve (s : R₂[X]) : R₂[X] :=
  X ^ 2 +
    N13IntegralInfinityChart.hBase.comp s * X -
    N13IntegralInfinityChart.rhsBase.comp s
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Integral vertical graph data `m(v)=0`, `t=a+cv`. -/
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
def ideal (E : VerticalGraph) : Ideal InfinityCurve :=
  Ideal.span
    ({aeval N13IntegralInfinityGraphJacobian.yClass E.m,
      N13IntegralInfinityChart.tClass -
        aeval N13IntegralInfinityGraphJacobian.yClass E.s} :
      Set InfinityCurve)
end VerticalGraph
open N13IntegralInfinityGraphJacobian
def L (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.s
def U (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.m
def G (E : VerticalGraph) : InfinityCurve :=
  N13IntegralInfinityChart.tClass - L E
def W (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.w
/-- Divided-difference cofactor for
`F(t,v) - F(L,v) = (t-L) Gbar`. -/
def Gbar (E : VerticalGraph) : InfinityCurve :=
  yClass *
      (N13IntegralInfinityChart.tClass ^ 2 +
        N13IntegralInfinityChart.tClass * L E +
        L E ^ 2) +
    (yClass - 1) *
      (N13IntegralInfinityChart.tClass + L E) -
    1
def GbarT (E : VerticalGraph) : InfinityCurve :=
  yClass *
      (2 * N13IntegralInfinityChart.tClass + L E) +
    (yClass - 1)
def GbarV (E : VerticalGraph) : InfinityCurve :=
  N13IntegralInfinityChart.tClass ^ 2 +
      N13IntegralInfinityChart.tClass * L E +
      L E ^ 2 +
      (N13IntegralInfinityChart.tClass + L E) +
    algebraMap R₂ InfinityCurve E.c *
      (yClass *
          (N13IntegralInfinityChart.tClass + 2 * L E) +
        (yClass - 1))
def Uv (E : VerticalGraph) : InfinityCurve :=
  aeval yClass (derivative E.m)
def Wv (E : VerticalGraph) : InfinityCurve :=
  aeval yClass (derivative E.w)
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
abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph
/-- The weight-six affine transform of the vertical equation `m(v)`. -/
def affineVerticalEquation (E : VerticalGraph) : AffineCurve :=
  N13GeneralizedMumfordIntegral.yClass ^ 2 +
    N13GeneralizedMumfordIntegral.xClassHom
        (C (E.m.coeff 1) * X ^ 3) *
      N13GeneralizedMumfordIntegral.yClass +
    N13GeneralizedMumfordIntegral.xClassHom
      (C (E.m.coeff 0) * X ^ 6)
/-- The weight-three affine transform of `t-(a+cv)`. -/
def affineLinearEquation (E : VerticalGraph) : AffineCurve :=
  N13OrdinaryCurveOverlap.xClass ^ 2 -
    algebraMap R₂ AffineCurve E.a *
      N13OrdinaryCurveOverlap.xClass ^ 3 -
    algebraMap R₂ AffineCurve E.c *
      N13GeneralizedMumfordIntegral.yClass
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
abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph
end
end MazurProof.N13RankTwoInfinityVerticalGraphRecovery
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
attribute [local instance] MazurProof.N13AllPointAffineSpread.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
def integralReciprocal (a b : R₂) : R₂[X] :=
  X ^ 2 + C a * X + C b
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
abbrev κ : Type :=
  IsLocalRing.ResidueField R₂
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.baseSpecialAlgebra
/-- The inverse affine coordinate inside the generic graph quotient. -/
def tbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  algebraMap Q₂ (GenericQuotient D) (-(D.u.coeff 0)⁻¹) *
    (xbar D +
      algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))
/-- The ordinary infinity ordinate inside the generic graph quotient. -/
def vbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  tbar D ^ 3 * goodYbar D
def baseToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    R₂[X] →+* GenericQuotient D :=
  Polynomial.eval₂RingHom
    (coefficientToGenericQuotient D) (tbar D)
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
abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph
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
/-- The affine coordinate is a unit in the quotient by `I`.  This is the
ideal-theoretic form of saying that the closed subscheme cut out by `I`
does not acquire support on the omitted divisor `x=0`. -/
def XUnitMod (I : Ideal AffineCurve) : Prop :=
  ∃ q : AffineCurve,
    1 - q * N13SpecialCurveOverlap.xClass ∈ I
end
end MazurProof.N13SpecialAffineSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor =====
section
/-!
# Special divisors cut out by infinity-chart graphs

A monic quadratic graph on the special infinity chart splits over `F₂`.
Roots at `t = 0` give the two points at infinity, while roots at `t = 1`
give affine points on the overlap.  This is the proper root divisor needed
when an integral reciprocal graph loses affine degree after reduction.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Mumford graph data on the special infinity chart, with a monic
horizontal polynomial. -/
structure SemiMumford
    extends
      GeneralizedGraphIdealCore.SemiGraph
        N13SpecialInfinityChart.hPoly
        N13SpecialInfinityChart.rhsPoly where
  u_monic : u.Monic
/-- Reduce an integral infinity graph coefficientwise modulo `2`. -/
def reduceGraphData
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic) :
    SemiMumford where
  u := N13IntegralInfinityReduction.reducePoly E.u
  v := N13IntegralInfinityReduction.reducePoly E.v
  w := N13IntegralInfinityReduction.reducePoly E.w
  u_monic := hu.map N13IntegralInfinityReduction.reduceBase
  curve_eq := by
    have h := congrArg N13IntegralInfinityReduction.reducePoly E.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      N13IntegralInfinityReduction.reduce_hBase,
      N13IntegralInfinityReduction.reduce_rhsBase] using h
end
end MazurProof.N13SpecialInfinityGraphDivisor
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
/-- The ideal of the graph `u(t) = 0`, `v∞ = v(t)`. -/
def graphIdeal (u v : K[X]) : Ideal Ring :=
  GeneralizedGraphIdealCore.graphIdeal xClassHom yClass u v
/-- The affine ideal contributed by an unordered pair of infinity roots. -/
def rootAffineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford) :
    Sym2 K → Ideal N13SpecialDivisorCharts.SpecialAffine :=
  Sym2.lift
    ⟨fun a b =>
        (if a = 0 then ⊤ else
          N13GoodCoordinateRingTwo.mumfordIdeal
            (X - C 1) (C (D.v.eval a))) *
        (if b = 0 then ⊤ else
          N13GoodCoordinateRingTwo.mumfordIdeal
            (X - C 1) (C (D.v.eval b))),
      fun a b => by
        dsimp
        rw [mul_comm]⟩
/-- Evaluation of the affine root-ideal product on a concrete unordered
pair. -/
@[simp] theorem rootAffineIdeal_mk
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a b : K) :
    rootAffineIdeal D s(a, b) =
      (if a = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval a))) *
      (if b = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval b))) :=
  rfl
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
/-- Translation by the residue coordinate `a`; over `F₂` this translation
is its own inverse. -/
def translate (a : K) (p : K[X]) : K[X] :=
  p.comp (X + C a)
/-- The nonconstant vertical graph ideal `(m(v),t-(a+v))`. -/
def verticalIdeal (m : K[X]) (a : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13SpecialInfinityChart.vClass m,
      N13SpecialInfinityChart.tClass -
        aeval N13SpecialInfinityChart.vClass (C a + X)} :
      Set Ring)
/-- Translation by an `F₂` coordinate is involutive. -/
theorem translateLinear_comp_translateLinear (a : K) :
    (C a + X).comp (X + C a) = X := by
  have haa : a + a = 0 := by
    fin_cases a <;> decide
  simp only [add_comp, C_comp, X_comp]
  calc
    C a + (X + C a) = X + (C a + C a) := by ring
    _ = X := by rw [← C_add, haa]; simp
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction =====
section
/-!
# Special restriction of constant vertical infinity graphs

An integral vertical infinity graph is defined by a monic quadratic
`m(v)` and a linear relation `t=a+cv`.  This file treats the branch in
which `c` reduces to zero.  On the special fibre the relation becomes the
constant equation `t=ā`, so the reduced quadratic is forced to be `v²+v`
and the infinity ideal is the principal fibre ideal `(t-ā)`.

The weighted affine closure is not recomputed generator by generator.
Its reflected reciprocal equation makes `x` a unit modulo the ideal, and
this property survives reduction.  The canonical target fibre has the same
property.  Equality of the infinity ideals and compatibility on the overlap
therefore determine the full reduced two-chart pair.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Integral vertical graph data on the infinity chart. -/
abbrev VerticalGraph :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
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
set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- The exact remaining datum on the reciprocal chart.  Its horizontal
equation is the integral reciprocal quadratic, its other two equations
have the weighted bounds needed for two-chart reflection, and its reflected
ordinate cuts out the original generic Mumford graph. -/
structure ReciprocalGraphClosure
    (D : SexticMumford.Mumford Model)
    (a b : R₂) where
  data : InfinityGraphData
  data_u :
    data.u =
      N13ReciprocalQuadraticReflection.integralReciprocal a b
  v_degree : data.v.natDegree ≤ 3
  w_degree : data.w.natDegree ≤ 4
  generic_ordinate :
    D.u ∣
      N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly
            (N13IntegralInfinityGraphTwoChart.affineV data)) -
        D.v
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
/-- Points on the completed special curve. -/
abbrev CurvePoint : Type :=
  N13SymmetricSquareTwo.CurvePoint
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
/-- Literal coefficientwise reduction of the weighted infinity ideal. -/
def reducedWeightedInfinityIdeal
    (P : IntegralPoint) :
    Ideal N13IntegralInfinityReduction.SpecialRing :=
  Ideal.span
    {1 -
        N13IntegralInfinityReduction.specialBaseClass
            (C (N13GeneralizedMumfordReduction.reduceBase P.1.1)) *
          N13SpecialInfinityChart.tClass,
      N13SpecialInfinityChart.vClass -
        N13IntegralInfinityReduction.specialBaseClass
            (C (N13GeneralizedMumfordReduction.reduceBase P.1.2)) *
          N13SpecialInfinityChart.tClass ^ 3}
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
/-- Algebra structure used to extend an integral fractional ideal to the
generic sextic coordinate ring. -/
local instance integralRationalAlgebra :
    Algebra N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra
/-- The common function field is the fraction field of the integral affine
coordinate ring. -/
local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13QuadraticTwoChartSpreadSaturation.integralRationalAlgebra
local instance integralFunctionFieldFractionRing :
    IsFractionRing A K :=
  N13IntegralFractionalHull.functionField_isFractionRing
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
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
/-- Literal effective degree-two divisors on the completed special fibre. -/
abbrev EffectiveDivisorTwo : Type :=
  N13TwoChartPicardRealization.EffectiveDivisorTwo
end
end MazurProof.N13SplitQuadraticPicardRealization
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
/-- The X-adic ideal in the complete coefficient ring. -/
def xIdeal : Ideal Power :=
  Ideal.span ({PowerSeries.X} : Set Power)
local instance instIsAdicCompletePowerXIdeal : IsAdicComplete xIdeal Power := by
  unfold xIdeal
  infer_instance
theorem infinityCurvePoly_eval_zero_mem :
    N13FormalInfinityChart.infinityCurvePoly.eval 0 ∈ xIdeal := by
  have hx : PowerSeries.X ∈ xIdeal :=
    Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  have hrhs : N13FormalInfinityChart.rhsPower ∈ xIdeal := by
    unfold N13FormalInfinityChart.rhsPower
    refine Ideal.add_mem xIdeal hx ?_
    simpa only [pow_two] using
      Ideal.mul_mem_left xIdeal PowerSeries.X hx
  simpa [N13FormalInfinityChart.infinityCurvePoly] using
    Submodule.neg_mem xIdeal hrhs
end
end MazurProof.N13FormalInfinityBranches
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
theorem toZMod_mk_of_eq (y c : Q₂) (h : ‖y‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hy : y = c) :
    PadicInt.toZMod (⟨y, h⟩ : ℤ_[2]) = PadicInt.toZMod (⟨c, hc⟩ : ℤ_[2]) := by
  subst hy; rfl
end
end MazurProof.N13InverseInfinityData
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
/-- The existing oriented fractional-ideal presentation of the
characteristic-zero N13 Picard group, with the positive infinity chosen. -/
abbrev J13 : Type := N13MumfordAbelJacobi.ConcretePic ℚ
/-!
For the smooth two-infinity sextic, a projective Cartier divisor is encoded
by its invertible fractional ideal on the affine chart together with its two
orders at the omitted infinity points.  This carrier uses arbitrary
invertible fractional ideals, not merely the subgroup generated by rational
points.
-/
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
/-- The explicit rational function `Y + s(X) = Y - (-s(X))`. -/
def caFn13 : RatFun13ˣ :=
  SexticMumford.ySubFunctionUnit M13 (-s13)
/-! ## Exact order at the positive infinity branch -/
/-! ## Pass the principal divisor to the oriented Picard quotient -/
end MazurProof.N13Arithmetic
end
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
/-- Laurent monomials are units, with inverse exponent. -/
def tPowUnit (n : ℤ) : Laurentˣ where
  val := N13FormalCurveOverlap.tPow n
  inv := N13FormalCurveOverlap.tPow (-n)
  val_inv := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
  inv_val := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
end
end MazurProof.N13OrdinaryCompletionCompatibility
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
attribute [local instance] MazurProof.N13PrimitiveVerticalPresentation.instAlgebraAffineRationalRing
local instance instIsFractionRingAffineCommonField : IsFractionRing Affine CommonField :=
  N13IntegralFractionalHull.functionField_isFractionRing
end N13Charts
end
end MazurProof.N13PrimitiveVerticalPresentation
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
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing
attribute [local instance] MazurProof.N13PrimitiveAffineComparison.instIsLocalizationIntegralRingVerticalScalarsR
end
end MazurProof.N13PrimitiveAffineComparison
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityIdealApproximation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityIdealApproximation =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Actual N13 two-branch ideal equality implies all-order approximation on the
ordinary infinity chart after clearing one nonzero vertical scalar. The
scalar is retained, not cancelled in the integral ring. This is the precise
input that becomes ordinary approximation after generic-fibre localization.
-/
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13InfinityIdealApproximation.instFactPrimeOfNatNat_fLT
theorem jet_eq_of_dvd_sub (n : ℕ) (r s : QP)
    (h : (PowerSeries.X : QP) ^ n ∣ r - s) : jetQuot n r = jetQuot n s := by
  have hh : jetQuot n (r - s) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh
end
end MazurProof.N13InfinityIdealApproximation
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
attribute [local instance] MazurProof.N13IntegralPrincipalComparison.instAlgebraAR
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13MarkedTensorComparison.instAlgebraAR
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing
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
attribute [local instance] MazurProof.N13EffectiveDataCompatibility.instAlgebraAR
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing
end
end MazurProof.N13EffectiveDataCompatibility
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
open N13SpecialDivisorCharts hiding K
theorem conjugate_involutive (z : R) : conjugate (conjugate z) = z := by
  have hz : z = linear (coeff0 z) (coeffY z) := (recompose z).symm
  calc
    conjugate (conjugate z) = conjugate (conjugate (linear (coeff0 z) (coeffY z))) := by rw [← hz]
    _ = linear ((coeff0 z - coeffY z * hPoly) - -coeffY z * hPoly) (- -coeffY z) := by
      rw [conjugate_linear, conjugate_linear]
    _ = linear (coeff0 z) (coeffY z) := by congr 1 <;> ring
    _ = z := hz.symm
theorem linear_mul_conjugate (p q : K[X]) :
    linear p q * conjugate (linear p q) = xClass (normPolynomial p q) := by
  rw [conjugate_linear]
  simp only [linear, normPolynomial, xClass_sub, xClass_mul, xClass_pow, xClass_neg]
  linear_combination -(xClass q) ^ 2 * yClass_relation
theorem mul_conjugate (z : R) : z * conjugate z = xClass (norm z) := by
  have he := linear_mul_conjugate (coeff0 z) (coeffY z)
  have hz : linear (coeff0 z) (coeffY z) = z := recompose z
  rw [hz] at he
  exact he
theorem norm_ne_zero (z : R) (hz : z ≠ 0) : norm z ≠ 0 := by
  intro hn
  have hp := mul_conjugate z
  rw [hn, xClass_zero] at hp
  rcases mul_eq_zero.mp hp with h | h
  · exact hz h
  · have hc := congrArg conjugate h
    rw [conjugate_involutive, map_zero] at hc
    exact hz hc
open N13SpecialComparisonFactorPair hiding xClass R
end
end MazurProof.N13SpecialAffineNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Compute the actual special infinity ideals of rational-point divisors under
both named branch maps. The finite-degree and two infinity counts add to
the total degree. A principal ideal equation therefore gives an exact
Laurent-order balance, not a guessed sheet assignment.
-/
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
def pointOrder (negative : Bool) : CurvePoint → ℕ
  | Sum.inl _ => 0
  | Sum.inr P => if P.1 = (if negative then 1 else 0) then 1 else 0
def divisorOrder (negative : Bool) : EffectiveDivisorTwo → ℕ :=
  Sym2.lift ⟨fun P Q => pointOrder negative P + pointOrder negative Q, fun P Q => Nat.add_comm _ _⟩
@[simp] theorem divisorOrder_mk (negative : Bool) (P Q : CurvePoint) :
    divisorOrder negative s(P, Q) = pointOrder negative P + pointOrder negative Q := rfl
end
end MazurProof.N13SpecialDivisorBranchOrders
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
def residual (H R s : K[X]) : K[X] := s ^ 2 + H * s - R
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

-- ===== FLT.Assumptions.MazurProof.N13SpecialFiniteBranchJets =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialFiniteBranchJets =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual Hensel branches at the four finite rational points of the GOOD F2
curve. Their certified nine-jets are the four finite polynomials used in
the bounded principal-function certificate.
-/
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def xIdeal : Ideal P := Ideal.span ({PowerSeries.X} : Set P)
instance instIsAdicCompletePXIdeal : IsAdicComplete xIdeal P := by unfold xIdeal; infer_instance
def evalBase (a : K) : K[X] →+* P := Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.X + PowerSeries.C a)
end
end MazurProof.N13SpecialFiniteBranchJets
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
abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo
end
end MazurProof.N13SpecialAbelCode
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialFinitePointOrders =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialFinitePointOrders =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Compute the four finite local point/divisor ideals, and identify the given
special divisor code with the weighted six actual point multiplicities.
-/
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
def finitePointOrder (a : K) (negative : Bool) : CurvePoint → ℕ
  | Sum.inl P => if P.1.1 = a ∧ P.1.2 = (if negative then 1 else 0) then 1 else 0
  | Sum.inr _ => 0
def finiteDivisorOrder (a : K) (negative : Bool) : EffectiveDivisorTwo → ℕ :=
  Sym2.lift ⟨fun P Q => finitePointOrder a negative P + finitePointOrder a negative Q,
    fun P Q => Nat.add_comm _ _⟩
@[simp] theorem finiteDivisorOrder_mk (a : K) (negative : Bool) (P Q : CurvePoint) :
    finiteDivisorOrder a negative s(P, Q) = finitePointOrder a negative P + finitePointOrder a negative Q := rfl
end
end MazurProof.N13SpecialFinitePointOrders
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient =====
section
/-!
# The explicit `ZMod 19` code of the special Abel quotient (plan Q8717, A03–A07)

`divisorCode` (A01/A02, `N13SpecialAbelCode`) separates the 21 effective degree-two divisors
exactly up to `AbelRel`: equal codes force equal divisors or two canonical divisors (A03/A04).
Hence it descends to an injective, and by counting bijective, map
`PicTwoSetModel → ZMod 19` (A05/A06), and every `r : ZMod 19` transports to a translation of
`PicTwoSetModel` (A07).  The separation fact is a finite check on
`Sym2 (BasePoint × K)`, done by `decide` after transport along `curvePointEquiv`.
-/
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- The canonical pencil in the explicit coordinates. -/
def CanonBP (S : Sym2 (BasePoint × K)) : Prop :=
  ∃ b : BasePoint, S = s((b, 0), (b, 1))
instance instDecidablePredSym2ProdBasePointKCanonBP : DecidablePred CanonBP := fun S => by
  unfold CanonBP; infer_instance
theorem map_canonicalDivisor (b : BasePoint) :
    (canonicalDivisor b).map curvePointEquiv = s((b, 0), (b, 1)) := by
  simp [canonicalDivisor]
end
end MazurProof.N13SpecialAbelCode
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
def baseDivisor : EffectiveDivisorTwo :=
  s(specialCuspEquiv .zeroPlus, specialCuspEquiv .negOneMinus)
end
end MazurProof.N13KernelBaseDivisor
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
abbrev Overlap : Type :=
  N13FormalCurveOverlap.Overlap
/-- Every Laurent monomial is a unit, with the opposite monomial as
inverse. -/
def tPowUnit (n : ℤ) : Laurentˣ where
  val := N13FormalCurveOverlap.tPow n
  inv := N13FormalCurveOverlap.tPow (-n)
  val_inv := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
  inv_val := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
@[simp] theorem coe_tPowUnit (n : ℤ) :
    (tPowUnit n : Laurent) =
      N13FormalCurveOverlap.tPow n :=
  rfl
/-- Evaluation of an ordinary polynomial at `t` agrees with first viewing
it as a power series and then including it into Laurent series. -/
theorem eval₂_tPow_one_eq_includePower
    (p : R₂[X]) :
    p.eval₂ (algebraMap R₂ Laurent)
        (N13FormalCurveOverlap.tPow 1) =
      N13FormalInfinityChart.includePowerRing
        (p : PowerSeries R₂) := by
  have h :
      Polynomial.eval₂RingHom
          (algebraMap R₂ Laurent)
          (N13FormalCurveOverlap.tPow 1) =
        N13FormalInfinityChart.includePowerRing.comp
          Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [N13FormalInfinityChart.includePowerRing,
        N13FormalCurveOverlap.tPow,
        HahnSeries.algebraMap_apply']
    · simp [N13FormalInfinityChart.includePowerRing_X]
  exact congrArg (fun f : R₂[X] →+* Laurent => f p) h
attribute [local instance] tInvInvertible
/-- Reversal factors a polynomial at infinity into its pole monomial and a
power series with the coefficients in the opposite order. -/
theorem polyAtTInv_eq_reverse
    (p : R₂[X]) :
    N13FormalCurveOverlap.polyAtTInv p =
      N13FormalInfinityChart.includePowerRing
          (p.reverse : PowerSeries R₂) *
        N13FormalCurveOverlap.tPow
          (-(p.natDegree : ℤ)) := by
  have h :=
    Polynomial.eval₂_reverse_mul_pow
      (algebraMap R₂ Laurent)
      (N13FormalCurveOverlap.tPow (-1)) p
  have hpow :
      N13FormalCurveOverlap.tPow (-1) ^ p.natDegree =
        N13FormalCurveOverlap.tPow
          (-(p.natDegree : ℤ)) := by
    simp [N13FormalCurveOverlap.tPow,
      HahnSeries.single_pow]
  change
    p.reverse.eval₂ (algebraMap R₂ Laurent)
          (N13FormalCurveOverlap.tPow 1) *
        N13FormalCurveOverlap.tPow (-1) ^ p.natDegree =
      N13FormalCurveOverlap.polyAtTInv p at h
  rw [eval₂_tPow_one_eq_includePower, hpow] at h
  exact h.symm
/-! ## Reduction of polynomial restrictions -/
/-- Coefficientwise reduction as a ring homomorphism. -/
def reduceLaurentHom : Laurent →+* LaurentBar where
  toFun := N13FormalLineBundleCech.reduceLaurent
  map_zero' := N13FormalLineBundleCech.reduceLaurent_zero
  map_one' := N13FormalLineBundleCech.reduceLaurent_one
  map_add' := N13FormalLineBundleCech.reduceLaurent_add
  map_mul' := N13FormalLineBundleCech.reduceLaurent_mul
@[simp] theorem reduceLaurentHom_apply
    (f : Laurent) :
    reduceLaurentHom f =
      N13FormalLineBundleCech.reduceLaurent f :=
  rfl
/-- Evaluate a special-fibre polynomial at `t⁻¹`. -/
def specialPolyAtTInv : K[X] →+* LaurentBar :=
  Polynomial.eval₂RingHom
    (algebraMap K LaurentBar)
    (N13FormalLineBundleCech.tPow (R := K) (-1))
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
abbrev Overlap : Type :=
  N13MumfordFormalTransition.Overlap
/-- The two coefficients which recover the disk coordinates to first
order. -/
def firstJet (z : Overlap) : Fin 2 → R₂ :=
  ![-z.1.coeff 0,
    -z.1.coeff (-1) + z.1.coeff 0]
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
theorem mem_leftIdeal_iff (p : BiPoly R) :
    p ∈ leftIdeal R ↔
      ∀ m ∈ p.support,
        ∃ i : Fin 2, m (Sum.inl i) ≠ 0 := by
  rw [leftIdeal, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h m hm
    obtain ⟨i, hi, hmi⟩ := h m hm
    obtain ⟨j, rfl⟩ := hi
    exact ⟨j, hmi⟩
  · intro h m hm
    obtain ⟨i, hmi⟩ := h m hm
    exact ⟨Sum.inl i, ⟨i, rfl⟩, hmi⟩
theorem mem_rightIdeal_iff (p : BiPoly R) :
    p ∈ rightIdeal R ↔
      ∀ m ∈ p.support,
        ∃ i : Fin 2, m (Sum.inr i) ≠ 0 := by
  rw [rightIdeal, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h m hm
    obtain ⟨i, hi, hmi⟩ := h m hm
    obtain ⟨j, rfl⟩ := hi
    exact ⟨j, hmi⟩
  · intro h m hm
    obtain ⟨i, hmi⟩ := h m hm
    exact ⟨Sum.inr i, ⟨i, rfl⟩, hmi⟩
theorem crossExponent_le
    (m : Var →₀ ℕ) (i j : Fin 2)
    (hi : m (Sum.inl i) ≠ 0)
    (hj : m (Sum.inr j) ≠ 0) :
    Finsupp.single (Sum.inl i) 1 +
        Finsupp.single (Sum.inr j) 1 ≤ m := by
  intro k
  by_cases hki : k = Sum.inl i
  · subst k
    simp [Nat.one_le_iff_ne_zero.mpr hi]
  · by_cases hkj : k = Sum.inr j
    · subst k
      simp [Nat.one_le_iff_ne_zero.mpr hj]
    · simp [hki, hkj]
theorem monomial_mem_axis_product
    (p : BiPoly R) (m : Var →₀ ℕ)
    (i j : Fin 2)
    (hi : m (Sum.inl i) ≠ 0)
    (hj : m (Sum.inr j) ≠ 0) :
    monomial m (p.coeff m) ∈ leftIdeal R * rightIdeal R := by
  have hleft : leftVar R i ∈ leftIdeal R := by
    apply Ideal.subset_span
    exact ⟨Sum.inl i, ⟨i, rfl⟩, rfl⟩
  have hright : rightVar R j ∈ rightIdeal R := by
    apply Ideal.subset_span
    exact ⟨Sum.inr j, ⟨j, rfl⟩, rfl⟩
  have hcross :
      leftVar R i * rightVar R j ∈
        leftIdeal R * rightIdeal R :=
    Ideal.mul_mem_mul hleft hright
  have hdvd :
      monomial
          (Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inr j) 1)
          (1 : R) ∣
        monomial m (p.coeff m) := by
    apply MvPolynomial.monomial_dvd_monomial.mpr
    exact
      ⟨Or.inr (crossExponent_le m i j hi hj),
        one_dvd (p.coeff m)⟩
  rw [crossMonomial_eq] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  rw [hq]
  exact (leftIdeal R * rightIdeal R).mul_mem_right q hcross
/-- The ideals generated by the two disjoint coordinate blocks meet
transversely. -/
theorem leftIdeal_inf_rightIdeal :
    leftIdeal R ⊓ rightIdeal R =
      leftIdeal R * rightIdeal R := by
  apply le_antisymm
  · intro p hp
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro m hm
    obtain ⟨i, hi⟩ :=
      (mem_leftIdeal_iff R p).mp hp.1 m hm
    obtain ⟨j, hj⟩ :=
      (mem_rightIdeal_iff R p).mp hp.2 m hm
    exact monomial_mem_axis_product R p m i j hi hj
  · exact Ideal.mul_le_inf
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
variable [AddCommGroup K]
set_option maxHeartbeats 4000000 in
/-- The diagonal part of a regular group law.  This is the exact unary
input used by the separatedness argument. -/
structure DoublingLaw
    (coord : K → Fin 2 → R₂) where
  double_error_mem :
    ∀ z i,
      coord (2 • z) i - (coord z i + coord z i) ∈
        N13TwoAdicKernelChart.coordIdeal coord z *
          N13TwoAdicKernelChart.coordIdeal coord z
namespace DoublingLaw
variable {coord : K → Fin 2 → R₂}
end DoublingLaw
namespace PolynomialLaw
variable {coord : K → Fin 2 → R₂}
end PolynomialLaw
set_option maxHeartbeats 4000000 in
/-- The minimal geometric input required for the separatedness argument:
faithful disk representatives and their unary doubling estimate. -/
structure DoublingGeometricData
    (K : Type u) [AddCommGroup K] where
  pair : K → N13TwoAdicAbelChartData.DiskPair
  pair_zero :
    pair 0 = N13TwoAdicAbelChartData.basePair
  pair_injective : Function.Injective pair
  law :
    DoublingLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))
namespace DoublingGeometricData
variable (D : DoublingGeometricData K)
def coord : K → Fin 2 → R₂ :=
  fun z => N13TwoAdicAbelChartData.DiskPair.coord (D.pair z)
@[simp] theorem coord_zero :
    D.coord 0 = 0 := by
  rw [coord, D.pair_zero]
  exact N13TwoAdicAbelChartData.DiskPair.coord_basePair
theorem coord_injective :
    Function.Injective D.coord :=
  N13TwoAdicAbelChartData.DiskPair.coord_injective.comp
    D.pair_injective
theorem coord_mem_two
    (z : K) (i : Fin 2) :
    D.coord z i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 :=
  N13TwoAdicAbelChartData.DiskPair.coord_mem_two
    (D.pair z) i
include D
end DoublingGeometricData
namespace GeometricData
end GeometricData
end
end MazurProof.N13TwoAdicAbelChartLaw
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
/-- The rational oriented Picard group of the N13 curve. -/
abbrev RationalPic : Type :=
  N13TwoAdicAbelChartSection.RationalPic
/-- The oriented Picard group of the N13 curve over the two-adic field. -/
abbrev Pic₂ : Type :=
  N13TwoAdicAbelChartPic.Pic
/-- The Picard class of the distinguished nonspecial base disk pair. -/
def basePic : Pic₂ :=
  N13TwoAdicAbelChartPic.DiskPair.pic
    N13TwoAdicAbelChartData.basePair
/-! ## Recovering canonical disk pairs from kernel representatives -/
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
end NearBaseFamily
namespace MappedSpecialRepresentative
variable {c : Pic₂}
end MappedSpecialRepresentative
namespace MappedSpecialFamily
variable {H : AddSubgroup RationalPic}
end MappedSpecialFamily
/-! ## Canonical mapped-special representatives -/
namespace CanonicalMappedSpecialFamily
variable {H : AddSubgroup RationalPic}
end CanonicalMappedSpecialFamily
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
/-! ## Comparing a selected double with the squared transition -/
end NearBaseFamily
/-! ## The exact remaining unary compatibility -/
namespace FirstJetDoublingCompatibility
variable {H : AddSubgroup RationalPic}
end FirstJetDoublingCompatibility
/-! ## One-call assembly from mapped-special representatives -/
namespace MappedSpecialFamily
variable {H : AddSubgroup RationalPic}
end MappedSpecialFamily
namespace CanonicalMappedSpecialFamily
variable {H : AddSubgroup RationalPic}
end CanonicalMappedSpecialFamily
/-! ## Specialization to the eventual spread classifier -/
namespace Concrete
variable {Line : Type u}
end Concrete
end
end MazurProof.N13RationalKernelDoublingAdapter
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
def cuspMumford (c : N13Mumford.Cusp13) : N13Mumford.Mumford Q₂ :=
  (SexticMumford.pointMumford (N13Mumford.model ℚ) (N13Mumford.cuspPoint c)).mapCoeffs
    N13InfinityBaseChange.ratToQ₂ N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)
end
end MazurProof.N13KernelBasePic
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
def matrix (P : DiskPair) (s : Fin 2 → R₂) : Matrix (Fin 4) (Fin 4) R₂ :=
  let x₀ := P.x₀
  let x₁ := P.x₁
  let u₀ := x₀ ^ 2 + x₀
  let u₁ := x₁ ^ 2 + x₁
  let d₀ := 2 * x₀ + 1
  let d₁ := 2 * x₁ + 1
  let y₀ := oppositeY P 0
  let y₁ := oppositeY P 1
  !![u₀, u₀ * x₀, y₀, y₀ * x₀;
     u₁, u₁ * x₁, y₁, y₁ * x₁;
     d₀, d₀ * x₀ + u₀, s 0, y₀ + x₀ * s 0;
     d₁, d₁ * x₁ + u₁, s 1, y₁ + x₁ * s 1]
end
end MazurProof.N13IntegralHermiteNumerator
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
abbrev c := N13TwoAdicMumfordTransport.coeffMap
def x (P : DiskPair) (j : Fin 2) : K := c (N13CenteredHermiteFirstOrder.x P j)
def y (P : DiskPair) (j : Fin 2) : K := c (N13CenteredHermiteFirstOrder.oppositeY P j)
def s (P : DiskPair) (j : Fin 2) : K := c (N13HermiteResidualDivisibility.slope P j)
def U (P : DiskPair) : K[X] := N13TwoAdicMumfordTransport.mapPoly P.u
end
end MazurProof.N13ActualHermiteEquations
end

end

-- ===== FLT.Assumptions.MazurProof.N13RationalHermiteMatrix =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RationalHermiteMatrix =====
section
/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

The accepted integral interpolation matrix stays invertible over Q2.
Consequently every rational Hermite numerator with leading coefficient t
has its four remaining coefficients equal to t times one integral solution.
No division by a moving coordinate or by t occurs in this comparison.
-/
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13RationalHermiteMatrix.instFactPrimeOfNatNat_fLT
def matrixQ (P : DiskPair) : Matrix (Fin 4) (Fin 4) K :=
  (N13IntegralHermiteNumerator.matrix P (N13HermiteResidualDivisibility.slope P)).map c
def rhsQ (P : DiskPair) : Fin 4 → K :=
  fun j => c (N13IntegralHermiteNumerator.rightSide P j)
end
end MazurProof.N13RationalHermiteMatrix
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralMatchedNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralMatchedNorm =====
section
/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Descend the actual matched norm identity to Z2. Leading coefficients
determine the scalar exactly as 1-e1 after cancelling the nonzero rational
normalization scale squared. Coefficient injection then gives the literal
integral norm equation required by the accepted centered-norm theorem.
-/
namespace MazurProof.N13IntegralMatchedNorm
noncomputable section
open Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT
abbrev U : R₂[X] := N13AbelChartBase.baseSmoothMumford.u
def normPoly (A b : R₂[X]) : R₂[X] :=
  (U * A) ^ 2 - (U * A) * b * N13GeneralizedMumfordIntegral.hPoly -
    b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly
end
end MazurProof.N13IntegralMatchedNorm
end

end


