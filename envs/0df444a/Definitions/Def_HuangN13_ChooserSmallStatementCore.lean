-- Prove2me | Definitions.Def_HuangN13_ChooserSmallStatementCore
-- name    : HuangN13_ChooserSmallStatementCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:13:06.153522+00:00
-- url     : https://prove2.me/theorems/4149513d-f530-4913-9b4a-98c5ccd177cb
-- title:
--   Exact original statement data for contractIdeal_eq_affineIdeal, exists_integralInfinity_basis_oneT_or_oneV, exists_horizontal_or_vertical_recovery…
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_finiteAffineIdeal_isUnit
import Theorems.Thm_MazurProof_N13InfinityBaseChange_infinityCompatible
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13ReciprocalInfinityContraction_goodYbar_relation
import Theorems.Thm_MazurProof_N13ReciprocalInfinityContraction_xbar_mul_tbar
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_invFracMap_toPrincipalIdeal

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem orientedFracMap_principalOriented
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O')
    (α : (FunctionField M)ˣ) :
    orientedFracMap ι hι hM (principalOriented M O α) =
      principalOriented M' O' (functionUnitMap ι hι hM α) := by
  apply Prod.ext
  · change
      invFracMap ι hι hM
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α) =
        toPrincipalIdeal (CoordinateRing M') (FunctionField M')
          (functionUnitMap ι hι hM α)
    exact invFracMap_toPrincipalIdeal ι hι hM α
  · change
      O.ordPlus α =
        O'.ordPlus (functionUnitMap ι hι hM α)
    exact (hO α).symm
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem principalRange_le_comap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O') :
    (principalOriented M O).range ≤
      Subgroup.comap (orientedFracMap ι hι hM)
        (principalOriented M' O').range := by
  intro z hz
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
  rw [Subgroup.mem_comap]
  exact MonoidHom.mem_range.mpr
    ⟨functionUnitMap ι hι hM α,
      (orientedFracMap_principalOriented ι hι hM O O' hO α).symm⟩
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- The additive homomorphism on concrete oriented Picard groups induced by
coefficient extension. -/
def picMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O') :
    ConcretePic M O →+ ConcretePic M' O' :=
  MonoidHom.toAdditive <|
    QuotientGroup.map
      (principalOriented M O).range
      (principalOriented M' O').range
      (orientedFracMap ι hι hM)
      (principalRange_le_comap ι hι hM O O' hO)
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The concrete oriented Picard base-change map from the rational N13
function field to its two-adic coefficient extension. -/
def picMapRatToQ₂ :
    SexticMumford.ConcretePic
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) →+
      SexticMumford.ConcretePic
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂) :=
  SexticMumford.OrientedBaseChange.picMap
    ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)
    (N13Infinity.positiveInfinityOrder ℚ)
    (N13Infinity.positiveInfinityOrder Q₂)
    (infinityCompatible ratToQ₂ ratToQ₂_injective)
end
end MazurProof.N13InfinityBaseChange
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A finite quadratic Mumford graph has an actual proper two-chart integral
line whose affine generic fibre is the original graph ideal. -/
def finiteQuadraticTwoChartLine
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (AffineCurve ⧸ finiteAffineIdeal D)) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  twoChartLineOfInfinityClosure
    (finiteAffineIdeal D)
    (finiteAffineIdeal_isUnit D hdeg hfinite)
    hfinite
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialQuadraticGraphRegularity
noncomputable section
attribute [local instance] MazurProof.N13SpecialQuadraticGraphRegularity.instFactPrimeOfNatNat_fLT
/-- The reduced horizontal polynomial retains degree two. -/
theorem reduceSemiMumford_u_natDegree
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    (reduceSemiMumford D hdeg).u.natDegree = 2 := by
  change
    (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree = 2
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    D.u_monic.natDegree_map, hdeg]
end
end MazurProof.N13SpecialQuadraticGraphRegularity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Three-generated affine closure of a vertical graph, including the
redundant reciprocal equation that removes support at `x=0`. -/
def affineIdeal (u : R₂[X]) (E : VerticalGraph) :
    Ideal AffineCurve :=
  Ideal.span
    ({affineReciprocal u,
      affineVerticalEquation E,
      affineLinearEquation E} : Set AffineCurve)
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem vbar_relation
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    vbar D ^ 2 +
        (1 + tbar D ^ 2 + tbar D ^ 3) * vbar D =
      tbar D + tbar D ^ 2 := by
  exact
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      (xbar D) (tbar D) (goodYbar D)
      (xbar_mul_tbar D hdeg h0)
      (goodYbar_relation D)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem infinityCurve_root
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        (baseToGenericQuotient D) (vbar D) = 0 := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul, sub_eq_zero]
  simpa [baseToGenericQuotient, coefficientToGenericQuotient,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] using
      vbar_relation D hdeg h0
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def integralInfinityToGenericQuotient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityRing →+* GenericQuotient D :=
  AdjoinRoot.lift
    (baseToGenericQuotient D)
    (vbar D)
    (infinityCurve_root D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The canonical integral infinity ideal attached directly to the generic
Mumford graph quotient. -/
def integralInfinityIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Ideal InfinityRing :=
  RingHom.ker (integralInfinityToGenericQuotient D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Only the geometric properties already constructed for the same Data.
In particular, neither a principal comparison nor additivity is a field. -/
def Certified (D : Data) : Prop :=
  ∃ E : N13Mumford.SemiMumford Q₂,
    EffectiveChamber E ∧
    genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
    AffineVerticallySaturated D.charts ∧
    HasInfinityMultiplicities D.charts (positiveMultiplicity E) (negativeMultiplicity E)
end
end MazurProof.N13EffectiveDataCompatibility
end
end


