-- Prove2me | Definitions.Def_HuangN13_DoublingStatementCore
-- name    : HuangN13_DoublingStatementCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:27:59.648726+00:00
-- url     : https://prove2.me/theorems/6b8c8b90-c1de-45f7-8ef0-768f668a46d5
-- title:
--   Exact original statement data for selected_cross_coefficients, representative_nonempty, exists_nearBase…
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_mul
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_oneOverlap
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_toOverlap
import Theorems.Thm_MazurProof_N13FormalLineBundleCech_mulOverlap_assoc
import Theorems.Thm_MazurProof_N13FormalLineBundleCech_reduceOverlap_mul

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13FormalLineBundleCech.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceLaurent_tPow
    (n : ℤ) :
    reduceLaurent (tPow (R := R₂) n) =
      tPow (R := K) n := by
  ext m
  by_cases hmn : m = n
  · subst m
    simp [reduceLaurent, tPow, reduceBase]
  · simp [reduceLaurent, tPow, reduceBase, hmn]
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
namespace NearIdentityTransition
variable (g : NearIdentityTransition)
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Tensor square of a near-trivial formal line bundle, written on its
overlap transition. -/
def square : NearIdentityTransition where
  transition := mulOverlap g.transition g.transition
  inverse := mulOverlap g.inverse g.inverse
  mul_inverse := by
    calc
      mulOverlap
          (mulOverlap g.transition g.transition)
          (mulOverlap g.inverse g.inverse) =
        mulOverlap g.transition
          (mulOverlap g.transition
            (mulOverlap g.inverse g.inverse)) :=
        mulOverlap_assoc _ _ _
      _ =
        mulOverlap g.transition
          (mulOverlap
            (mulOverlap g.transition g.inverse)
            g.inverse) := by
          rw [mulOverlap_assoc]
      _ =
        mulOverlap g.transition
          (mulOverlap oneOverlap g.inverse) := by
          rw [g.mul_inverse]
      _ = mulOverlap g.transition g.inverse := by
          rw [oneOverlap_mul]
      _ = oneOverlap := g.mul_inverse
  inverse_mul := by
    calc
      mulOverlap
          (mulOverlap g.inverse g.inverse)
          (mulOverlap g.transition g.transition) =
        mulOverlap g.inverse
          (mulOverlap g.inverse
            (mulOverlap g.transition g.transition)) :=
        mulOverlap_assoc _ _ _
      _ =
        mulOverlap g.inverse
          (mulOverlap
            (mulOverlap g.inverse g.transition)
            g.transition) := by
          rw [mulOverlap_assoc]
      _ =
        mulOverlap g.inverse
          (mulOverlap oneOverlap g.transition) := by
          rw [g.inverse_mul]
      _ = mulOverlap g.inverse g.transition := by
          rw [oneOverlap_mul]
      _ = oneOverlap := g.inverse_mul
  reduce_transition := by
    rw [reduceOverlap_mul, g.reduce_transition, oneOverlap_mul]
end NearIdentityTransition
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Multiplication of normal-form coordinates agrees with the pair
multiplication used by the Čech complex. -/
theorem toOverlap_mul
    (z w : FormalCurve) :
    toOverlap (z * w) =
      N13FormalLineBundleCech.mulOverlap
        (toOverlap z) (toOverlap w) := by
  apply ofOverlap_injective
  rw [ofOverlap_mul, ofOverlap_toOverlap,
    ofOverlap_toOverlap, ofOverlap_toOverlap]
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem toOverlap_one :
    toOverlap (1 : FormalCurve) =
      N13FormalLineBundleCech.oneOverlap (R := R₂) := by
  apply ofOverlap_injective
  rw [ofOverlap_toOverlap, ofOverlap_oneOverlap]
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A genuine unit on the formal overlap, whose reduction is one, supplies
the complete near-identity transition package.  Its inverse is inherited
from the unit rather than postulated separately. -/
def transitionOfUnit
    (u : FormalCurveˣ)
    (hreduce :
      N13FormalLineBundleCech.reduceOverlap
          (toOverlap (u : FormalCurve)) =
        N13FormalLineBundleCech.oneOverlap (R := N13FormalLineBundleCech.K)) :
    N13FormalLineBundleCech.NearIdentityTransition where
  transition := toOverlap (u : FormalCurve)
  inverse := toOverlap ((u⁻¹ : FormalCurveˣ) : FormalCurve)
  mul_inverse := by
    rw [← toOverlap_mul]
    simp
  inverse_mul := by
    rw [← toOverlap_mul]
    simp
  reduce_transition := hreduce
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem polyAtTInv_X :
    polyAtTInv X = tPow (-1) := by
  simp [polyAtTInv]
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem polyAtTInv_C (a : R₂) :
    polyAtTInv (_root_.Polynomial.C a) = algebraMap R₂ Laurent a := by
  simp [polyAtTInv]
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem toOverlap_algebraMap
    (f : Laurent) :
    toOverlap (algebraMap Laurent FormalCurve f) = (f, 0) := by
  calc
    toOverlap (algebraMap Laurent FormalCurve f) =
        toOverlap (ofOverlap (f, 0)) := by
          congr 1
          simp [ofOverlap]
    _ = (f, 0) := toOverlap_ofOverlap _
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reversal of a monic polynomial is a power-series unit because its
constant coefficient is one. -/
theorem reverse_powerSeries_isUnit
    (p : R₂[X]) (hp : p.Monic) :
    IsUnit (p.reverse : PowerSeries R₂) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    Polynomial.constantCoeff_coe,
    Polynomial.coeff_zero_reverse,
    hp.leadingCoeff]
  exact isUnit_one
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A monic affine polynomial becomes a unit on the integral Laurent
overlap. -/
theorem polyAtTInv_isUnit
    (p : R₂[X]) (hp : p.Monic) :
    IsUnit (N13FormalCurveOverlap.polyAtTInv p) := by
  rw [polyAtTInv_eq_reverse]
  exact
    (reverse_powerSeries_isUnit p hp).map
        N13FormalInfinityChart.includePowerRing
      |>.mul (tPowUnit (-(p.natDegree : ℤ))).isUnit
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13FormalLineBundleCech.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordFormalTransition.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceLaurent_algebraMap
    (a : R₂) :
    N13FormalLineBundleCech.reduceLaurent
        (algebraMap R₂ Laurent a) =
      algebraMap K LaurentBar
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  ext n
  by_cases hn : n = 0
  · subst n
    simp [N13FormalLineBundleCech.reduceLaurent,
      N13FormalLineBundleCech.reduceBase,
      N13GeneralizedMumfordReduction.reduceBase]
  · simp [N13FormalLineBundleCech.reduceLaurent,
      N13FormalLineBundleCech.reduceBase,
      N13GeneralizedMumfordReduction.reduceBase, hn]
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordFormalTransition.instFactPrimeOfNatNat_fLT
/-- Restriction to infinity commutes with coefficientwise reduction. -/
theorem reduceLaurent_polyAtTInv
    (p : R₂[X]) :
    N13FormalLineBundleCech.reduceLaurent
        (N13FormalCurveOverlap.polyAtTInv p) =
      specialPolyAtTInv
        (N13GeneralizedMumfordReduction.reducePoly p) := by
  have h :
      reduceLaurentHom.comp
          N13FormalCurveOverlap.polyAtTInv =
        specialPolyAtTInv.comp
          N13GeneralizedMumfordReduction.reducePoly := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [specialPolyAtTInv,
        N13GeneralizedMumfordReduction.reducePoly]
    · simp [specialPolyAtTInv,
        N13FormalCurveOverlap.polyAtTInv_X,
        N13GeneralizedMumfordReduction.reducePoly]
      change
        N13FormalLineBundleCech.reduceLaurent
            (N13FormalLineBundleCech.tPow (R := R₂) (-1)) =
          N13FormalLineBundleCech.tPow (R := K) (-1)
      exact N13FormalLineBundleCech.reduceLaurent_tPow (-1)
  exact congrArg (fun f : R₂[X] →+* LaurentBar => f p) h
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The scalar formal-curve unit represented by a monic affine
polynomial. -/
def formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    FormalCurveˣ :=
  ((polyAtTInv_isUnit p hp).map
    (algebraMap Laurent FormalCurve)).unit
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem coe_formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    (formalPolyUnit p hp : FormalCurve) =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.polyAtTInv p) :=
  IsUnit.unit_spec
    ((polyAtTInv_isUnit p hp).map
      (algebraMap Laurent FormalCurve))
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordFormalTransition.instFactPrimeOfNatNat_fLT
theorem reduceOverlap_formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          (formalPolyUnit p hp : FormalCurve)) =
      (specialPolyAtTInv
          (N13GeneralizedMumfordReduction.reducePoly p), 0) := by
  rw [coe_formalPolyUnit,
    N13FormalCurveOverlap.toOverlap_algebraMap]
  apply Prod.ext
  · change
      N13FormalLineBundleCech.reduceLaurent
          (N13FormalCurveOverlap.polyAtTInv p) =
        specialPolyAtTInv
          (N13GeneralizedMumfordReduction.reducePoly p)
    exact reduceLaurent_polyAtTInv p
  · change N13FormalLineBundleCech.reduceLaurent 0 = 0
    exact N13FormalLineBundleCech.reduceLaurent_zero
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The base graph's monic polynomial, as a formal-overlap unit. -/
def baseFormalPolyUnit : FormalCurveˣ :=
  formalPolyUnit
    N13AbelChartBase.baseSmoothMumford.u
    N13AbelChartBase.baseSmoothMumford.u_monic
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Ratio of the monic polynomial trivializations for a near-base graph
and the selected base graph. -/
def transitionUnit
    (D : NearBaseMumford) :
    FormalCurveˣ :=
  formalPolyUnit D.u D.u_monic *
    baseFormalPolyUnit⁻¹
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13AbelChartBase.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT
theorem reducePoly_eq_base
    (D : NearBaseMumford) :
    N13GeneralizedMumfordReduction.reducePoly D.u =
      N13GeneralizedMumfordReduction.reducePoly
        N13AbelChartBase.baseSmoothMumford.u := by
  rw [D.reduce_u]
  exact N13AbelChartBase.reduce_baseSmoothMumford_u.symm
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordFormalTransition.instFactPrimeOfNatNat_fLT
/-- The ratio transition of a near-base graph has identity special
fibre. -/
theorem reduce_transitionUnit
    (D : NearBaseMumford) :
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          (transitionUnit D : FormalCurve)) =
      N13FormalLineBundleCech.oneOverlap (R := K) := by
  change
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          ((formalPolyUnit D.u D.u_monic : FormalCurve) *
            (baseFormalPolyUnit⁻¹ : FormalCurveˣ))) =
      N13FormalLineBundleCech.oneOverlap (R := K)
  rw [N13FormalCurveOverlap.toOverlap_mul,
    N13FormalLineBundleCech.reduceOverlap_mul]
  have hred :
      N13FormalLineBundleCech.reduceOverlap
          (N13FormalCurveOverlap.toOverlap
            (formalPolyUnit D.u D.u_monic : FormalCurve)) =
        N13FormalLineBundleCech.reduceOverlap
          (N13FormalCurveOverlap.toOverlap
            (baseFormalPolyUnit : FormalCurve)) := by
    rw [reduceOverlap_formalPolyUnit,
      show baseFormalPolyUnit =
          formalPolyUnit
            N13AbelChartBase.baseSmoothMumford.u
            N13AbelChartBase.baseSmoothMumford.u_monic from rfl,
      reduceOverlap_formalPolyUnit,
      reducePoly_eq_base D]
  rw [hred, ← N13FormalLineBundleCech.reduceOverlap_mul,
    ← N13FormalCurveOverlap.toOverlap_mul]
  simp [N13FormalLineBundleCech.reduceOverlap_one]
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
/-- Every smooth integral graph reducing to the selected base graph supplies
the genuine near-identity transition used by the actual twisted Čech
complex. -/
def nearIdentityTransition
    (D : NearBaseMumford) :
    N13FormalLineBundleCech.NearIdentityTransition :=
  N13FormalCurveOverlap.transitionOfUnit
    (transitionUnit D) (reduce_transitionUnit D)
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The fixed base transition written in overlap coordinates. -/
def baseOverlap : Overlap :=
  N13FormalCurveOverlap.toOverlap
    (N13MumfordFormalTransition.baseFormalPolyUnit : FormalCurve)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restore the fixed base denominator in an arbitrary near-identity
transition displacement. -/
def weightedDeviationOfTransition
    (g : N13FormalLineBundleCech.NearIdentityTransition) : Overlap :=
  N13FormalLineBundleCech.mulOverlap g.deviation baseOverlap
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
/-- The actual transition attached to a two-disk divisor. -/
def diskTransition (P : DiskPair) :
    N13FormalLineBundleCech.NearIdentityTransition :=
  N13MumfordFormalTransition.nearIdentityTransition
    (N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair P)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Restrict rational-to-two-adic Picard base change to a subgroup. -/
def subgroupToPic
    (H : AddSubgroup RationalPic) :
    H →+ Pic₂ :=
  N13InfinityBaseChange.picMapRatToQ₂.comp H.subtype
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT
/-- The two-adic integer coefficient ring of the Abel chart. -/
abbrev R₂ : Type :=
  ℤ_[2]
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- A kernel-indexed family of smooth integral graphs reducing to the
selected nonspecial quadratic graph.

The stored equality is centered at the distinguished base divisor, exactly
as required by the Abel chart.  Hensel recovery will turn each graph into a
unique ordered disk pair without any additional choice compatibility. -/
structure NearBaseFamily
    (H : AddSubgroup RationalPic) where
  graph : H → NearBaseMumford
  realize_graph :
    ∀ z,
      (graph z).centeredPic =
        N13TwoAdicAbelChartSection.subgroupToPic H z
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
/-- Recover the unique ordered pair of Hensel roots from each near-base
integral graph. -/
def pair
    (F : NearBaseFamily H) :
    H → DiskPair :=
  fun z => (F.graph z).diskPair
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT
/-- A balanced quadratic representative of a centered two-adic Picard
class whose canonical contraction has the literal selected special graph.

The represented uncentered class is translated by `basePic`.  This
translation is forced because disk-pair coordinates are centered at the
distinguished base divisor. -/
structure MappedSpecialRepresentative
    (c : Pic₂) where
  mumford : SexticMumford.Mumford Model₂
  class_eq :
    SexticMumford.classOf
        Model₂ (N13Infinity.positiveInfinityOrder ℚ_[2])
        mumford =
      c + basePic
  map_contract_eq_special :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal
            mumford.toSemi)) =
      N13SpecialQuotientBasis.specialIdeal
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
/-- The two integral Abel-chart coordinates of the recovered disk pair. -/
def coord
    (F : NearBaseFamily H) :
    H → Fin 2 → R₂ :=
  fun z =>
    N13TwoAdicAbelChartData.DiskPair.coord (F.pair z)
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
/-- The weighted first jet of the tensor square of the actual formal
transition attached to the selected disk representative of `z`. -/
def squareJet
    (F : NearBaseFamily H) (z : H) :
    Fin 2 → R₂ :=
  N13MumfordFormalTransitionJet.firstJet
    (N13MumfordFormalTransitionJet.weightedDeviationOfTransition
      (N13MumfordFormalTransitionJet.diskTransition
        (F.pair z)).square)
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
def quad (a₀ a₁ : R₂) : R₂[X] := X ^ 2 + _root_.Polynomial.C a₁ * X + _root_.Polynomial.C a₀
end
end MazurProof.N13HermiteResidualDivisibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
def lin (b₀ b₁ : R₂) : R₂[X] := _root_.Polynomial.C b₀ + _root_.Polynomial.C b₁ * X
end
end MazurProof.N13HermiteResidualDivisibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
abbrev Kernel := specialization.ker
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredPrincipalNumerator
noncomputable section
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Dot-notation bridge: `P.mumford` for `P : N13TwoAdicAbelChartData.DiskPair`
is the chart-Pic Mumford representative (definitionally the same function). -/
abbrev _root_.MazurProof.N13TwoAdicAbelChartData.DiskPair.mumford
    (P : N13TwoAdicAbelChartData.DiskPair) :=
  N13TwoAdicAbelChartPic.DiskPair.mumford P
end
end MazurProof.N13CenteredPrincipalNumerator
end
end


