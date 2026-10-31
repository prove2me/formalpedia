-- Prove2me | Definitions.Def_HuangN13_InfinityGraphLineCore
-- name    : HuangN13_InfinityGraphLineCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:57:04.451115+00:00
-- url     : https://prove2.me/theorems/028fdfcc-6a07-430a-8219-1c8b9c9d651b
-- title:
--   Actual integral infinity graph lines and their special root divisors
-- statement:
--   The original actual two-chart line of bounded integral infinity graph data and the special root divisor, including exactly their construction dependencies.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_MazurProof_N13IntegralGraphJacobian_graphIdeal_isUnit
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphJacobian_graphIdeal_isUnit
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_curveEquationAtRoot
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_degreeTwo_splits

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClassHom (p : R₂[X]) :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      affineCoeffMap p :=
  affineToInfinityOverlap_of p
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_generalized_yClass :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      affineYImage :=
  affineToInfinityOverlap_yClass
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def infinityIdeal (D : GraphData) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    N13IntegralInfinityGraphJacobian.xClassHom
    N13IntegralInfinityGraphJacobian.yClass
    D.u D.v
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def affineIdeal
    (D : GraphData) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  GeneralizedGraphIdealCore.graphIdeal
    N13GeneralizedMumfordIntegral.xClassHom
    N13GeneralizedMumfordIntegral.yClass
    (affineU D) (affineV D)
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityIdeal_isUnit
    (D : GraphData)
    (hu : D.u ≠ 0) :
    IsUnit (infinityIdeal D : InfinityFractionalIdeal) := by
  exact
    N13IntegralInfinityGraphJacobian.graphIdeal_isUnit D hu
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem affineIdeal_isUnit
    (D : GraphData)
    (hdu : D.u.natDegree ≤ 2)
    (hdv : D.v.natDegree ≤ 3)
    (hdw : D.w.natDegree ≤ 4)
    (hu : D.u ≠ 0) :
    IsUnit
      (affineIdeal D :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  exact
    N13IntegralGraphJacobian.graphIdeal_isUnit
      (affineGraphData D hdu hdv hdw)
      (affineU_ne_zero D hu)
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affineU_on_overlap
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (affineU D)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
            (N13IntegralInfinityGraphJacobian.xClassHom D.u) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    show affineU D = D.u.reflect 2 by rfl,
    reflect_on_overlap 2 D.u hu, xClassHom_on_overlap]
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affineV_on_overlap
    (D : GraphData)
    (hv : D.v.natDegree ≤ 3) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (GeneralizedGraphIdealCore.ySubClass
          N13GeneralizedMumfordIntegral.xClassHom
          N13GeneralizedMumfordIntegral.yClass
          (affineV D)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
            (GeneralizedGraphIdealCore.ySubClass
              N13IntegralInfinityGraphJacobian.xClassHom
              N13IntegralInfinityGraphJacobian.yClass
              D.v) := by
  simp only [GeneralizedGraphIdealCore.ySubClass, map_sub,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  rw [show affineV D = D.v.reflect 3 by rfl,
    reflect_on_overlap 3 D.v hv, xClassHom_on_overlap]
  simp only [N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.yClass,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.vOverlap]
  ring
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine weighted closure and the integral infinity graph define the
same ideal on the Laurent overlap. -/
theorem ideals_agree_on_overlap
    (D : GraphData)
    (hu : D.u.natDegree ≤ 2)
    (hv : D.v.natDegree ≤ 3) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineIdeal D) =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        (infinityIdeal D) := by
  simp only [affineIdeal, infinityIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    Ideal.map_span, Set.image_pair]
  rw [affineU_on_overlap D hu, affineV_on_overlap D hv]
  let ux :
      N13OrdinaryCurveOverlap.InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hux2 :
      ((ux ^ 2 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 2 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 2 =
        N13OrdinaryCurveOverlap.xOverlap ^ 2
    rw [hux]
  have hux3 :
      ((ux ^ 3 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 3 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 3 =
        N13OrdinaryCurveOverlap.xOverlap ^ 3
    rw [hux]
  have hs :=
    span_pair_unit_mul
      (ux ^ 2) (ux ^ 3)
      ((algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap)
          (N13IntegralInfinityGraphJacobian.xClassHom D.u))
      ((algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap)
          (GeneralizedGraphIdealCore.ySubClass
            N13IntegralInfinityGraphJacobian.xClassHom
            N13IntegralInfinityGraphJacobian.yClass D.v))
  rw [hux2, hux3] at hs
  exact hs
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A bounded nonzero integral infinity graph gives a root-free invertible
line on the two ordinary integral charts. -/
def twoChartLine
    (D : GraphData)
    (hdu : D.u.natDegree ≤ 2)
    (hdv : D.v.natDegree ≤ 3)
    (hdw : D.w.natDegree ≤ 4)
    (hu : D.u ≠ 0) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := affineIdeal D
  infinityIdeal := infinityIdeal D
  affine_isUnit := affineIdeal_isUnit D hdu hdv hdw hu
  infinity_isUnit := infinityIdeal_isUnit D hu
  overlap_eq := ideals_agree_on_overlap D hdu hdv
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- A monic integral quadratic retains degree two after reduction. -/
theorem reduceGraphData_u_natDegree
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2) :
    (reduceGraphData E hu).u.natDegree = 2 := by
  change
    (E.u.map
      N13IntegralInfinityReduction.reduceBase).natDegree = 2
  rw [hu.natDegree_map, hdeg]
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- The two roots of a split infinity graph form an unordered pair. -/
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
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- The canonical unordered pair of roots of a special infinity graph. -/
noncomputable def rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    Sym2 K :=
  Classical.choose (exists_rootPair D hdeg)
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- The multiset underlying the chosen root pair is the polynomial root
multiset. -/
theorem rootPair_toMultiset
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    (rootPair D hdeg).toMultiset = D.u.roots :=
  Classical.choose_spec (exists_rootPair D hdeg)
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- Membership in the chosen root pair is equivalent to vanishing of the
horizontal polynomial. -/
theorem mem_rootPair_iff_isRoot
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) (a : K) :
    a ∈ rootPair D hdeg ↔ D.u.IsRoot a := by
  rw [← Sym2.mem_toMultiset, rootPair_toMultiset,
    Polynomial.mem_roots D.u_monic.ne_zero]
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- Complete an infinity-graph root to the special curve: `t = 0` is a
point at infinity and the nonzero root `t = 1` lies on the affine overlap. -/
noncomputable def rootPoint
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (a : K) (ha : a ∈ rootPair D hdeg) :
    N13SpecialDivisorCharts.CurvePoint :=
  if ha0 : a = 0 then
    Sum.inr
      ⟨D.v.eval a, by
        subst a
        exact curveEquationAtRoot D
          ((mem_rootPair_iff_isRoot D hdeg 0).mp ha)⟩
  else
    Sum.inl
      ⟨(1, D.v.eval a), by
        have ha1 : a = 1 :=
          (N13GoodModelTwo.fixedTwo_eq_zero_or_one
            a (ZMod.pow_card a)).resolve_left ha0
        subst a
        simpa using
          (N13GoodModelTwo.affine_iff_infinity_on_overlap
            (show (1 : K) * 1 = 1 by simp)).mpr
            (curveEquationAtRoot D
              ((mem_rootPair_iff_isRoot D hdeg 1).mp ha))⟩
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
/-- The effective degree-two divisor consisting of the two completed graph
roots. -/
noncomputable def graphDivisor
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  Sym2.pmap (rootPoint D hdeg) (rootPair D hdeg)
    (fun _ ha => ha)
end
end MazurProof.N13SpecialInfinityGraphDivisor
end
end


