-- Prove2me | Definitions.Def_GeneralCK_E8_reusable_cell_interface
-- name    : GeneralCK_E8_reusable_cell_interface
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:22:49.777463+00:00
-- url     : https://prove2.me/theorems/a38acdca-95ee-485d-b37f-e748e5e5f5c6
-- title:
--   Reusable E8 cell certificates and exact partition predicates
-- statement:
--   A cell certificate stores a rectangle, a center and interval Taylor data. AllLeaves records both positive leaf predicates and rational split points inside their parent rectangles. CellsPositive states that every rectangle in a list has E8 positivity. These preserve the original mathematical definitions; separate theorems establish certificate soundness and aggregation.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates Set GeneralCK.Certificates.DyadicInterval

section
namespace GeneralCK.Certificates.E8TAxisPartitionKernel

open GeneralCK









def Rect.leftS (r : Rect) (x : ℚ) : Rect := { r with s1 := x }
def Rect.rightS (r : Rect) (x : ℚ) : Rect := { r with s0 := x }
def Rect.lowerT (r : Rect) (x : ℚ) : Rect := { r with t1 := x }
def Rect.upperT (r : Rect) (x : ℚ) : Rect := { r with t0 := x }

def AllLeaves (P : Rect → Prop) : Tree → Rect → Prop
  | .leaf, r => P r
  | .splitS x left right, r =>
      r.s0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ r.s1 ∧
        AllLeaves P left (r.leftS x) ∧ AllLeaves P right (r.rightS x)
  | .splitT x lower upper, r =>
      r.t0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ r.t1 ∧
        AllLeaves P lower (r.lowerT x) ∧ AllLeaves P upper (r.upperT x)












end GeneralCK.Certificates.E8TAxisPartitionKernel
end

section
namespace GeneralCK.Certificates.E8TAxisCellCertificateSchema

open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients E8TAxisGeneralCenteredTaylor
open E8TAxisPartitionKernel

set_option maxHeartbeats 1000000



structure Certificate (p : ℕ) where
  rectangle : Rect
  centerS : ℝ
  centerT : ℝ
  data : Data p

namespace Certificate





end Certificate





end GeneralCK.Certificates.E8TAxisCellCertificateSchema
end

section
namespace GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

open E8TAxisPartitionKernel



def CellsPositive (rs : List Rect) : Prop := ∀ r ∈ rs, CellPositive r











end GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
end


