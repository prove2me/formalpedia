-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:29.422798+00:00
-- url     : https://prove2.me/theorems/39b9cf80-9969-4cd9-911c-3f1955f42cba
-- title:
--   PChart Max Ideals
-- statement:
--   Definitions and structural lemmas for PChart Max Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}
theorem chartIncIdeal_eq_sup {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    chartIncIdeal W t e = chartIncIdeal I t e ⊔ W.map (rename Sum.inl) := by
  unfold chartIncIdeal
  apply le_antisymm
  · refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw [Ideal.map_sup]
    exact sup_le le_sup_right (((Ideal.map_mono le_sup_right).trans le_sup_left).trans le_sup_left)
  · refine sup_le (sup_le ?_ le_sup_right) ?_
    · exact (Ideal.map_mono (sup_le_sup_right h _)).trans le_sup_left
    · exact (Ideal.map_mono le_sup_left).trans le_sup_left
theorem chartIncIdeal_le {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    chartIncIdeal I t e ≤ chartIncIdeal W t e :=
  le_sup_left.trans_eq (chartIncIdeal_eq_sup h t).symm
def toSub {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) (e : ℕ) :
    ChartInc I t e →+* ChartInc W t e :=
  Ideal.Quotient.factor (chartIncIdeal_le h t)
end ChartMaxIdeals
end
end GroundTheory.Heights₂.Heights


