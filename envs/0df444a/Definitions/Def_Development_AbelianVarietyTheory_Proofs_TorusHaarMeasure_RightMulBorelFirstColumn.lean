-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:42:41.541942+00:00
-- url     : https://prove2.me/theorems/5fa58481-1fb4-4bea-b956-0e6b7a17a957
-- title:
--   Right Mul Borel First Column
-- statement:
--   Definitions and structural lemmas for Right Mul Borel First Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
namespace GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def colSq {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) : ℝ :=
  ‖x τ 0 0‖ ^ 2 + ‖x τ 1 0‖ ^ 2
noncomputable def idx (X : Data E 2) (τ : X.Ψ) : Fin (nd X) :=
  Fintype.equivFin (Ent X) ⟨τ, ⟨(1, 0), by decide⟩⟩
end GlobalTheory.TwoLines


