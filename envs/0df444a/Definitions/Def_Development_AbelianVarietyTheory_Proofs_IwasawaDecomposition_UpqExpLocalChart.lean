-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:35.104331+00:00
-- url     : https://prove2.me/theorems/b423c5c0-fbb7-48a5-89fe-4de2b653ac98
-- title:
--   Upq Exp Local Chart
-- statement:
--   Definitions and structural lemmas for Upq Exp Local Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqExpLocalChart.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
namespace GlobalTheory.ExpBallSandwich
section Matrices
variable {n : Type} [Fintype n] [DecidableEq n]
noncomputable def sumAbs (M : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖
section Op
open scoped Matrix.Norms.Operator
end Op
end Matrices
end GlobalTheory.ExpBallSandwich


