-- Prove2me | Definitions.Def_OAIQ073V002
-- name    : OAIQ073V002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:58:48.495367+00:00
-- url     : https://prove2.me/theorems/acf1202c-e559-4d26-bd28-fdb59196edda
-- title:
--   Definitions bundle OAIQ073V002 of the split of OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.RVM.unselectedLabelSignedForce`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`VlasovMaxwell_Retarded_SourceForceConeKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceForceConeKernel.lean).
--
--   **Imports.** It imports the published bundle `Def_VlasovMaxwell`; the bundle `OAIQ073V000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.RVM.Admissible.unselected_label_uniform`, `OAI.RVM.PhaseFlowOn.unselectedLabelSignedForce_integrable` and `OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition`; the proofs of `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform`, `OAI.RVM.Admissible.unselected_label_uniform`, `OAI.RVM.PhaseFlowOn.unselectedLabelSignedForce_integrable`, `OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound` and `OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition`.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceForceConeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def unselectedLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  (1-labelSelectedCutoff α zX T Q p) •
    (ψ (labelReceiverTime α zX T p) • actualLabelSignedForce s α zX T p)

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end


