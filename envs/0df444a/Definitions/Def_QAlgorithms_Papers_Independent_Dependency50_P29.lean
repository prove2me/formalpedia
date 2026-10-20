-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29
-- name    : QAlgorithms_Papers_Independent_Dependency50_P29
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:27:57.486993+00:00
-- url     : https://prove2.me/theorems/6197495e-d61b-4b95-b470-52c4698d7163
-- title:
--   Definitions for Energy-constrained private and quantum capacities of quantum channels
-- statement:
--   The objects the formalized statements of *Energy-constrained private and quantum capacities of quantum channels* (arXiv:1609.01997) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `lossFormula`: PDF p.23, Eq.(331): the displayed pure-loss coherent-information expression. This scalar definition is not an operational capacity definition.
--   - `amplifierFormula`: PDF p.24, Eq.(333): the displayed quantum-limited amplifier expression. This scalar definition is not an operational capacity definition.
-- source:
--   Energy-constrained private and quantum capacities of quantum channels, arXiv:1609.01997v2, https://arxiv.org/abs/1609.01997v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

/-!
Statements from Wilde--Qi, arXiv:1609.01997v2.
The separable-space channel and operational capacity interfaces are deferred explicitly
in this paper's GAPS.json. The scalar limits below concern the displayed functions,
not a definition of any operational capacity. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.23, Eq.(331): the displayed pure-loss coherent-information expression.
This scalar definition is not an operational capacity definition. -/
def lossFormula (eta occupation : ℝ) : ℝ :=
  thermalEntropy (eta * occupation) - thermalEntropy ((1 - eta) * occupation)

/-- PDF p.24, Eq.(333): the displayed quantum-limited amplifier expression.
This scalar definition is not an operational capacity definition. -/
def amplifierFormula (gain occupation : ℝ) : ℝ :=
  thermalEntropy (gain * occupation + gain - 1) -
    thermalEntropy ((gain - 1) * (occupation + 1))

example : thermalEntropy 0 = 0 := by
  simp [thermalEntropy]

example (eta : ℝ) : lossFormula eta 0 = 0 := by
  simp [lossFormula]

example (occupation : ℝ) : amplifierFormula 1 occupation = thermalEntropy occupation := by
  simp [amplifierFormula, thermalEntropy]

end QAlgorithms.Papers.Independent.Dependency50.P29


