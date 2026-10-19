-- Prove2me | Definitions.Def_OAIQWZT001
-- name    : OAIQWZT001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:28:46.59127+00:00
-- url     : https://prove2.me/theorems/ad84a36c-d9f4-49fc-b4b9-78005e7669bd
-- title:
--   OpenAI zero-temperature SK split: definitions bundle 2 (heat-equation lemmas)
-- statement:
--   The second of three definitions bundles of the split of OpenAI's proof of `OAI.ZeroTemperatureSK.full_support`. It holds OpenAI's Lean definitions from `lean/OAI/Probability/SKSupport` (OpenAI, *Full support of the zero-temperature Sherrington-Kirkpatrick order parameter*, OpenAI Math Release, September 27, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. It holds two of OpenAI's lemmas from `Foundations/ExponentialBoundLipschitz.lean` on the spatial derivatives of `Heat.varianceHeat` (`Heat.deriv_varianceHeat`, `Heat.deriv_deriv_varianceHeat`), which later definitions need. It imports the definitions bundle `OAIQWZT000`.
-- source:
--   OpenAI, Full support of the zero-temperature Sherrington-Kirkpatrick order parameter, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 281; Apache License 2.0); definitions carved from lean/OAI/Probability/SKSupport at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWZT000

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ExponentialBoundLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

namespace ZeroTemperatureSK.Heat

lemma deriv_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (t : ℝ) :
    deriv (varianceHeat t g) = varianceHeat t (deriv g) :=
  funext (fun x => (hasDerivAt_scaled_space hgc hg hg' (Real.sqrt t) x).deriv)

lemma deriv_deriv_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) (t : ℝ) :
    deriv (deriv (varianceHeat t g)) = varianceHeat t (deriv (deriv g)) := by
  rw [deriv_varianceHeat (hgc.of_le (by norm_num)) hg hg',
    deriv_varianceHeat (show ContDiff ℝ 1 (deriv g) from hgc.deriv') hg' hg'']

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end


