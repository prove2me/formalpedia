-- Prove2me | Definitions.Def_OAIQWSIFPK000
-- name    : OAIQWSIFPK000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:16:53.066365+00:00
-- url     : https://prove2.me/theorems/6f913300-e292-4b53-a0b3-1ffb53cce105
-- title:
--   Ellipse maps and disk automorphisms for the classical univalent-function theorems (OpenAI strict inverse-first-power split)
-- statement:
--   Three small definitions from OpenAI's Lean development for *A strict inverse-first-power bound for univalent functions* (OpenAI Math Release, September 24, 2026, result family 072, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. They are used inside the proofs of the four classical statements of this split (Koebe one-quarter theorem, Bieberbach's $|a_2| \le 2$, Gronwall's coefficient bound $|b_1| \le 1$, and the Koebe distortion theorem). None of those statements mentions them.
--
--   All three live in the namespace `OAI.StrictInverseFirstPower`.
--   - `ellipseLinear c` is the real-linear map $\mathbb C \to \mathbb C$, $z \mapsto z + c\,\bar z$ (as a continuous $\mathbb R$-linear map, `1 + c • Complex.conjCLE`). When $|c| < 1$ it maps circles about $0$ onto ellipses.
--   - `ellipseInverse c z` is $(z - c\,\bar z)/(1 - |c|^2)$, the inverse of `ellipseLinear c` when $|c| < 1$.
--   - `diskAutomorphism a z` is $(a + z)/(1 + \bar a z)$. When $|a| < 1$ it is a conformal automorphism of the unit disk sending $0$ to $a$.
--
--   The bundle also contains OpenAI's two `@[simp]` lemmas about them: `ellipseLinear_apply` ($\texttt{ellipseLinear}\ c\ z = z + c\,\bar z$, by definition) and `diskAutomorphism_zero` ($\texttt{diskAutomorphism}\ a\ 0 = a$). It imports only Mathlib.
--
--   The larger definitions bundle of the same development, which carries the main proof's definitions, imports this bundle instead of repeating these declarations.
-- source:
--   OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/StrictMeans (AreaCoefficients.lean, DiskAutomorphisms.lean) at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

def ellipseLinear (c : ℂ) : ℂ →L[ℝ] ℂ :=
  1 + c • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] lemma ellipseLinear_apply (c z : ℂ) : ellipseLinear c z = z + c * conj z := rfl

def ellipseInverse (c z : ℂ) : ℂ := (z - c * conj z) / (1 - ‖c‖ ^ 2 : ℝ)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiskAutomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def diskAutomorphism (a z : ℂ) : ℂ := (a + z) / (1 + conj a * z)

@[simp] lemma diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by simp [diskAutomorphism]

end
end StrictInverseFirstPower

end

end OAI
end


