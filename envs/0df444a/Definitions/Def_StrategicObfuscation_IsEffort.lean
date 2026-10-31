-- Prove2me | Definitions.Def_StrategicObfuscation_IsEffort
-- name    : StrategicObfuscation_IsEffort
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:08.427079+00:00
-- url     : https://prove2.me/theorems/88f2cadd-4788-4a04-abdb-cee9b9763b16
-- title:
--   Effort selection $e(\alpha,\sigma)$
-- statement:
--   A function $E$ of $(\alpha,\sigma)$ is an **effort selection** for the return $g$ when $E(\alpha,\sigma)$ is a best response (1) for all $\alpha,\sigma\in[0,1]$. This is the paper's $e(\alpha,\sigma)$, in which $g$ is omitted.
--
--   **Formalization Note** The argmax in (1) need not be a singleton, so all statements fix one selection $E$, used consistently in the equilibrium and in the thresholds $\bar\sigma_1,\bar\sigma_2$. That a maximizer exists is part of this hypothesis.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), eq. (1), p.10

import Mathlib
import Definitions.Def_StrategicObfuscation_IsBestResponse

open Set

namespace StrategicObfuscation

/-- **The effort selection `e(α, σ)` of (1).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), eq. (1), p.10 (PDF p.10): "For the sake of notation, we
omit g and simply write e(α, σ)."

`E` is an effort selection for the return `g` when `E α σ` solves (1) for all `α, σ ∈ [0, 1]`.

**Formalization Note** The paper treats `e(α, σ)` as a function. The Lean statements fix one selection
`E` and use it everywhere: in the equilibrium, in `σ̄1` and in `σ̄2`. That a maximizer exists is part
of this hypothesis, exactly as (1) presumes it. -/
def IsEffort (π : ℝ → ℝ → ℝ) (g : ℝ) (E : ℝ → ℝ → ℝ) : Prop :=
  ∀ α ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (0 : ℝ) 1, IsBestResponse π g α σ (E α σ)

end StrategicObfuscation


