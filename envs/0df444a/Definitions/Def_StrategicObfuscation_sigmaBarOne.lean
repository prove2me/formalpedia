-- Prove2me | Definitions.Def_StrategicObfuscation_sigmaBarOne
-- name    : StrategicObfuscation_sigmaBarOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:04.578376+00:00
-- url     : https://prove2.me/theorems/6788fc31-2156-41eb-9e34-4dafbd32e807
-- title:
--   The threshold $\bar\sigma_1$
-- statement:
--   The threshold $\bar\sigma_1$ is the largest resource level below which the applicant does not obfuscate even when uncertified proposals are funded for sure:
--
--   $$\bar\sigma_1=\sup\{\sigma\in[0,1] : e(1,s)=0\ \text{for all } 0\le s<\sigma\}.$$
--
--   **Formalization Note** The set contains $0$ and is bounded by $1$, so the supremum is genuine.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3, p.11

import Mathlib

open Set

namespace StrategicObfuscation

/-- **The threshold `σ̄1`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3, p.11 (PDF p.11): "σ̄1 is defined as the maximum value
of σ such that the solution to (1) is e∗ = 0 for all σ < σ̄1."

**Formalization Note** The supremum is taken over `σ ∈ [0, 1]` with `E 1 s = 0` for all `0 ≤ s < σ`.
That set contains `0` vacuously and is bounded by `1`, so `sSup` is a genuine supremum. `E 1` is
monotone (milestone M1), so the set is an interval and its supremum is the paper's maximum. -/
noncomputable def sigmaBarOne (E : ℝ → ℝ → ℝ) : ℝ :=
  sSup {σ ∈ Icc (0 : ℝ) 1 | ∀ s ∈ Ico (0 : ℝ) σ, E 1 s = 0}

end StrategicObfuscation


