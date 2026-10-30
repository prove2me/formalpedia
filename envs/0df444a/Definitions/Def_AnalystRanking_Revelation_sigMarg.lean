-- Prove2me | Definitions.Def_AnalystRanking_Revelation_sigMarg
-- name    : AnalystRanking_Revelation_sigMarg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:30:22.878376+00:00
-- url     : https://prove2.me/theorems/58d52d6c-d477-46f4-a520-8790976c5c0d
-- title:
--   Marginal signal law $\Pr(s\mid\omega)$
-- statement:
--   Each analyst's private signal $s\in\{h,l\}$ has precision $\gamma$:
--   $$\Pr(s\mid\omega)=\begin{cases}\gamma,& s \text{ matches } \omega,\\ 1-\gamma,&\text{otherwise}.\end{cases}$$
--
--   This is the precision $\gamma=\Pr(s_i=\omega\mid\omega)\in(\tfrac12,1)$ of §2 (p. 6).
--
--   **Formalization Note** Signals and states are both `Bool` (`true` $=h$, `true` $=H$), so "matches" is equality.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6

import Mathlib

namespace AnalystRanking.Revelation

/-- **Marginal signal law, `Pr(s | ω)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6: each analyst receives a private signal `s_i ∈ {h, l}` of precision
"`γ = Pr(s_i = ω | ω) ∈ (1/2, 1)`".

`sigMarg γ ω s` is `Pr(s_i = s | ω)`: `γ` if the signal matches the state, `1 − γ` otherwise.

**Formalization Note.** Signals `{h, l}` and states `{H, L}` are both encoded as `Bool`
(`true = h`, `true = H`), so "the signal matches the state" is `s = ω`. -/
noncomputable def sigMarg (γ : ℝ) (ω s : Bool) : ℝ :=
  if s = ω then γ else 1 - γ

end AnalystRanking.Revelation


