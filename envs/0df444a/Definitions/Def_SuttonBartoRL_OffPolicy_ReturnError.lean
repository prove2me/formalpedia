-- Prove2me | Definitions.Def_SuttonBartoRL_OffPolicy_ReturnError
-- name    : SuttonBartoRL_OffPolicy_ReturnError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:21:22.439988+00:00
-- url     : https://prove2.me/theorems/3fd1af35-e74f-4df8-a15a-4a88e52fb9c7
-- title:
--   Mean square value error VE and mean square return error RE
-- statement:
--   Let $\mathcal S$ be a finite set of states with weighting $\mu$. For an estimate $\hat v:\mathcal S\to\mathbb R$ (the approximate value function $\hat v(\cdot,\mathbf w)$ at a fixed weight vector) and a target value function $v$, the **mean square value error** (9.1) is
--   $$\mathrm{VE} = \sum_{s\in\mathcal S}\mu(s)\,\bigl[v(s) - \hat v(s)\bigr]^2 .$$
--   If, given $S_t = s$, the return $G_t$ has distribution $\nu_s$ on $\mathbb R$, and $S_t\sim\mu$, the **mean square return error** of (11.24) is
--   $$\mathrm{RE} = \mathbb E\bigl[(G_t - \hat v(S_t))^2\bigr] = \sum_{s\in\mathcal S}\mu(s)\int (g - \hat v(s))^2\,d\nu_s(g).$$
--
--   The RE is observable from data, while the VE needs the true value function; (11.24) relates the two.
--
--   **Formalization Note** The return is modelled only through its conditional distributions $\nu_s$; the theorem that uses these objects assumes each $\nu_s$ is a probability measure with finite second moment, so the integrals are genuine (a Bochner integral of a non-integrable function would be $0$).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, (9.1) p. 199; (11.24) p. 275

import Mathlib

open MeasureTheory

namespace SuttonBartoRL.OffPolicy

variable {S : Type} [Fintype S]

/-- (9.1), p. 199, recalled on p. 266: the mean square value error of an estimate `v̂ : S → ℝ`
(the approximate value function `v̂(·, w)` at a fixed weight vector `w`) against the true value
function `v`, `VE = Σ_{s ∈ S} µ(s) [v(s) − v̂(s)]²`. -/
def VE (μ : S → ℝ) (v : S → ℝ) (vhat : S → ℝ) : ℝ :=
  ∑ s, μ s * (v s - vhat s) ^ 2

/-- (11.24), first line, p. 275: the mean square return error
`RE = E[(G_t − v̂(S_t))²]` when `S_t ∼ µ` and, given `S_t = s`, the return `G_t` has distribution
`ν s` (a probability measure on `ℝ`):
`RE = Σ_{s ∈ S} µ(s) ∫ (g − v̂(s))² dν_s(g)`. -/
noncomputable def RE (μ : S → ℝ) (ν : S → Measure ℝ) (vhat : S → ℝ) : ℝ :=
  ∑ s, μ s * ∫ g, (g - vhat s) ^ 2 ∂(ν s)

end SuttonBartoRL.OffPolicy


