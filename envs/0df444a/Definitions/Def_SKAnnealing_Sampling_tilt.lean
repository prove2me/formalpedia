-- Prove2me | Definitions.Def_SKAnnealing_Sampling_tilt
-- name    : SKAnnealing_Sampling_tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:30.980586+00:00
-- url     : https://prove2.me/theorems/4cc8f684-6b71-460d-8593-c7f5dcd998ab
-- title:
--   Exponential tilt of a law on $\{\pm1\}^N$ by an external field
-- statement:
--   For a law $p$ on $\{\pm1\}^N$ and a field $z\in\mathbb R^N$, the **tilt** of $p$ by $z$ is the law
--   $$p^{z}(y)=\frac{p(y)\,e^{\langle z,y\rangle}}{\sum_x p(x)\,e^{\langle z,x\rangle}},$$
--   where a configuration $y$ is read as a vector of $\pm1$ entries.
--
--   Stochastic localization started at $\mu$ has an explicit form ([EM22], p. 3): draw $\sigma\sim\mu$ and a Brownian motion $(B_t)$; the measure at time $t$ is the posterior of $\sigma$ given $t\sigma+B_t$, which is the tilt $\mu^{\,t\sigma+B_t}$ (display (4)). The measures of Theorem 1.4 are tilts of the planted SK model.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), displays (3)–(4), p. 3; Theorem 1.4, p. 4

import Mathlib
import Definitions.Def_CriticalSK

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- A configuration as a vector of `±1` entries in `ℝ^N`. -/
noncomputable def spinVec {N : ℕ} (x : Spin N) : Fin N → ℝ :=
  fun i => spinValue (x i)

/-- The **exponential tilt** of a law `p` on `{±1}^N` by an external field `z ∈ ℝ^N`:
`tilt p z (y) ∝ p(y) exp⟨z, y⟩`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), displays (3)–(4), p. 3; Theorem 1.4, p. 4.

**Formalization Note** Reading R6: stochastic localization from `µ` at time `t` is the posterior of
`σ ∼ µ` given `tσ + B_t` ([EM22], p. 3), i.e. `tilt µ (t σ + B_t)` (the factor `exp(−t‖y‖²/2)` is
constant on the cube). -/
noncomputable def tilt {N : ℕ} (p : Spin N → ℝ) (z : Fin N → ℝ) (y : Spin N) : ℝ :=
  p y * Real.exp (∑ i, z i * spinVec y i) /
    ∑ x : Spin N, p x * Real.exp (∑ i, z i * spinVec x i)

end SKAnnealing.Sampling


