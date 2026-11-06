-- Prove2me | Definitions.Def_SKAnnealing_Sampling_gibbsOf
-- name    : SKAnnealing_Sampling_gibbsOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:22.785903+00:00
-- url     : https://prove2.me/theorems/94628c0f-7500-4733-aed0-14d0a3a94b92
-- title:
--   Gibbs distribution $\mu_{\beta H}$ of a Hamiltonian, and $H_{\max}$, $H_{\min}$
-- statement:
--   For a Hamiltonian $H:\{\pm1\}^N\to\mathbb R$ and an inverse temperature $\beta\in\mathbb R$, the **Gibbs distribution** is
--   $$\mu_{\beta H}(x)=\frac{\exp(\beta H(x))}{\sum_y\exp(\beta H(y))}.$$
--   $H_{\max}$ and $H_{\min}$ are the largest and smallest values of $H$ on the cube.
--
--   This is the general setting of Section 2.2, in which simulated annealing is analysed. For $H(\sigma)=\tfrac12\langle\sigma,W\sigma\rangle$ (zero diagonal), $\mu_{\beta H}$ is the SK measure $\mu_{\beta W}$ of (1), i.e. the published `OAI.CriticalSK.gibbs (β • W)`.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), §2.2, p. 11

import Mathlib
import Definitions.Def_CriticalSK

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- The Gibbs distribution `µ_{βH}(x) ∝ exp(β H(x))` of a Hamiltonian `H : {±1}^N → ℝ`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), §2.2, p. 11.

**Formalization Note** `gibbsOf (hamiltonian W) β = gibbs (β • W)` (verification file): with
`H = hamiltonian W = ½⟨σ, Wσ⟩` (zero diagonal, reading R8) this is the SK measure (1). -/
noncomputable def gibbsOf {N : ℕ} (H : Spin N → ℝ) (β : ℝ) (x : Spin N) : ℝ :=
  Real.exp (β * H x) / ∑ y : Spin N, Real.exp (β * H y)

/-- `H_max`: the maximum of `H` over the (finite, nonempty) cube. -/
noncomputable def hMax {N : ℕ} (H : Spin N → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty H

/-- `H_min`: the minimum of `H` over the cube. -/
noncomputable def hMin {N : ℕ} (H : Spin N → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty H

end SKAnnealing.Sampling


