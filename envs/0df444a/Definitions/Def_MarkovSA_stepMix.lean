-- Prove2me | Definitions.Def_MarkovSA_stepMix
-- name    : MarkovSA_stepMix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:18.327986+00:00
-- url     : https://prove2.me/theorems/8b30af1e-03ae-41a9-aaa0-1fe92c06e304
-- title:
--   $t_k=t_{\alpha_k}$, the mixing time at precision $\alpha_k$
-- statement:
--   For stepsizes $(\alpha_k)$, $t_k=t_{\alpha_k}$ is the mixing time of the chain at precision $\alpha_k$:
--
--   $$
--   t_k=\min\Big\{m\ge0:\max_{y}\|P^m(y,\cdot)-\mu\|_{TV}\le\alpha_k\Big\}.
--   $$
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, Definition 2.1 and the sentence after it, p.6

import Mathlib
import Definitions.Def_mm_mixing

namespace MarkovSA

/-- `t_k = t_{α_k}`: the mixing time (Definition 2.1, Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.6) of the chain at precision `α_k`,
`t_δ = min{k ≥ 0 : max_y ‖P^k(y, ·) − μ‖_TV ≤ δ}` (platform `MarkovMixing.mixingTime`). -/
noncomputable def stepMix {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (α : ℕ → ℝ) (k : ℕ) : ℕ :=
  MarkovMixing.mixingTime P μ (α k)

end MarkovSA


