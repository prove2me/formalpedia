-- Prove2me | Definitions.Def_CPDETrial_muT
-- name    : CPDETrial_muT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:26.06968+00:00
-- url     : https://prove2.me/theorems/e289a19a-5920-4977-8e50-08781c71b5ce
-- title:
--   Posterior mean $\mu^T$ along the realized trial
-- statement:
--   $\mu^t(\omega)$ is the posterior mean of eq. (8) after the first $t$ patients, computed from the prior $(\mu^0,\Sigma^0)$ along the realized allocations $u^s(\omega)$ and observations $Y^{s+1}_{u^s}(\omega)$, $s<t$.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 6 (§1.3) and p. 9, eq. (8)

import Mathlib
import Definitions.Def_CPDETrial_postMean
import Definitions.Def_CPDETrial_obs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The posterior mean `µ^T` along the realized trial.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.3 (p. 6) and eq. (8) (p. 9).

`muT mu0 Sig0 lam θ ε u t ω` is `µ^t(ω)`: the recursion (8) run from the prior `(µ⁰, Σ⁰)` along
the realized allocations `u^s(ω)` and observations `Y^{s+1}_{u^s}(ω)`, `s < t`. -/
noncomputable def muT {M : ℕ} {Ω : Type*} (mu0 : Fin M → ℝ) (Sig0 : Matrix (Fin M) (Fin M) ℝ)
    (lam : Fin M → ℝ≥0) (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ)
    (u : ℕ → Ω → Fin M) (t : ℕ) (ω : Ω) : Fin M → ℝ :=
  postMean mu0 Sig0 lam (fun s => u s ω) (fun s => obs θ ε u s ω) t

end CPDETrial


