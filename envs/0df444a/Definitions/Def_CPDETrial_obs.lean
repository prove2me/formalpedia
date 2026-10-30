-- Prove2me | Definitions.Def_CPDETrial_obs
-- name    : CPDETrial_obs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:50:07.130118+00:00
-- url     : https://prove2.me/theorems/cd7a1143-1be6-4002-bec5-d9ead8c70f4a
-- title:
--   The observation following an allocation
-- statement:
--   With unknown means $\theta$, sampling errors $\varepsilon^t_i$ and allocations $u^t$, the observation of patient $t+1$ is
--
--   $$
--   Y^{t+1}_{u^t}=\theta_{u^t}+\varepsilon^{t+1}_{u^t}.
--   $$
--
--   **Formalization Note** The paper's model $Y^t_i\mid\theta\sim N(\theta_i,\lambda_i)$, independent given $\theta$, is encoded with errors $\varepsilon^t_i\sim N(0,\lambda_i)$ that are independent and independent of $\theta$; the joint law is the same.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), pp. 6–7, §1.2–1.3

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The observation that follows an allocation.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.2–1.3, pp. 6–7: `Y^t_i | θ_i ∼ N(θ_i, λ_i)`; "After an action `u^t` … is chosen, the
observation `Y^{t+1}_{u^t}` is realized before the next period's decision".

With unknown means `θ`, sampling errors `ε t i` (so that `Y^t_i = θ_i + ε t i`) and a random
allocation sequence `u`, `obs θ ε u t ω = θ_{u^t}(ω) + ε^{t+1}_{u^t}(ω) = Y^{t+1}_{u^t}(ω)`.

**Formalization Note.** The paper's conditional model `Y^t_i | θ ∼ N(θ_i, λ_i)`, independent
given `θ`, is encoded as `Y^t_i = θ_i + ε^t_i` with independent errors `ε^t_i ∼ N(0, λ_i)`
independent of `θ` (see `TrialModel`); this gives the same joint law. `ε 0 ·` is unused. -/
noncomputable def obs {M : ℕ} {Ω : Type*} (θ : Ω → EuclideanSpace ℝ (Fin M))
    (ε : ℕ → Fin M → Ω → ℝ) (u : ℕ → Ω → Fin M) (t : ℕ) (ω : Ω) : ℝ :=
  θ ω (u t ω) + ε (t + 1) (u t ω) ω

end CPDETrial


