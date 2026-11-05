-- Prove2me | Definitions.Def_GoodProphets_loss
-- name    : GoodProphets_loss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:21.296585+00:00
-- url     : https://prove2.me/theorems/59b2d2f2-02dc-4e3f-a749-5fb976b547b9
-- title:
--   The loss $L_{\mathrm{ALG}}=\mathbb E[f_{\vec N}(\vec x^{\mathrm{ALG}})-\mathrm{OPT}(\vec N)]$, eq. (1)
-- statement:
--   The **loss** of an online algorithm, for an arrival distribution $\vec p$, a horizon $T$ and a heads-up time $\hat T$, is
--   $$
--   L_{\mathrm{ALG}}:=\mathbb E\Big[f_{\vec N}(\vec x^{\mathrm{ALG}})-\mathrm{OPT}(\vec N)\Big],\tag{1}
--   $$
--   the expected difference between the objective of the algorithm's final counts and that of a clairvoyant, who knows the whole sample path, including its length. The expectation is over the numbers of arrivals $\vec N$, over their order and over the algorithm's randomization. This is the performance measure of the paper: a loss bounded independently of $T$ is a **uniform loss** guarantee.
--
--   **Formalization Note** The expectation is a finite sum over trajectories, with the trajectory probabilities of `Policy`. $T$ and $\hat T$ are fixed numbers. The paper's random heads-up time, independent of the arrivals and chosen e.g. by an oblivious adversary, is covered by conditioning on it, because the goal bounds the loss uniformly in $T$ and $\hat T$. $\mathrm{OPT}(\vec N)$ is the fractional optimum over $\vec x\ge0$.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), §2, pp.8–9, "Performance Benchmark", eq. (1)

import Mathlib
import Definitions.Def_GoodProphets_lpObj
import Definitions.Def_GoodProphets_seqProb
import Definitions.Def_GoodProphets_Policy

namespace GoodProphets

/-- The loss (1) of an online algorithm (Banerjee & Freund, *Good prophets know when the end is
near*, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), §2, pp.8–9):

`L_ALG := E[f_N(x^ALG) − OPT(N)]`,

the expectation over the arrivals (their numbers `N` and their order) and over the algorithm's
randomization, for horizon `T` and heads-up time `T̂ = Th`.

**Formalization Note** The expectation is the finite sum over trajectories
`(θ⃗, a⃗) : (Fin T → Fin k) × (Fin T → Fin ℓ)` weighted by `trajWeight`. `N_θ` is the number of
type-`θ` arrivals cast to `ℝ`, and `OPT(N)` the fractional clairvoyant optimum over `x ≥ 0`. `T` and
`T̂` are fixed numbers; the paper's random `T̂` independent of the arrivals is covered by
conditioning, since the goal bounds the loss uniformly in `T` and `T̂`. -/
noncomputable def loss {k ℓ r m : ℕ} (I : Instance k ℓ r m) (π : Policy k ℓ) (p : Fin k → ℝ)
    (T Th : ℕ) : ℝ :=
  ∑ θs : Fin T → Fin k, ∑ as : Fin T → Fin ℓ,
    trajWeight π p Th θs as *
      (lpObj I (fun θ => (countAll θs θ : ℝ)) (xALG θs as) - OPT I (fun θ => (countAll θs θ : ℝ)))

end GoodProphets


