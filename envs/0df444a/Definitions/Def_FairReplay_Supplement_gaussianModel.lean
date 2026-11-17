-- Prove2me | Definitions.Def_FairReplay_Supplement_gaussianModel
-- name    : FairReplay_Supplement_gaussianModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:43:07.403872+00:00
-- url     : https://prove2.me/theorems/658ddbd2-ae06-4d0b-afbc-bf67b9df4fd5
-- title:
--   Gaussian delta-oracle model $Z_v\sim N(\theta_v,\nu_v^2)$
-- statement:
--   In the **Gaussian delta-oracle model**, a call at vertex $v$ reveals only the old/new difference $Z_v=P_1(v;R)-P_0(v;R)$, modelled as
--   $$Z_v\sim N(\theta_v,\nu_v^2)$$
--   with known variance $\nu_v^2>0$, independently across calls. A sequential tester chooses, round by round, at which vertex to call the oracle.
--
--   This is the observation law of the Gaussian allocation results (Theorems 10.1 and 10.2).
--
--   **Formalization Note** A sequential-sampling environment whose actions are the vertices; $\nu_v$ is the standard deviation, so the variance is $\nu_v^2$. Independence across calls is supplied by the trajectory law of the sequential-sampling model.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §3, p.3 (PDF p.5) and §10, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_StochasticBandit

open MeasureTheory ProbabilityTheory

namespace FairReplay.Supplement

/-- **Gaussian delta-oracle model** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under
Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, §3, p.3 (PDF p.5):
"A vertex-paired old/new difference Zv = P1(v; R) − P0(v; R) has mean θv and variance ν²v [...]
Assume independent calls and Zv ∼ N(θv, ν²v) with known ν²v > 0"; §10, p.11: "A Gaussian
delta-oracle call reveals only Zv = P1(v; R) − P0(v; R)").

`gaussianModel θ ν` is the sequential-sampling environment whose actions are the vertices `v` of
`Fin n`; one call at `v` returns one draw of `N(θ v, (ν v)²)`. Calls are independent (the trajectory
law of the sequential-sampling model draws every round afresh).

**Formalization Note** `ν v` is the standard deviation, so the variance is `(ν v)²`; the theorems
assume `ν v > 0`. One Gaussian delta-oracle call is one round of the model. -/
noncomputable def gaussianModel {n : ℕ} (θ ν : Fin n → ℝ) : BanditAlgorithm.StochasticBandit n where
  P v := gaussianReal (θ v) (Real.toNNReal (ν v ^ 2))
  prob _ := inferInstance

end FairReplay.Supplement


