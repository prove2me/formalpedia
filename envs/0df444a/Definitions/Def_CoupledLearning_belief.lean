-- Prove2me | Definitions.Def_CoupledLearning_belief
-- name    : CoupledLearning_belief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:03.148402+00:00
-- url     : https://prove2.me/theorems/beb3012f-267a-4ac5-afcd-44a8734f455a
-- title:
--   The belief process $\theta^k$ of (θ-update)
-- statement:
--   Given the initial belief $\theta^1$, the played profiles $q^k$, the realized payoffs $y^k$ and the update stages $k_1<k_2<\cdots$, the belief is constant between update stages, and at an update stage
--
--   $$\theta^{k_{t+1}}(s)=\frac{\theta^{k_t}(s)\prod_{k=k_t}^{k_{t+1}-1}\varphi^s(y^k|q^k)}{\sum_{s'\in S}\theta^{k_t}(s')\prod_{k=k_t}^{k_{t+1}-1}\varphi^{s'}(y^k|q^k)},\qquad s\in S.$$
--
--   The belief is computed from the data and is not a free process. The module also defines the Bayes step $\theta(s)L(s)/\sum_{s'}\theta(s')L(s')$ and the last update stage $\le k$.
--
--   **Formalization Note** Stages are indexed from $0$ and the first stage is an update stage. If a normalizer is $0$, Lean's division returns $0$; this happens only on a null set for the learning process.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, (θ-update), pp.7–8

import Mathlib
import Definitions.Def_CoupledLearning_Prof

namespace CoupledLearning

/-- One Bayes step: the posterior `θ(s) L(s) / ∑_{s'} θ(s') L(s')` of a prior `θ` and
likelihoods `L` (arXiv:2206.05637v2, (θ-update), p.8). If the normalizer is `0` Lean's division
returns `0`. -/
noncomputable def bayesStep {S : Type*} [Fintype S] (θ L : S → ℝ) : S → ℝ :=
  fun s => θ s * L s / ∑ s', θ s' * L s'

/-- The last update stage `≤ k`: the largest `j ≤ k` with `j ∈ T` (the paper's `k_t` with
`k_t ≤ k < k_{t+1}`); `0` if there is none. -/
noncomputable def lastUpdate (T : Set ℕ) (k : ℕ) : ℕ := by
  classical exact Nat.findGreatest (· ∈ T) k

/-- The belief `θ^k` of the learning dynamics (arXiv:2206.05637v2, (θ-update), pp.7–8), computed
from the initial belief `θ₁`, the played profiles `qs j = q^j`, the realized payoffs
`ys j = y^j` and the set `T` of update stages `k_1 < k_2 < …`. The belief is constant between
update stages, and at an update stage `k_{t+1}`
`θ^{k_{t+1}}(s) = θ^{k_t}(s) ∏_{k=k_t}^{k_{t+1}−1} φ^s(y^k|q^k) / ∑_{s'} θ^{k_t}(s') ∏_{k=k_t}^{k_{t+1}−1} φ^{s'}(y^k|q^k)`.

**Formalization Note.** Stages are indexed from `0` (Lean stage `k` is the paper's stage `k + 1`),
and the first stage `0` is an update stage in every use. At an update stage `k + 1` the previous
update stage is `k_t = lastUpdate T k` and the belief at stage `k` equals `θ^{k_t}`, so the
recursion below is (θ-update) verbatim. -/
noncomputable def belief {I S : Type*} [Fintype S] {d : I → ℕ} (θ₁ : S → ℝ)
    (φ : S → Prof d → (I → ℝ) → ℝ) (qs : ℕ → Prof d) (ys : ℕ → I → ℝ) (T : Set ℕ) :
    ℕ → S → ℝ
  | 0 => θ₁
  | k + 1 => by
    classical
    exact if k + 1 ∈ T then
      bayesStep (belief θ₁ φ qs ys T k)
        (fun s => ∏ j ∈ Finset.Ico (lastUpdate T k) (k + 1), φ s (qs j) (ys j))
    else belief θ₁ φ qs ys T k

end CoupledLearning


