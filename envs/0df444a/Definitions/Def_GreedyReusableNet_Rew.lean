-- Prove2me | Definitions.Def_GreedyReusableNet_Rew
-- name    : GreedyReusableNet_Rew
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:03.729256+00:00
-- url     : https://prove2.me/theorems/99d7c64a-3e32-446f-ab21-3993f5a475dd
-- title:
--   Total expected reward $\mathrm{Rew}(\pi)$
-- statement:
--   For a policy $\pi$ and horizon $T$,
--   $$\mathrm{Rew}(\pi)=\mathbb E\Big[\sum_{t<T}\ \sum_{B\in\mathcal A^\pi_{t,\mathrm{act}}} r_t\big(B;n^\pi_t(B)\big)\Big],$$
--   the expectation over the policy's initial seed, its period seeds, the activation draws and the blocking times. The module also defines the general path functional $\mathbb E[\sum_t\sum_{B\in\mathcal A_{t,\mathrm{act}}}g(t,B,n_t)]$ used in (12) and (13).
--
--   The paper: "Our objective is to design an online policy $\pi$ to maximize its total expected revenue throughout the $T$ time periods, which we denote as $\mathrm{Rew}(\pi)$."
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.3, p.15; eq. (2), p.10

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule

open MeasureTheory

namespace GreedyReusableNet

/-- **A path functional**: `∑_t ∑_{B ∈ 𝒜_{t,act}} g(t, B, n_t)` along a history `h`, where
`𝒜_{t,act}` is the set of bundles activated in period `t` and `n_t` the counting vector before
period `t` (Simchi-Levi, Zheng & Zhu, SSRN 3981123, eq. (2), p.10). -/
noncomputable def pathSum {N : ℕ} (h : History N)
    (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) : ℝ :=
  ∑ k : Fin h.length, ∑ B ∈ (h.get k).2.1, g k B (counts (h.take k))

/-- **An expected path functional** of a policy over the horizon `T`:
`𝔼[∑_{t<T} ∑_{B ∈ 𝒜_{t,act}} g(t, B, n_t)]`, the expectation over the policy's initial seed and
the tape. -/
noncomputable def expectedSum {N : ℕ} (I : ProblemInstance N) (T : ℕ) (ρ : Rule N)
    (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) : ℝ :=
  ∫ p : ℝ × Tape N T, pathSum (run I (ρ.act p.1) p.2 T) g ∂(ρ.seedLaw.prod (tapeLaw N T))

/-- **The total expected reward** `Rew(π)` (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.3, p.15:
"its total expected revenue throughout the `T` time periods"; per-period reward (2), p.10): the
expectation of `∑_{t<T} ∑_{B ∈ 𝒜^π_{t,act}} r_t(B; n^π_t(B))`, over the realizations of the
activation sets, the blocking times and the randomization of `π`. -/
noncomputable def Rew {N : ℕ} (I : ProblemInstance N) (T : ℕ) (ρ : Rule N) : ℝ :=
  expectedSum I T ρ (fun t B n => (I.period t).reward B n)

end GreedyReusableNet


