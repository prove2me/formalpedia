-- Prove2me | Definitions.Def_TightQLearning_IsGenerativeModel
-- name    : TightQLearning_IsGenerativeModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:45.932988+00:00
-- url     : https://prove2.me/theorems/2cae2671-8d58-4d4b-87da-16a68146befd
-- title:
--   §2 — the generative model: independent samples $s_t(s,a)\sim P(\cdot\mid s,a)$
-- statement:
--   A family of random variables $s_t(s,a)$ on a probability space $(\Omega,\mu)$ is a **generative model** of the MDP over the horizon $T$ if, for $1\le t\le T$ and every pair $(s,a)$:
--
--   1. each $s_t(s,a)$ is measurable, the state space carrying the discrete $\sigma$-algebra;
--   2. $\mu\{s_t(s,a)=s'\}=P(s'\mid s,a)$ for every state $s'$;
--   3. the whole family indexed by $(t,s,a)$ is jointly independent, across iterations and across pairs.
--
--   This is the sampling model of the synchronous setting: one fresh sample per state-action pair per iteration.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6; Algorithm 1, p.7

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting

open MeasureTheory ProbabilityTheory

namespace TightQLearning

/-- The generative model of the synchronous setting (arXiv:2102.06548v4, §2, p.6; Algorithm 1,
p.7): "in each iteration t, we collect an independent sample s_t(s, a) ∼ P(· | s, a) for every
state-action pair (s, a) ∈ S × A".

**Formalization Note.** `X` carries the discrete σ-algebra `⊤`. For `1 ≤ t ≤ T`, each `sample t s a`
is a random variable with law `P(· | s, a)`, and the whole family indexed by `(t, s, a)` with
`1 ≤ t ≤ T` is jointly independent, across iterations and across pairs. Nothing is assumed about
`sample t` for `t` outside `[1, T]`, which the algorithm never reads. -/
def IsGenerativeModel {X A : Type} [Fintype X] (M : QLearning.Convergence.FiniteMDP X A) (T : ℕ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (sample : ℕ → X → A → Ω → X) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, ∀ s a, @Measurable Ω X mΩ ⊤ (sample t s a)) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ s a s',
    μ {ω | sample t s a ω = s'} = ENNReal.ofReal (M.P s a s')) ∧
  @iIndepFun Ω {i : ℕ × X × A // i.1 ∈ Finset.Icc 1 T} mΩ (fun _ => X) (fun _ => ⊤)
    (fun i => sample i.1.1 i.1.2.1 i.1.2.2) μ

end TightQLearning


