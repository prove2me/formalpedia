-- Prove2me | Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues
-- name    : FeinbergPOMDP_WStar_Supplement_MDPValues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:20:22.239811+00:00
-- url     : https://prove2.me/theorems/95639e00-b869-4cd3-a388-0968739dd1d1
-- title:
--   §2, pp. 5–6 — expected total discounted costs (2.1), optimal values, optimal, Markov and stationary policies, inf-compactness
-- statement:
--   Expected costs and optimality for a Markov decision process on Borel spaces, built on the published MDP, policy and strategic-measure objects.
--
--   Let $M$ be an MDP with state space $\mathbb S$, action space $\mathbb A$, transition probability $q$ and one-step cost $c(s,a)=\ell+g(s,a)$ with $\ell\in\mathbb R$ and $g\ge0$, so $c$ takes values in $\mathbb R\cup\{+\infty\}$. For a policy $\pi$ (a sequence of stochastic kernels on $\mathbb A$ given the histories) and an initial state $s$, let $P^\pi_s$ be the strategic measure on trajectories $(s_0,a_0,s_1,a_1,\dots)$ given by the Ionescu Tulcea theorem.
--
--   1. **Finite horizon (2.1).** $v^\pi_{T,\alpha}(s)=E^\pi_s\sum_{t=0}^{T-1}\alpha^t c(s_t,a_t)$, with $v^\pi_{0,\alpha}=0$.
--   2. **Infinite horizon.** $v^\pi_\alpha(s)=E^\pi_s\sum_{t=0}^{\infty}\alpha^t c(s_t,a_t)$.
--   3. **Optimal values.** $v_{T,\alpha}(s)=\inf_\pi v^\pi_{T,\alpha}(s)$ and $v_\alpha(s)=\inf_\pi v^\pi_\alpha(s)$, over all policies.
--   4. **Optimal policies.** $\pi$ is $T$-horizon (discount-) optimal if $v^\pi_{T,\alpha}=v_{T,\alpha}$ ($v^\pi_\alpha=v_\alpha$) at every initial state.
--   5. **Markov policies.** A sequence of Borel maps $\varphi_t:\mathbb S\to\mathbb A$ defines the nonrandomized Markov policy choosing $\varphi_t(s_t)$ at time $t$.
--   6. **Integrals of extended-real functions** $\int v\,d\mu=\int v^+d\mu-\int v^-d\mu$.
--   7. **Inf-compactness.** A function into $\overline{\mathbb R}$ is inf-compact if all its level sets $\{v\le\lambda\}$, $\lambda\in\mathbb R$, are compact.
--
--   These are the quantities in which the optimality statements (i)–(vi) of Theorem 3.1 are expressed.
--
--   **Formalization Note** The expectations are taken as the expectation of the positive parts minus that of the negative parts of the one-step costs, in the extended reals. Under Assumption (D) (cost bounded below, $\alpha<1$) the negative parts have finite expectation and under Assumption (P) ($c\ge0$) they vanish, so no $\infty-\infty$ arises and these are the paper's expected costs. The MDP, its policies and the strategic measure are the published definitions `FeinbergLiang.ACOE.MDP`, `Policy` and `pathMeasure`.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, §2, (2.1), Assumptions (D), (P), optimal values and policies, p. 5; inf-compactness, p. 6 and p. 23

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace FeinbergPOMDP.WStar.Supplement

/-! Feinberg, Kasyanov, Zgurovsky, *Partially Observable Total-Cost Markov Decision Processes with
Weakly Continuous Transition Probabilities*, arXiv:1401.2168v2, §2, pp. 5–6: expected total
discounted costs (2.1) of a policy, finite and infinite horizon, the optimal values
`g(p) = inf_π g^π(p)`, optimal policies, Markov and stationary policies, and inf-compactness.

The MDP itself, its (randomized, history-dependent) policies and the strategic measure given by the
Ionescu Tulcea theorem are the published general objects `FeinbergLiang.ACOE.MDP`,
`FeinbergLiang.ACOE.Policy` and `FeinbergLiang.ACOE.pathMeasure`. -/

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The one-step cost `c(s, a) = lower + cost(s, a) ∈ ℝ ∪ {+∞}` of the MDP `M`, as an extended
real. -/
noncomputable def oneStepCost (M : MDP S A) (s : S) (a : A) : EReal :=
  (M.lower : EReal) + (M.cost s a : EReal)

/-- The `T`-horizon expected total discounted cost (2.1) of the policy `π` from the initial state
`s`: `E^π_s ∑_{t<T} α^t c(s_t, a_t)`, computed as the expectation of the positive parts minus the
expectation of the negative parts of the one-step costs (in `[0, ∞]`, then in `EReal`). For
`T = 0` it is `0`.

Formalization Note. Under (D) the negative parts are bounded by `max(−lower, 0)`, and under (P)
they vanish, so the subtracted expectation is finite and the difference is the expectation of the
sum of the costs (no `∞ − ∞` occurs). `α^0 = 1`, also for `α = 0`. -/
noncomputable def horizonCost (M : MDP S A) (π : Policy S A) (T : ℕ) (α : ℝ) (s : S) : EReal :=
  ((∫⁻ ω, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (α ^ t) * (oneStepCost M (ω t).1 (ω t).2).toENNReal
        ∂(pathMeasure M π s) : ℝ≥0∞) : EReal) -
  ((∫⁻ ω, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (α ^ t) * (-(oneStepCost M (ω t).1 (ω t).2)).toENNReal
        ∂(pathMeasure M π s) : ℝ≥0∞) : EReal)

/-- The infinite-horizon expected total discounted cost (`T = ∞` in (2.1)) of `π` from `s`:
`E^π_s ∑_{t=0}^∞ α^t c(s_t, a_t)`, the expectation of the series of positive parts minus the
expectation of the series of negative parts. Under (D) (`α < 1`, `c` bounded below) and under (P)
(`c ≥ 0`) the subtracted term is finite, and this is the paper's `v^π_α(s)`. -/
noncomputable def discountedCost (M : MDP S A) (π : Policy S A) (α : ℝ) (s : S) : EReal :=
  ((∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t) * (oneStepCost M (ω t).1 (ω t).2).toENNReal
        ∂(pathMeasure M π s) : ℝ≥0∞) : EReal) -
  ((∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t) * (-(oneStepCost M (ω t).1 (ω t).2)).toENNReal
        ∂(pathMeasure M π s) : ℝ≥0∞) : EReal)

/-- The optimal `T`-horizon value `v_{T,α}(s) = inf_{π ∈ Π} v^π_{T,α}(s)`, the infimum over all
(randomized, history-dependent) policies. -/
noncomputable def optHorizonCost (M : MDP S A) (T : ℕ) (α : ℝ) (s : S) : EReal :=
  ⨅ π : Policy S A, horizonCost M π T α s

/-- The optimal infinite-horizon value `v_α(s) = inf_{π ∈ Π} v^π_α(s)`. -/
noncomputable def optDiscountedCost (M : MDP S A) (α : ℝ) (s : S) : EReal :=
  ⨅ π : Policy S A, discountedCost M π α s

/-- `π` is `T`-horizon discount-optimal: `v^π_{T,α}(s) = v_{T,α}(s)` for every initial state. -/
def IsHorizonOptimal (M : MDP S A) (π : Policy S A) (T : ℕ) (α : ℝ) : Prop :=
  ∀ s, horizonCost M π T α s = optHorizonCost M T α s

/-- `π` is discount-optimal: `v^π_α(s) = v_α(s)` for every initial state. -/
def IsDiscountOptimal (M : MDP S A) (π : Policy S A) (α : ℝ) : Prop :=
  ∀ s, discountedCost M π α s = optDiscountedCost M α s

/-- The (nonrandomized) Markov policy `(φ₀, φ₁, …)`: at epoch `t` the action `φ_t(s_t)` is chosen
with probability one. The decision rules are Borel maps, as stochastic kernels must be. A
`T`-horizon Markov policy `(φ₀, …, φ_{T−1})` is any such sequence; the `T`-horizon cost does not
depend on `φ_t` for `t ≥ T`. -/
noncomputable def markovPolicy (φ : ℕ → S → A) (hφ : ∀ t, Measurable (φ t)) : Policy S A where
  rule t := Kernel.deterministic (fun h => φ t h.2) ((hφ t).comp measurable_snd)

/-- The expectation `∫ v dμ` of an extended-real function, as the expectation of its positive part
minus that of its negative part. For `v` bounded below and `μ` a probability measure it is the
usual integral in `ℝ ∪ {+∞}`. -/
noncomputable def lintegralE (μ : Measure S) (v : S → EReal) : EReal :=
  ((∫⁻ s, (v s).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ s, (-(v s)).toENNReal ∂μ : ℝ≥0∞) : EReal)

/-- Inf-compactness (pp. 6, 23): every level set `{u : g(u) ≤ λ}`, `λ ∈ ℝ`, is compact. -/
def InfCompact {U : Type*} [TopologicalSpace U] (g : U → EReal) : Prop :=
  ∀ l : ℝ, IsCompact {u | g u ≤ (l : EReal)}

end FeinbergPOMDP.WStar.Supplement


