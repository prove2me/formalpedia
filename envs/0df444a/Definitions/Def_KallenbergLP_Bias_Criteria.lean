-- Prove2me | Definitions.Def_KallenbergLP_Bias_Criteria
-- name    : KallenbergLP_Bias_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:48:06.704236+00:00
-- url     : https://prove2.me/theorems/617d0b84-fc45-4c2b-aeea-d39275f8e6e3
-- title:
--   Period, discounted, average, upper-average, and optimal rewards
-- statement:
--   For any admissible policy $R$ and starting state $i$, let $v_i^t(R)$ be its expected reward in period $t$. Its **discounted reward**, **average reward**, and **upper average reward** are
--
--   $$
--   v_i^\beta(R)=\sum_{t=1}^{\infty}\beta^{t-1}v_i^t(R),\qquad
--   \phi_i(R)=\liminf_{T\to\infty}\frac1T\sum_{t=1}^T v_i^t(R),\qquad
--   \hat\phi_i(R)=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T v_i^t(R).
--   $$
--
--   The values $v_i^\beta$ and $\phi_i$ are statewise suprema over the full class $C$ of history-dependent randomized policies. A policy is **bias optimal** if $v_i^\beta(R)-v_i^\beta\to0$ as $\beta\uparrow1$ for every $i$; it is **average optimal** if $\phi_i(R)=\phi_i$ for every $i$.
--
--   These criteria retain the distinction between all policies and the pure stationary subclass, which is central to Theorem 5.2.2.
--
--   **Formalization Note** The real `tsum` is used for discounted rewards and is applied near $\beta=1$ from below, where finite rewards and stochastic transition rows make it summable. A horizon $T=0$ receives Lean's totalized average value zero; this does not affect the limits as $T\to\infty$. The real suprema and liminf/limsup are finite for this finite bounded-reward model.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 21–23, Section 2.2; p. 102, equation (4.2.9); p. 161, equation (5.1.1); https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_Policy

open Filter

namespace KallenbergLP.Bias

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Expected reward in period `n + 1`, for any history-dependent randomized policy. -/
def periodReward (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a : α, occupancy M R i j a n * M.reward j a

/-- The discounted expected reward of a general policy. Used near `β = 1` from below. -/
noncomputable def discountedReward (M : MDP N α) (R : Policy M)
    (i : Fin N) (β : ℝ) : ℝ :=
  ∑' n : ℕ, β ^ n * periodReward M R i n

/-- The statewise supremum of discounted rewards over the entire policy class C. -/
noncomputable def optimalDiscounted (M : MDP N α) (i : Fin N) (β : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ R : Policy M, x = discountedReward M R i β}

/-- The average reward is the liminf of the finite-horizon average, as on p. 22. -/
noncomputable def averageReward (M : MDP N α) (R : Policy M) (i : Fin N) : ℝ :=
  liminf (fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ n ∈ Finset.range T, periodReward M R i n) atTop

/-- The upper average reward of (4.2.9). -/
noncomputable def upperAverageReward (M : MDP N α) (R : Policy M) (i : Fin N) : ℝ :=
  limsup (fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ n ∈ Finset.range T, periodReward M R i n) atTop

/-- The statewise supremum of average rewards over the entire policy class C. -/
noncomputable def optimalAverage (M : MDP N α) (i : Fin N) : ℝ :=
  sSup {x : ℝ | ∃ R : Policy M, x = averageReward M R i}

/-- Bias optimality on p. 22 compares with all policies, not only C_D. -/
def IsBiasOptimal (M : MDP N α) (R : Policy M) : Prop :=
  ∀ i : Fin N,
    Tendsto (fun β : ℝ => discountedReward M R i β - optimalDiscounted M i β)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0)

/-- Average optimality is componentwise for every initial state. -/
def IsAverageOptimal (M : MDP N α) (R : Policy M) : Prop :=
  ∀ i : Fin N, averageReward M R i = optimalAverage M i

end KallenbergLP.Bias


