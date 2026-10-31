-- Prove2me | Definitions.Def_CryptoMiningMFG_Control
-- name    : CryptoMiningMFG_Control
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:34.990164+00:00
-- url     : https://prove2.me/theorems/968463e4-3896-4c45-afd4-55ebe7f7ca98
-- title:
--   Hash-rate controls: non-anticipating rules $\varphi_j(s;\tau_1,\dots,\tau_j)\ge0$
-- statement:
--   A **hash-rate control** tells a miner which hash rate $\alpha_s\ge0$ to use at each time $s$. It may depend on time and on the miner's own reward history: while $j$ rewards have been received, at times $\tau_1\le\dots\le\tau_j$, the hash rate is
--
--   $$
--   \alpha_s=\varphi_j(s;\tau_1,\dots,\tau_j)\ge0 .
--   $$
--
--   Each rule $\varphi_j$ is jointly measurable in $(s,\tau)$ and locally integrable in $s$, so the cumulative cost $c\int\alpha_s\,ds$ is finite over bounded periods. The **constant control** $a\ge0$ uses $\alpha_s\equiv a$ whatever happens.
--
--   This class contains every Markov control $\alpha_s=\alpha(s,X_s)$ of the paper, since the wealth $X_s$ is a function of $s$ and of the reward history once the starting point is fixed. The value function is a supremum over this class.
--
--   **Formalization Note** A control does not depend on the starting wealth. The constant control at $a$ uses $\max(a,0)$; it is only applied with $a>0$.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, §2.3 p.8 ("The representative miner chooses a hash rate α_t ≥ 0"); §2.4 p.10 (controls of (2.4))

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace CryptoMiningMFG

/-- A **hash-rate control** of an individual miner. Li, Reppen, Sircar, arXiv:1912.01952v2, §2.3,
p.8 ("The representative miner chooses a hash rate α_t ≥ 0") and §2.4, p.10.

`φ j s τ` is the hash rate `α_s ≥ 0` the miner uses at (absolute) time `s` while it has received
`j` rewards so far, at times `τ = (τ₁, …, τ_j)`. The rule is jointly measurable in `(s, τ)` and
locally integrable in time, so that the cumulative cost `c ∫ α_s ds` is finite on bounded
intervals.

**Formalization Note.** The paper takes Markovian controls `α_t = α(t, X_t)` (p.10). Here a control
is any non-anticipating function of time and of the miner's own reward history. This class
contains every Markov control (the wealth `X_t` is a function of `t` and the reward history once
the start point is fixed) and is the one the value function is a supremum over. A control does
not depend on the starting wealth; a feedback of the wealth started at `(t, x)` is a different
control for each `x`. -/
structure Control where
  /-- the hash-rate rule -/
  φ : (j : ℕ) → ℝ → (Fin j → ℝ) → ℝ
  nonneg : ∀ j s τ, 0 ≤ φ j s τ
  measurable : ∀ j, Measurable (fun q : ℝ × (Fin j → ℝ) => φ j q.1 q.2)
  locallyIntegrable : ∀ j τ (a b : ℝ), ∫⁻ s in Ioc a b, ENNReal.ofReal (φ j s τ) ≠ ∞

/-- The **constant hash rate** `a` (used with `a ≥ 0`; the rate is `max a 0`, so a negative `a`
gives the zero control). -/
noncomputable def constControl (a : ℝ) : Control where
  φ := fun _ _ _ => max a 0
  nonneg := fun _ _ _ => le_max_right _ _
  measurable := fun _ => measurable_const
  locallyIntegrable := fun _ _ a b => by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Ioc])

end CryptoMiningMFG


