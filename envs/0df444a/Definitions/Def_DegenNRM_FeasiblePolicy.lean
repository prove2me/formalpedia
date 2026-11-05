-- Prove2me | Definitions.Def_DegenNRM_FeasiblePolicy
-- name    : DegenNRM_FeasiblePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:46.846878+00:00
-- url     : https://prove2.me/theorems/a2c13a48-87d0-4120-808d-ef8f7353a3fb
-- title:
--   Feasible online policies, their capacities $\tilde c^\pi_t$ and value $V^\pi(I)$
-- statement:
--   A possibly randomized online policy draws internal randomness $\xi$ from a probability space independent of the arrivals, and serves the query of period $t$ iff $x_t(\xi,I)=1$. It is **feasible** if
--
--   1. $x_t$ depends only on $\xi$ and the arrivals $(\tilde r_1,\tilde a_1),\dots,(\tilde r_t,\tilde a_t)$;
--   2. the capacity constraint (1), $\sum_{t=1}^T\tilde a_{t,i}x_t\le C_i$ for all $i\in[m]$, holds on every sample path.
--
--   The remaining capacities are $\tilde c^\pi_t=C-\sum_{\tau<t}\tilde a_\tau x_\tau$ and the collected value is $V^\pi(I)=\sum_{t=1}^T\tilde r_tx_t$. Lemma 1 is stated for every feasible policy.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §2, (1), p.6; §3.1, p.11

import Mathlib
import Definitions.Def_DegenNRM_Instance

open MeasureTheory

namespace DegenNRM

/-- **A feasible online policy** (Jiang, Ma & Zhang, arXiv:2210.07996v5, §2, (1), p.6).

A (possibly randomized) online policy draws its internal randomness `ξ` from a probability space
`Ξ`, independent of the sample path, and serves the query of period `t` iff `x t ξ ω = true`
(period `t ∈ [T]` is the coordinate `t - 1`). It is **feasible** if

1. `x_t` depends only on the arrivals `(r̃_1, ã_1), …, (r̃_t, ã_t)` (and on `ξ`): two sample paths
   that agree up to period `t` give the same decision in period `t`;
2. the capacity constraint (1) holds on every sample path:
   `Σ_t ã_{t,i} x_t ≤ C_i` for every resource `i`.

**Formalization Note.** The dependence on `F(·)` is through the fixed instance. Randomized
policies (p.6: "x̃^π_t can be stochastic if π is a randomized policy") are covered by the
auxiliary randomness `ξ`. -/
def IsFeasiblePolicy {m n T : ℕ} {Ξ : Type*} (inst : Instance m n) (C : Fin m → ℝ)
    (x : Fin T → Ξ → (Fin T → Fin n × ℝ) → Bool) : Prop :=
  (∀ t ξ ω ω', (∀ τ, τ ≤ t → ω τ = ω' τ) → x t ξ ω = x t ξ ω') ∧
    ∀ ξ ω i, (∑ t, if x t ξ ω then inst.a (ω t).1 i else 0) ≤ C i

/-- **The remaining capacities `c̃^π_t` of a policy** (arXiv:2210.07996v5, §3.1, p.11):
`policyCapacity … k ξ ω = C - Σ_{τ < k} ã_τ x̃^π_τ`, the capacities at the beginning of period
`k + 1` (so `k = 0` gives `c̃^π_1 = C` and `k = T` gives `c̃^π_{T+1}`). -/
def policyCapacity {m n T : ℕ} {Ξ : Type*} (inst : Instance m n) (C : Fin m → ℝ)
    (x : Fin T → Ξ → (Fin T → Fin n × ℝ) → Bool) (k : ℕ) (ξ : Ξ) (ω : Fin T → Fin n × ℝ) :
    Fin m → ℝ :=
  C - ∑ τ : Fin T, if (τ : ℕ) < k ∧ x τ ξ ω = true then inst.a (ω τ).1 else 0

/-- **The total collected value `V^π(I) = Σ_t r̃_t x̃^π_t`** of a policy (arXiv:2210.07996v5,
§2, p.6). -/
def policyTotal {n T : ℕ} {Ξ : Type*} (x : Fin T → Ξ → (Fin T → Fin n × ℝ) → Bool) (ξ : Ξ)
    (ω : Fin T → Fin n × ℝ) : ℝ :=
  ∑ t, if x t ξ ω then (ω t).2 else 0

end DegenNRM


