-- Prove2me | Definitions.Def_QuantileMDP_optValue
-- name    : QuantileMDP_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:09.408569+00:00
-- url     : https://prove2.me/theorems/635a1d72-1c00-431a-8ff5-073181818a64
-- title:
--   The optimal quantile value function $v_t(s,\tau)$ (5) and the intermediate value $\tilde v_t(s,\tau,a)$
-- statement:
--   Fix a model $M$, a horizon $T$, a time $t$, a state $s$ and a level $\tau$. The **optimal value function** (5) is
--
--   $$
--   v_t(s,\tau)=\sup_{\pi_{t:T}\ \text{admissible}} Q_\tau\Bigl[\sum_{k=t}^{T-1}r_k(S_k,a_k,w_k)\ \Big|\ S_t=s\Bigr],
--   $$
--
--   where the process starts in $s$ at time $t$ and the policy's histories begin with $S_t$. The **intermediate value function** fixes the first action:
--
--   $$
--   \tilde v_t(s,\tau,a)=\sup_{\pi_{t:T}\ \text{admissible},\ \mu_t(s)=a} Q_\tau\Bigl[\sum_{k=t}^{T-1}r_k(S_k,a_k,w_k)\ \Big|\ S_t=s\Bigr].
--   $$
--
--   At $t=0$, $v_0(s,\tau)$ is the optimal value of the QMDP (3) from $S_0=s$. These are the optimal values; the values computed by the backward recursion are a separate definition (`dpValue`).
--
--   **Formalization Note** The process started at time $t$ is the shifted model $M^{(t)}$ started at time $0$, over the horizon $T-t$ (truncated subtraction: $0$ when $t\ge T$). The suprema are taken in `EReal`; for a non-admissible $a$ the second supremum is empty and equals $-\infty$.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.1, value function and (5), p.10; §3.2, definition of ṽ_t, p.10

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model

open MeasureTheory

namespace QuantileMDP

variable {S A : Type*}

/-- The optimal value function (5): `v_t(s, τ) = max_{π_{t:T}} Q_τ[∑_{k=t}^{T-1} r_k | S_t = s]`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.1, the value
function and (5), p.10.

**Formalization Note** The process started at time `t` in state `s` is the model `M.shift t`
started at time `0`, with a fresh policy whose histories begin with `S_t` (p.10). The maximum is
the `EReal` supremum over admissible policies of `M.shift t`; the horizon is `T - t`
(truncated, so `0` when `t ≥ T`). -/
noncomputable def optValue [Fintype S] (M : Model S A) (T t : ℕ) (s : S) (τ : ℝ) : EReal :=
  ⨆ (π : Policy S A) (_ : (M.shift t).Admissible π),
    quantile (rewardLaw (M.shift t) (T - t) π s) τ

/-- The intermediate value function `ṽ_t(s, τ, a) = max_{π_{t:T} | μ_t(s) = a} v_t^{π_{t:T}}(s, τ)`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.2, p.10.

**Formalization Note** `μ_t(s) = a` is the condition that the shifted policy's first action, on
the history `(S_t) = (s)`, is `a`. For a non-admissible `a` the supremum is empty, `⊥`. -/
noncomputable def optValueAct [Fintype S] (M : Model S A) (T t : ℕ) (s : S) (τ : ℝ) (a : A) :
    EReal :=
  ⨆ (π : Policy S A) (_ : (M.shift t).Admissible π) (_ : π 0 (fun _ => s) = a),
    quantile (rewardLaw (M.shift t) (T - t) π s) τ

end QuantileMDP


