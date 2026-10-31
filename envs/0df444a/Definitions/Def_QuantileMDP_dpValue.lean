-- Prove2me | Definitions.Def_QuantileMDP_dpValue
-- name    : QuantileMDP_dpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:03.141992+00:00
-- url     : https://prove2.me/theorems/4859e761-913b-448b-a5bc-a19d03819353
-- title:
--   The backward recursion $v_T=0$, $v_t(s,\tau)=\max_a\mathrm{OPT}(s,\tau,a,v_{t+1})$ of Theorem 2
-- statement:
--   Fix a model $M$ with finite state set $\mathcal S$ and a horizon $T$. The **dynamic-programming values** are defined backwards: $v_T(s,\tau)=0$, and for $t=T-1,\dots,0$
--
--   $$
--   v_t(s,\tau)=\max_{a\in\mathcal A_t(s)}\ \mathrm{OPT}\bigl(p,g,\tau\bigr),\qquad p_{s'}=P_t(s'\mid s,a),\quad g_{s'}(q)=v_{t+1}(s',q)+r_t(s,a,s'),
--   $$
--
--   with $\mathrm{OPT}$ the problem of (8) over $q\in[0,1]^{\mathcal S}$. For $t\ge T$ the value is $0$.
--
--   These are the values that Theorem 2 identifies with the optimal quantile of the cumulative reward. They are a definition separate from the optimal value function (5).
--
--   **Formalization Note** The recursion runs on the number $T-t$ of steps to go. $\mathrm{OPT}$ is `opt`, with the corrected budget $\sum p_iq_i<\tau$ or $=0$; the maximum over actions is the `EReal` supremum over the admissible set. The terminal value is $0$ for every $\tau$; only $\tau\in[0,1]$ is ever used.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.3, Theorem 2, p.12; Theorem 1 (8), p.11

import Mathlib
import Definitions.Def_QuantileMDP_opt
import Definitions.Def_QuantileMDP_Model

namespace QuantileMDP

variable {S A : Type*}

/-- The backward recursion of Theorem 2 indexed by the number `n` of steps to go: `0` when no
step is left, otherwise `max_a OPT(s, τ, a, v_{t+1})` with `p_i = P_t(s_i | s, a)` and
`g_i(q) = v_{t+1}(s_i, q) + r_t(s, a, s_i)`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, Theorem 2, p.12,
with `OPT` of Theorem 1 (8), p.11.

**Formalization Note** `OPT` is `opt` with the corrected budget. The maximum over `a` ranges over
the admissible actions `adm t s`. -/
noncomputable def dpAux [Fintype S] (M : Model S A) : ℕ → ℕ → S → ℝ → EReal
  | 0, _, _, _ => 0
  | n + 1, t, s, τ => ⨆ a ∈ M.adm t s, opt (fun s' => (M.P t s a s').toReal)
      (fun s' q => dpAux M n (t + 1) s' q + ((M.r t s a s' : ℝ) : EReal)) τ

/-- The value function computed by the backward recursion of Theorem 2: `v_T = 0` and
`v_t(s, τ) = max_a OPT(s, τ, a, v_{t+1}(·,·))` for `t = T-1, …, 0`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, Theorem 2, p.12.

**Formalization Note** `dpValue M T t = dpAux M (T - t) t`; it is `0` for `t ≥ T`. It is a
definition distinct from the optimal value `optValue` (5); Theorem 2 identifies them at `t = 0`.
The terminal value is `0` for every `τ`; only `τ ∈ [0,1]` is ever used. -/
noncomputable def dpValue [Fintype S] (M : Model S A) (T t : ℕ) (s : S) (τ : ℝ) : EReal :=
  dpAux M (T - t) t s τ

end QuantileMDP


