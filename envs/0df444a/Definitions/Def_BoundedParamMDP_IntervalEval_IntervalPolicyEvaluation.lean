-- Prove2me | Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation
-- name    : BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:03.862792+00:00
-- url     : https://prove2.me/theorems/32ad0266-0875-4f0c-95e1-a41ebae55ce2
-- title:
--   Interval policy evaluation $IVI_{\updownarrow\pi}$ and its bounds $IVI_{\downarrow\pi}$, $IVI_{\uparrow\pi}$ (eq. (27)), and contraction mappings
-- statement:
--   Fix a bounded-parameter MDP $M_\updownarrow$ over a finite state set $Q$ and action set $A$, with its set of member MDPs $M\in M_\updownarrow$ (the shared definitions `BoundedParamMDP.Optimal.BMDP` and `BoundedParamMDP.Optimal.Member`), and a policy $\pi:Q\to A$. For an exact MDP $M$ the policy value-iteration operator is $VI_{M,\pi}(v)(p)=R(p)+\gamma\sum_{q\in Q}F^M_{pq}(\pi(p))\,v(q)$ (eq. (7), p. 6).
--
--   Writing $\overline V$ for the set of value functions $v:Q\to\mathbb R$ with the sup norm $\|v\|=\max_{q\in Q}|v(q)|$, an operator $T:\overline V\to\overline V$ is a **contraction mapping** if there is $\lambda$ with $0\le\lambda<1$ such that $\|Tv-Tu\|\le\lambda\|v-u\|$ for all $u,v\in\overline V$ (p. 6).
--
--   **Interval policy evaluation** maps an interval value function $V_\updownarrow=[V_\downarrow,V_\uparrow]$ to the interval value function
--
--   $$IVI_{\updownarrow\pi}(V_\updownarrow)(p)=\Big[\min_{M\in M_\updownarrow}VI_{M,\pi}(V_\downarrow)(p),\ \max_{M\in M_\updownarrow}VI_{M,\pi}(V_\uparrow)(p)\Big]. \tag{27}$$
--
--   Its lower and upper bounds $IVI_{\downarrow\pi}$ and $IVI_{\uparrow\pi}$ depend only on $V_\downarrow$, respectively $V_\uparrow$, and are maps from value functions to value functions (p. 19).
--
--   These are the objects of the interval policy evaluation results (Theorems 10 and 11 and their consequence on p. 22).
--
--   **Formalization Note.** The minima and maxima over $M_\updownarrow$ are the real infimum and supremum over the member subtype `BoundedParamMDP.Optimal.Member B`; this type is nonempty (by the BMDP's sum conditions $\sum_q F_{\downarrow pq}(\alpha)\le1\le\sum_q F_{\uparrow pq}(\alpha)$) and every quantity involved is bounded, so they are the true infimum and supremum (attained, by the paper's Lemma 1). An interval value function is a pair `(V↓, V↑)` of functions $Q\to\mathbb R$; the operators are defined on all pairs. The norm is Mathlib's norm on `Q → ℝ`, which for finite $Q$ is the sup norm (and $0$ when $Q$ is empty). In Lean the contraction modulus is named `c`.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 6 (Section 3, eq. (4) and the definition of a contraction mapping), p. 19 (Section 5.1, eq. (27))

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.IntervalEval

/-- A contraction mapping on the space `V̄ = Q → ℝ` of value functions (Section 3, p. 6):
there is `λ` (written `c`) with `0 ≤ λ < 1` such that `‖T v - T u‖ ≤ λ ‖v - u‖` for all `u, v`, where
`‖v‖ = max_{q ∈ Q} |v(q)|` is the sup norm (4) (Mathlib's norm on `Q → ℝ` for finite `Q`). -/
def IsContraction {Q : Type*} [Fintype Q] (T : (Q → ℝ) → (Q → ℝ)) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ u v : Q → ℝ, ‖T v - T u‖ ≤ c * ‖v - u‖

/-- The lower-bound operator `IVI↓π : V̄ → V̄` of interval policy evaluation (eq. (27), p. 19):
`IVI↓π(v)(p) = min_{M ∈ M↕} VI_{M,π}(v)(p)`, an infimum over the members of `M↕`. -/
noncomputable def IVIlo {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (π : BoundedParamMDP.Optimal.Policy Q A) (v : Q → ℝ) : Q → ℝ :=
  fun p => ⨅ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIpol M.1 π v p

/-- The upper-bound operator `IVI↑π : V̄ → V̄` of interval policy evaluation (eq. (27), p. 19):
`IVI↑π(v)(p) = max_{M ∈ M↕} VI_{M,π}(v)(p)`, a supremum over the members of `M↕`. -/
noncomputable def IVIhi {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (π : BoundedParamMDP.Optimal.Policy Q A) (v : Q → ℝ) : Q → ℝ :=
  fun p => ⨆ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIpol M.1 π v p

/-- Interval policy evaluation `IVI↕π` (eq. (27), p. 19) on interval value functions
`V↕ = [V↓, V↑]`, represented as the pair `(V↓, V↑)` of lower and upper bound functions:
`IVI↕π(V↕)(p) = [min_{M ∈ M↕} VI_{M,π}(V↓)(p), max_{M ∈ M↕} VI_{M,π}(V↑)(p)]`. -/
noncomputable def IVI {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (π : BoundedParamMDP.Optimal.Policy Q A)
    (V : (Q → ℝ) × (Q → ℝ)) : (Q → ℝ) × (Q → ℝ) :=
  (IVIlo B π V.1, IVIhi B π V.2)

end BoundedParamMDP.IntervalEval


