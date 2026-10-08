-- Prove2me | Definitions.Def_BoundedParamMDP_IntervalEval_IntervalValueIteration
-- name    : BoundedParamMDP_IntervalEval_IntervalValueIteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:07:59.511911+00:00
-- url     : https://prove2.me/theorems/c78de12a-56a5-4091-9e19-1bbd86ee0bdf
-- title:
--   Interval value iteration $IVI_{\updownarrow opt}$, $IVI_{\updownarrow pes}$, the action sets $\rho_V$, $\sigma_V$, and the operators $IVI_{\downarrow opt,V}$, $IVI_{\uparrow pes,V}$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with a finite nonempty action set $A$. Closed intervals are compared by the two total orders of eq. (17):
--
--   $$[l_1,u_1]\le_{opt}[l_2,u_2]\iff u_1<u_2\ \text{or}\ (u_1=u_2\ \text{and}\ l_1\le l_2),\qquad [l_1,u_1]\le_{pes}[l_2,u_2]\iff l_1<l_2\ \text{or}\ (l_1=l_2\ \text{and}\ u_1\le u_2).$$
--
--   For an interval value function $V_\updownarrow=[V_\downarrow,V_\uparrow]$, a state $p$ and an action $\alpha$, let $I_\alpha(p)=\big[\min_{M\in M_\updownarrow}VI_{M,\alpha}(V_\downarrow)(p),\ \max_{M\in M_\updownarrow}VI_{M,\alpha}(V_\uparrow)(p)\big]$. **Optimistic** and **pessimistic interval value iteration** are
--
--   $$IVI_{\updownarrow opt}(V_\updownarrow)(p)=\max_{\alpha\in A,\ \le_{opt}}I_\alpha(p),\qquad IVI_{\updownarrow pes}(V_\updownarrow)(p)=\max_{\alpha\in A,\ \le_{pes}}I_\alpha(p). \tag{28, 29}$$
--
--   $IVI_{\uparrow opt}$ and $IVI_{\downarrow opt}$ denote the upper and lower bounds of $IVI_{\updownarrow opt}$, and similarly for the pessimistic operator. For a value function $V$,
--
--   $$\rho_V(p)=\operatorname*{argmax}_{\alpha\in A}\max_{M\in M_\updownarrow}VI_{M,\alpha}(V)(p),\qquad \sigma_V(p)=\operatorname*{argmax}_{\alpha\in A}\min_{M\in M_\updownarrow}VI_{M,\alpha}(V)(p)$$
--
--   are the sets of actions maximizing the upper, respectively lower, bound at $p$ (eqs. (23), (24), (31)). With $[V_1,V_2]$ the interval value function $p\mapsto[V_1(p),V_2(p)]$, the maps $IVI_{\downarrow opt,V},IVI_{\uparrow pes,V}:\overline V\to\overline V$ are
--
--   $$IVI_{\downarrow opt,V}(V')=IVI_{\downarrow opt}([V',V]),\qquad IVI_{\uparrow pes,V}(V')=IVI_{\uparrow pes}([V,V']).$$
--
--   These operators are the subject of the convergence results for interval value iteration (Lemma 4 and Theorem 13).
--
--   **Formalization Note.** The maximum for $\le_{opt}$ is computed as the supremum over the finite action set of the pairs $(u,l)$ in Lean's lexicographic order, then read back as the interval $[l,u]$; for $\le_{pes}$ the pairs $(l,u)$ are used. The minima and maxima over $M_\updownarrow$ are the real infimum and supremum over the nonempty member type. $\rho_V(p)$ and $\sigma_V(p)$ are sets of actions. The interval $[V',V]$ may be improper ($V'(p)>V(p)$); the operators are defined for every pair of functions, as the paper uses them.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 16 eq. (17), p. 18 eqs. (23)–(24), pp. 22–24 (Section 5.2, eqs. (28)–(31))

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.IntervalEval

/-- The interval that action `α` proposes at state `p` for the interval value function
`V↕ = [V↓, V↑]` (the pair `(V↓, V↑)`), the bracket inside eqs. (28)–(29), p. 23:
`[min_{M ∈ M↕} VI_{M,α}(V↓)(p), max_{M ∈ M↕} VI_{M,α}(V↑)(p)]`, as the pair
(lower end, upper end), with `min`/`max` the infimum/supremum over the members of `M↕`. -/
noncomputable def candInterval {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (V : (Q → ℝ) × (Q → ℝ)) (p : Q) (α : A) : ℝ × ℝ :=
  (⨅ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V.1 p,
    ⨆ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V.2 p)

/-- Optimistic interval value iteration `IVI↕opt` (eq. (28), p. 23):
`IVI↕opt(V↕)(p) = max_{α ∈ A, ≤opt} candInterval V↕ p α`, the maximum over the finite nonempty
action set for the total order `≤opt` of eq. (17), p. 16
(`[l₁, u₁] ≤opt [l₂, u₂] ⇔ u₁ < u₂ ∨ (u₁ = u₂ ∧ l₁ ≤ l₂)`), i.e. the lexicographic order on
(upper end, lower end). The result at `p` is the pair (lower end, upper end). -/
noncomputable def IVIopt {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (V : (Q → ℝ) × (Q → ℝ)) : Q → ℝ × ℝ :=
  fun p =>
    let m := Finset.univ.sup' Finset.univ_nonempty
      (fun α : A => toLex ((candInterval B V p α).2, (candInterval B V p α).1))
    ((ofLex m).2, (ofLex m).1)

/-- Pessimistic interval value iteration `IVI↕pes` (eq. (29), p. 23):
`IVI↕pes(V↕)(p) = max_{α ∈ A, ≤pes} candInterval V↕ p α`, the maximum for the total order
`≤pes` of eq. (17), p. 16 (`[l₁, u₁] ≤pes [l₂, u₂] ⇔ l₁ < l₂ ∨ (l₁ = l₂ ∧ u₁ ≤ u₂)`), i.e. the
lexicographic order on (lower end, upper end). The result at `p` is the pair
(lower end, upper end). -/
noncomputable def IVIpes {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (V : (Q → ℝ) × (Q → ℝ)) : Q → ℝ × ℝ :=
  fun p =>
    let m := Finset.univ.sup' Finset.univ_nonempty
      (fun α : A => toLex ((candInterval B V p α).1, (candInterval B V p α).2))
    ((ofLex m).1, (ofLex m).2)

/-- `ρ_V(p) = argmax_{α ∈ A} max_{M ∈ M↕} VI_{M,α}(V)(p)` (eqs. (23), p. 18, and (31), p. 24):
the set of actions maximizing the upper bound at `p`. -/
def rho {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (V : Q → ℝ) (p : Q) : Set A :=
  {α | ∀ β : A, (⨆ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 β V p) ≤ ⨆ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V p}

/-- `σ_V(p) = argmax_{α ∈ A} min_{M ∈ M↕} VI_{M,α}(V)(p)` (eq. (24), p. 18): the set of
actions maximizing the lower bound at `p`. -/
def sigma {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (V : Q → ℝ) (p : Q) : Set A :=
  {α | ∀ β : A, (⨅ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 β V p) ≤ ⨅ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V p}

/-- `IVI↓_{opt,V} : V̄ → V̄` (p. 23): for a value function `V`, it maps `V'` to the lower
bound `IVI↓opt([V', V])` of `IVI↕opt` applied to the interval value function
`[V', V] : p ↦ [V'(p), V(p)]`. -/
noncomputable def IVIloOptV {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (V : Q → ℝ) (V' : Q → ℝ) : Q → ℝ :=
  fun p => (IVIopt B (V', V) p).1

/-- `IVI↑_{pes,V} : V̄ → V̄` (p. 23): for a value function `V`, it maps `V'` to the upper
bound `IVI↑pes([V, V'])` of `IVI↕pes` applied to the interval value function
`[V, V'] : p ↦ [V(p), V'(p)]`. -/
noncomputable def IVIhiPesV {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A)
    (V : Q → ℝ) (V' : Q → ℝ) : Q → ℝ :=
  fun p => (IVIpes B (V, V') p).2

end BoundedParamMDP.IntervalEval


