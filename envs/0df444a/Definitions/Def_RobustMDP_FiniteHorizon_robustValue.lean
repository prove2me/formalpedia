-- Prove2me | Definitions.Def_RobustMDP_FiniteHorizon_robustValue
-- name    : RobustMDP_FiniteHorizon_robustValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:18:18.870583+00:00
-- url     : https://prove2.me/theorems/33bdb33d-5836-4fda-97b8-e92a9299aca9
-- title:
--   The robust recursion (7) and the worst-case evaluation recursion (10)
-- statement:
--   The **robust dynamic programming recursion** (7) computes value functions $v_0,\dots,v_N\in\mathbb R^n$ backwards from $v_N=c_N$:
--
--   $$
--   v_t(i)=\min_{a\in\mathcal A}\big(c_t(i,a)+\sigma_{\mathcal P_i^a}(v_{t+1})\big),\qquad i\in\mathcal X,\ t\in T .
--   $$
--
--   For a fixed controller policy $\pi=(\mathbf a_0,\dots,\mathbf a_{N-1})$, the **worst-case evaluation recursion** (10) computes $v_t^\pi$ backwards from $v_N^\pi=c_N$:
--
--   $$
--   v_t^\pi(i)=c_t(i,\mathbf a_t(i))+\sigma_{\mathcal P_i^{\mathbf a_t(i)}}(v_{t+1}^\pi),\qquad i\in\mathcal X,\ t\in T .
--   $$
--
--   These are the paper's algorithm; Theorem 1 identifies their values with the robust game values.
--
--   **Formalization Note** The terminal value $v_N=c_N$ is not printed in Theorem 1; it is implicit in its proof and explicit in Step 1 of the algorithm (p. 785, "Initialize the value function to its terminal value $\hat v_N=c_N$"). The stage index is a natural number; only $t\le N$ is meaningful, and for $t\ge N$ the value is $c_N$. The minimum over the finite nonempty action set is Lean's `⨅ a`.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, Theorem 1, Eqs. (7) and (10); terminal value from p. 785, Step 1

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model

namespace RobustMDP.FiniteHorizon

/-- The robust dynamic programming recursion (7), p. 783, with terminal value `v_N = c_N`
(stated in Step 1 of the algorithm, p. 785):
`v_t(i) = min_{a ∈ 𝒜} (c_t(i, a) + σ_{𝒫_i^a}(v_{t+1}))` for `t < N`, `v_N = c_N`.
The minimum over the finite nonempty action set is written `⨅ a`. Only `t ≤ N` is meaningful;
for `t ≥ N` the value is `c_N`. -/
noncomputable def Model.robustValue {n N : ℕ} {A : Type} (M : Model n N A) (t : ℕ) :
    Fin n → ℝ :=
  if h : t < N then
    fun i => ⨅ a : A, (M.cost ⟨t, h⟩ i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)))
  else M.terminalCost
termination_by N - t

/-- The worst-case evaluation recursion (10), p. 783, for a fixed controller policy `π`, with
terminal value `v_N^π = c_N`:
`v_t^π(i) = c_t(i, 𝐚_t(i)) + σ_{𝒫_i^{𝐚_t(i)}}(v_{t+1}^π)` for `t < N`. Only `t ≤ N` is meaningful;
for `t ≥ N` the value is `c_N`. -/
noncomputable def Model.policyValue {n N : ℕ} {A : Type} (M : Model n N A)
    (π : ControlPolicy n N A) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then
    fun i => M.cost ⟨t, h⟩ i (π ⟨t, h⟩ i) +
      Shared.supportFunction (M.rows (π ⟨t, h⟩ i) i) (M.policyValue π (t + 1))
  else M.terminalCost
termination_by N - t

end RobustMDP.FiniteHorizon


