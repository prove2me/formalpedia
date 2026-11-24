-- Prove2me | Definitions.Def_SurelyBetter_CLB_Supplement_SalesAgent
-- name    : SurelyBetter_CLB_Supplement_SalesAgent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:47:29.94981+00:00
-- url     : https://prove2.me/theorems/1b518a4f-15b1-46d7-a759-8c6c51d9802b
-- title:
--   §2, Table 1 and Theorem 1, pp. 7621, 7626 — sales-agent acts, the optimal strategy correspondence q*, and the set of acts H
-- statement:
--   This file fixes the sales-agent model of §2 in utility space, on top of the published model `SurelyBetter.CLB.Model`.
--
--   There are four states $s_1,s_2,s_3,s_4$: in $s_1$ only sale 1 succeeds if worked on, in $s_2$ only sale 2, in $s_3$ either sale, in $s_4$ neither. Payments are nonnegative reals and $u$ is the agent's utility of a payment. By Table 1, working on sale 1 under the payment $w_1$ pays $w_1$ in $s_1$ and $s_3$ and $0$ otherwise, and working on sale 2 under $w_2$ pays $w_2$ in $s_2$ and $s_3$ and $0$ otherwise. Their utility profiles are
--   $$\mathrm{sale}_1(w_1)=(u(w_1),u(0),u(w_1),u(0)),\qquad \mathrm{sale}_2(w_2)=(u(0),u(w_2),u(w_2),u(0)).$$
--
--   1. **Optimal strategy correspondence.** A strategy is the probability $q\in[0,1]$ of working on sale 1, i.e. the mixture $q\,\mathrm{sale}_1(w_1)+(1-q)\,\mathrm{sale}_2(w_2)$. For a preference represented by $V$ on utility profiles, $q^*(w_1,w_2)$ is the set of all $q\in[0,1]$ whose mixture is optimal among all such mixtures (the optimal-mixture set $\alpha^*_{f,g}$ of the published model with $f=\mathrm{sale}_1(w_1)$, $g=\mathrm{sale}_2(w_2)$).
--   2. **The set $H$ of Theorem 1.** $H$ is the set of utility profiles $v$ with values in $U=u(X)$ such that $v(s)\ge0$ for all $s$, $v(s_4)=0$, and $v$ is measurable with respect to $\{\{s_1,s_3\},\{s_2,s_4\}\}$ (that is, $v(s_1)=v(s_3)$ and $v(s_2)=v(s_4)$) or with respect to $\{\{s_2,s_3\},\{s_1,s_4\}\}$ (that is, $v(s_2)=v(s_3)$ and $v(s_1)=v(s_4)$).
--
--   These objects carry Theorem 1, which links monotonicity in optimal mixtures on $H$ to the monotone response of $q^*$ to compensation.
--
--   **Formalization Note** The states $s_1,\dots,s_4$ are `0, 1, 2, 3 : Fin 4`. The payment utility $u$ is a function `ℝ → ℝ`; only its values at nonnegative payments are used. Payment $0$ enters the profiles as $u(0)$, as in Table 1; Theorem 1 assumes $u(0)=0$.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7621, §2 and Table 1 (q*); p. 7626, Theorem 1 (the set H)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB

/-- §2, Table 1, p. 7621: the utility profile of working on sale 1 under payment `w₁`.
The states `s₁, s₂, s₃, s₄` are `0, 1, 2, 3 : Fin 4`; the agent is paid `w₁` in `s₁` and `s₃`
and `0` in `s₂` and `s₄`, so the profile is `(u(w₁), u(0), u(w₁), u(0))`. -/
def sale1Prof (u : ℝ → ℝ) (w₁ : ℝ) : Fin 4 → ℝ := ![u w₁, u 0, u w₁, u 0]

/-- §2, Table 1, p. 7621: the utility profile of working on sale 2 under payment `w₂`:
`(u(0), u(w₂), u(w₂), u(0))`. -/
def sale2Prof (u : ℝ → ℝ) (w₂ : ℝ) : Fin 4 → ℝ := ![u 0, u w₂, u w₂, u 0]

/-- §2, p. 7621: the sales agent's optimal strategy correspondence `q*(w₁, w₂)`, the set of all
probabilities `q ∈ [0,1]` of working on sale 1 such that the mixture
`q · sale 1 + (1 − q) · sale 2` is optimal for the preference represented by `V`. -/
def qStar (V : (Fin 4 → ℝ) → ℝ) (u : ℝ → ℝ) (w₁ w₂ : ℝ) : Set ℝ :=
  optMix V (sale1Prof u w₁) (sale2Prof u w₂)

/-- Theorem 1, p. 7626: the utility profiles of the acts in
`H = {h : u(h(s)) ≥ 0 for all s, u(h(s₄)) = 0, and h is measurable with respect to
{{s₁,s₃},{s₂,s₄}} or {{s₂,s₃},{s₁,s₄}}}`. Measurability with respect to a partition means
being constant on each of its blocks. -/
def salesActs (U : Set ℝ) : Set (Fin 4 → ℝ) :=
  {v | v ∈ Profiles U ∧ (∀ s, 0 ≤ v s) ∧ v 3 = 0 ∧
    ((v 0 = v 2 ∧ v 1 = v 3) ∨ (v 1 = v 2 ∧ v 0 = v 3))}

end SurelyBetter.CLB.Supplement


