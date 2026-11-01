-- Prove2me | Definitions.Def_SimpleMenus_ConstraintQualification
-- name    : SimpleMenus_ConstraintQualification
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:56.174381+00:00
-- url     : https://prove2.me/theorems/e3878671-2d2b-495f-be3e-cc24a9cb101e
-- title:
--   Constraint qualification (correction): step functions or a strictly feasible law
-- statement:
--   A function $f$ is a **step function** on $[0,\bar v]$ if some finite $P\subseteq[0,\bar v]$ makes $f$ constant on every open piece cut by $P$.
--
--   The family $\phi_1,\dots,\phi_K$ satisfies the **constraint qualification** if either every $\phi_k$ is a step function, or there is a law $F_0\in\mathcal F$ with
--
--   $$\int\phi_k\,dF_0>0\quad\text{for every }k\text{ such that }\phi_k\text{ is not a step function.}$$
--
--   This condition is not in the paper. It is added to Proposition 1, the duality step of its proof and Theorem 1, which are false without it. Counterexample: $K=1$, $0<c<\bar v$, $\phi(w)=\min(w-c,0)$ (bounded, continuous, nondecreasing), one price level $c$ with probability $1$. Then $\mathcal F=\mathcal P([c,\bar v])$ and $\mathrm{CR}=c/\bar v$, while Problems (3) and (4) both have value $0$. The support, quantile and multi-segment examples (step functions) and the mean example with $\mu<\bar v$ ($F_0=\delta_{\bar v}$) satisfy it.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, correction to Proposition 1 (p.10) and Theorem 1 (p.11); counterexample in the mission description

import Mathlib
import Definitions.Def_SimpleMenus_IsPiece
import Definitions.Def_SimpleMenus_ambiguitySet

open MeasureTheory Set

namespace SimpleMenus

/-- `f` is a step function on `[0, v̄]`: constant on each open piece cut by some finite
`P ⊆ [0, v̄]` (the support, quantile and multi-segment examples (I), (III), (IV) of
Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, pp.9–10, are of this kind). -/
def IsStep (vbar : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ P : Finset ℝ, (P : Set ℝ) ⊆ Icc 0 vbar ∧
    ∀ a b, IsPiece vbar P a b → ∃ c : ℝ, ∀ w ∈ Ioo a b, f w = c

/-- **Correction (constraint qualification).** Either every `ϕ_k` is a step function, or some law
`F₀ ∈ 𝓕` satisfies every constraint that is not a step function strictly:
`∫ ϕ_k dF₀ > 0`.

This hypothesis is not in Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3. It is added to Proposition 1, the duality step of its proof
(p.ec7) and Theorem 1, which are false without it. Counterexample (CE1): `K = 1`, `0 < c < v̄`,
`ϕ(w) = min(w − c, 0)` (bounded, continuous, nondecreasing: Assumption 1 holds, no breakpoint),
`n = 1`, `V = {c}`, `x = 1`. Then `𝓕 = P([c, v̄])`, `CR = c / v̄`, while (3) and (4) have value `0`
(in (3) the constraints at `p ∈ (0, c]`, `w ↑ c`, force `r·p ≤ 0`). The printed proof applies Sion's theorem
to feasible sets of which neither is compact. -/
def ConstraintQualification (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) : Prop :=
  (∀ k, IsStep vbar (phi k)) ∨
    ∃ F₀ ∈ ambiguitySet vbar phi, ∀ k, IsStep vbar (phi k) ∨ 0 < ∫ w, phi k w ∂F₀

end SimpleMenus


