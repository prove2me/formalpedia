-- Prove2me | Definitions.Def_CondBasedProd_IsOptRate
-- name    : CondBasedProd_IsOptRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:40.543094+00:00
-- url     : https://prove2.me/theorems/fa285d4b-0edf-40fc-bbf4-bd574eb9ac0d
-- title:
--   The optimal production rates: maximizers of the HJB bracket, their extremes and the strong set order
-- statement:
--   For $x<\xi$, a rate $s\in\mathcal S$ is an **optimal production rate** at $(x,t)$ under base rate $\lambda$ if it maximizes the bracket of the HJB equation (2),
--   $$
--   s'\mapsto r(s')-\lambda f(s')\Delta_\lambda(x,t)\quad\text{over }\mathcal S.
--   $$
--   At $x=\xi$ the only optimal rate is $s=0$. The set of optimal rates is written $\mathrm{Opt}_\lambda(x,t)$, and $\bar s^*_\lambda(x,t)=\sup\mathrm{Opt}_\lambda(x,t)$, $\underline s^*_\lambda(x,t)=\inf\mathrm{Opt}_\lambda(x,t)$. An auxiliary predicate says that $s$ maximizes $r(\cdot)-f(\cdot)y$ over $\mathcal S$ for a real $y$; the bracket above is the case $y=\lambda\Delta_\lambda(x,t)$.
--
--   A set $B$ lies below $A$ in the **strong set order** if, for $s\in A$ and $s'\in B$, one has $\min(s,s')\in B$ and $\max(s,s')\in A$. This is the sense in which the sets of maximizers decrease.
--
--   **Formalization Note** An optimal policy determines its rate only for almost every $t$, so the rate at a single state is defined through the bracket.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 1 and the following paragraph, display (2), p.10; App. A.1, p.34; App. A.9, p.39

import Mathlib
import Definitions.Def_CondBasedProd_Policy

open Set

namespace CondBasedProd

/-- `s` maximizes the bracket `r(s') − f(s') y` over `𝒮 = [0, s̄]`. With `y = λ Δ_λ(x,t)` this is the
bracket `r(s) − λ f(s) Δ_λ(x,t)` of (2), p.10. -/
def IsBracketMax (M : Model) (y s : ℝ) : Prop :=
  s ∈ Icc 0 M.sbar ∧ ∀ s' ∈ Icc 0 M.sbar, M.r s' - M.f s' * y ≤ M.r s - M.f s * y

/-- `s` is an **optimal production rate** at state `(x,t)` under base rate `lam`
(arXiv:2308.07507v2, p.10): "a solution to (2), which we denote by `s*_λ(x,t)`", i.e. a maximizer of
the bracket of (2) for `x < ξ`.

**Formalization Note.** At `x = ξ` the only admissible action is `s = 0` (App. A.1, p.34), so
`Opt_λ(ξ,t) = {0}`; `Δ_λ(ξ,t)` is never read. The optimal rate of a policy is determined only for
almost every `t`, so the rate at a state is defined through the bracket and not through a policy. -/
def IsOptRate (M : Model) (lam : ℝ) (x : ℕ) (t s : ℝ) : Prop :=
  if x < M.ξ then IsBracketMax M (lam * delta M lam x t) s else s = 0

/-- `Opt_λ(x,t)`, the set of optimal production rates at `(x,t)`. -/
def optRateSet (M : Model) (lam : ℝ) (x : ℕ) (t : ℝ) : Set ℝ :=
  {s | IsOptRate M lam x t s}

/-- The greatest optimal production rate `s̄*_λ(x,t)`. -/
noncomputable def optRateMax (M : Model) (lam : ℝ) (x : ℕ) (t : ℝ) : ℝ :=
  sSup (optRateSet M lam x t)

/-- The least optimal production rate `s̲*_λ(x,t)`. -/
noncomputable def optRateMin (M : Model) (lam : ℝ) (x : ℕ) (t : ℝ) : ℝ :=
  sInf (optRateSet M lam x t)

/-- `B` lies **below `A` in the strong set order**: for `s ∈ A` and `s' ∈ B`, `min s s' ∈ B` and
`max s s' ∈ A`. This is the sense in which "decreasing" is read for the sets of maximizers in
Theorem 1, p.12 (the maximizers need not be unique). -/
def StrongSetBelow (B A : Set ℝ) : Prop :=
  ∀ s ∈ A, ∀ s' ∈ B, min s s' ∈ B ∧ max s s' ∈ A

end CondBasedProd


