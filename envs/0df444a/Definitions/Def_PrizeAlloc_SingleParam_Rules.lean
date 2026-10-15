-- Prove2me | Definitions.Def_PrizeAlloc_SingleParam_Rules
-- name    : PrizeAlloc_SingleParam_Rules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:09.439666+00:00
-- url     : https://prove2.me/theorems/7ec731e5-4ea4-424e-938c-c8710dcc3e07
-- title:
--   p. 18 — single-parametric prize allocation rules and their representations f
-- statement:
--   Single-parametric rules (p. 18).
--
--   A **representation** is a continuous, non-decreasing function $f:\mathbb R_+\to\mathbb R_+$ with $f(x)\le x$ for each $x\ge 0$. Write $f^{(0)}(x)=x$ and $f^{(k)}(x)=f(f^{(k-1)}(x))$. A prize allocation rule $\varphi$ is the **single-parametric rule with representation $f$** if for each competition $(N,\mathcal R,E)$ there is $x\in\mathbb R_+$ with
--   $$\sum_{k=1}^{|N|}f^{(k-1)}(x)=E\qquad\text{and}\qquad \varphi_i(N,\mathcal R,E)=f^{(\mathcal R(i)-1)}(x)\ \text{ for each } i\in N.$$
--   So the winner gets $x$, the runner-up $f(x)$, the third $f(f(x))$, and so on, with $x$ chosen to exhaust the endowment. $\varphi$ is a **single-parametric rule** if it is the single-parametric rule with some representation $f$.
--
--   Examples from p. 18: Equal Division ($f(x)=x$), Winner-Takes-All ($f(x)=0$), Winner-Takes-Surplus with parameter $a$ ($f(x)=\min\{a,x\}$), and the arithmetic rule of Example 4 ($f(x)=\max\{0,x-1\}$).
--
--   **Formalization Note** $f$ is a function $\mathbb R\to\mathbb R$ constrained only on $[0,\infty)$: continuity and monotonicity are `ContinuousOn`/`MonotoneOn` on $[0,\infty)$, and $0\le f(x)\le x$ for $x\ge 0$; values at negative arguments are never used, because $f$ maps $[0,\infty)$ into itself. The sum $\sum_{k=1}^{|N|}f^{(k-1)}(x)$ is written with the shifted index $k=0,\dots,|N|-1$ and Lean's iterate `f^[k]`. "$x$ is chosen such that" is encoded as existence of such an $x$; the $x$ is in fact unique (see the item "x in the single-parametric rule is well defined").
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 18, Single-Parametric rules

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting

namespace PrizeAlloc.SingleParam

variable {U : Type*} [DecidableEq U]

/-- A representation (p. 18): `f : ℝ₊ → ℝ₊` continuous and non-decreasing with `f x ≤ x`,
written as a function on `ℝ` whose behaviour is constrained on `[0, ∞)` only. -/
def IsRepresentation (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ f x ∧ f x ≤ x

/-- `φ` is the single-parametric rule with representation `f` (p. 18): on every competition
`(l, E)` there is `x ≥ 0` with `∑_{k=1}^{|N|} f^{(k-1)}(x) = E` and `φ_i = f^{(R(i)-1)}(x)`. -/
def IsSingleParamRuleWith (f : ℝ → ℝ) (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E →
    ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧ ∀ i ∈ l, φ l E i = f^[PrizeAlloc.Interval.pos l i - 1] x

/-- Single-parametric rules (p. 18). -/
def IsSingleParamRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ f, IsRepresentation f ∧ IsSingleParamRuleWith f φ

end PrizeAlloc.SingleParam


