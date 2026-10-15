-- Prove2me | Definitions.Def_PrizeAlloc_Param_ParametricRule
-- name    : PrizeAlloc_Param_ParametricRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:14.243977+00:00
-- url     : https://prove2.me/theorems/2581106b-d1b6-474f-b292-c241a7c7a39e
-- title:
--   pp. 21–22 — parametric rules and proportional rules
-- statement:
--   A **parametric representation** is a sequence of functions $f_1,f_2,\dots:\mathbb R_+\to\mathbb R_+$, each continuous and non-decreasing, with $f_1(x)=x$ for each $x$ and $f_{k+1}(x)\le f_k(x)$ for each $k$ and each $x\ge 0$.
--
--   A prize allocation rule $\varphi$ is the **parametric rule with representation** $f_1,f_2,\dots$ if for each competition $(N,\mathcal R,E)$ and each competitor $i\in N$,
--
--   $$\varphi_i(N,\mathcal R,E)=f_{\mathcal R(i)}(x),\qquad\text{where } x\in\mathbb R_+ \text{ is such that } \sum_{k=1}^{|N|}f_k(x)=E.$$
--
--   A rule is **parametric** if it has some parametric representation. The winner receives $x$; position $k$ receives $f_k(x)$. Equal Division ($f_k(x)=x$), Winner-Takes-All ($f_1(x)=x$, $f_k=0$ for $k\ge2$) and the rule of Example 6 ($f_1(x)=x$, $f_k(x)=\max\{0,x-k\}$ for $k\ge 2$) are parametric.
--
--   A rule is **proportional** if there are $\lambda_1,\lambda_2,\dots\in\mathbb R_+$ with $\lambda_1>0$ and $\lambda_{k+1}\le\lambda_k$ for each $k$ such that for each competition $(N,\mathcal R,E)$ and each $i\in N$,
--
--   $$\varphi_i(N,\mathcal R,E)=\frac{\lambda_{\mathcal R(i)}}{\sum_{k=1}^{|N|}\lambda_k}\,E.$$
--
--   These are the families characterized by Theorem 3 and Corollary 8.
--
--   **Formalization Note** Both sequences are indexed from 1 as on the page; the entries $f_0$ and $\lambda_0$ are unused and unconstrained. Continuity, monotonicity, nonnegativity and $f_1(x)=x$ are required on $\mathbb R_+=[0,\infty)$ only, since $f_k:\mathbb R_+\to\mathbb R_+$. "Where $x\in\mathbb R_+$ is such that" is encoded as the existence of such an $x$ with the prize formula; since $\sum_{k\le|N|}f_k$ is continuous, strictly increasing (because $f_1(x)=x$) and vanishes at $0$, this $x$ is unique, so the existential and universal readings agree. The rule is required to be a prize allocation rule separately, in each theorem.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 21 (Parametric rules), p. 22 (Proportional rules)

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting

namespace PrizeAlloc.Param

variable {U : Type*} [DecidableEq U]

/-- `f 1, f 2, … : ℝ₊ → ℝ₊` continuous and non-decreasing, with `f 1 x = x` and
`f (k + 1) x ≤ f k x` (p. 21). The index is 1-based as on the page; `f 0` is unused. -/
def IsParamRepresentation (f : ℕ → ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → f 1 x = x) ∧
  ∀ k, 1 ≤ k → ContinuousOn (f k) (Set.Ici 0) ∧ MonotoneOn (f k) (Set.Ici 0) ∧
    ∀ x, 0 ≤ x → 0 ≤ f k x ∧ f (k + 1) x ≤ f k x

/-- `φ` is the parametric rule with representation `f` (p. 21): on each competition `(l, E)`,
`φ_i = f_{R(i)}(x)` where `x ≥ 0` satisfies `∑_{k=1}^{|N|} f_k(x) = E`. -/
def IsParamRuleWith (f : ℕ → ℝ → ℝ) (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E →
    ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, f k x) = E ∧ ∀ i ∈ l, φ l E i = f (PrizeAlloc.Interval.pos l i) x

/-- Parametric rules (p. 21). -/
def IsParamRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ f, IsParamRepresentation f ∧ IsParamRuleWith f φ

/-- Proportional rules (p. 22): `λ 1, λ 2, … ≥ 0` with `λ 1 > 0`, `λ (k + 1) ≤ λ k`, and
`φ_i = λ_{R(i)} / (∑_{k=1}^{|N|} λ_k) · E`. 1-based; `λ 0` is unused. -/
def IsProportionalRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ lam : ℕ → ℝ, 0 < lam 1 ∧ (∀ k, 1 ≤ k → 0 ≤ lam k ∧ lam (k + 1) ≤ lam k) ∧
    ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E → ∀ i ∈ l,
      φ l E i = lam (PrizeAlloc.Interval.pos l i) / (∑ k ∈ Finset.Icc 1 l.length, lam k) * E

end PrizeAlloc.Param


