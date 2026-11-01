-- Prove2me | Definitions.Def_ConstrainedTrading_repValue
-- name    : ConstrainedTrading_repValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:50.03398+00:00
-- url     : https://prove2.me/theorems/1ef5591a-0cbe-448f-976a-41d70ea0f0ef
-- title:
--   Value $\sum_z \lambda_z f(z)$ of a weighted set of integer points
-- statement:
--   For $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$, a finite set $S\subseteq\mathbb Z^E$ and weights $\lambda$, the **value** is
--   $$
--   \sum_{z\in S}\lambda_z f(z)\in[-\infty,\infty),
--   $$
--   computed in the extended reals. It is the objective of Definition 2.8.
--
--   **Formalization Note** The value lives in `EReal`; $f(z)=-\infty$ with $\lambda_z>0$ makes the whole value $-\infty$ (in Mathlib $\bot+a=\bot$ for every $a$). $+\infty$ never occurs.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.8, p.5

import Mathlib

namespace ConstrainedTrading

/-- The **value** `Σ_{z∈S} λ_z f(z)` of a weighted finite set of integer points under a valuation
`f : ℤ^E → ℝ ∪ {−∞}` (the objective of Definition 2.8, Kizilkale–Vohra, *Constrained Trading
Networks*, arXiv:2008.09757v1, p.5), computed in the extended reals.

**Formalization Note** `f z : WithBot ℝ` is sent to `EReal` (`⊥ ↦ ⊥`, `r ↦ r`), and the sum is
taken in `EReal`. The weights are used on their support, where they are positive, so
`λ_z · (−∞) = −∞` and a single `−∞` term makes the value `−∞` (in Mathlib `⊥ + a = ⊥` for
every `a : EReal`; `⊤` never occurs since `f` has no `+∞` value). -/
noncomputable def repValue {E : Type*} (f : (E → ℤ) → WithBot ℝ) (S : Finset (E → ℤ))
    (wt : (E → ℤ) → ℝ) : EReal :=
  ∑ z ∈ S, ((wt z : ℝ) : EReal) * WithBot.recBotCoe (⊥ : EReal) (fun r : ℝ => (r : EReal)) (f z)

end ConstrainedTrading


