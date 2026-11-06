-- Prove2me | Definitions.Def_IntervalToDynamic_LossMode
-- name    : IntervalToDynamic_LossMode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:44.441204+00:00
-- url     : https://prove2.me/theorems/c70e292a-266c-49ca-9000-ff6eaa476976
-- title:
--   The three loss classes: convex, $\alpha$-exp-concave, $\lambda$-strongly convex
-- statement:
--   A **loss mode** selects one of the three regimes of the paper: convex losses, $\alpha$-exp-concave losses, or $\lambda$-strongly convex losses. The curved modes carry their coefficient.
--
--   Every object that depends on the regime (the surrogate $h_t$, the coefficients of Table 2, the class of losses the inner algorithm must handle) is a function of the mode, so results that hold in all regimes are stated once.
--
--   **Formalization Note** The coefficient $\lambda$ is called `lam`, because `λ` is reserved in Lean.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Assumptions 1–2, pp.7–8; Eqs. (10)–(12), p.8

import Mathlib

namespace IntervalToDynamic

/-- The three loss classes of the paper. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Assumptions 1–2, pp.7–8, and Eqs. (10)–(12), p.8.

**Formalization Note.** The constructor carries the curvature coefficient of its regime: `α` of
exp-concavity, `lam` (the paper's `λ`, a reserved word in Lean) of strong convexity. A single type
lets Theorem 5 and Lemma 14 be stated once for all three regimes. -/
inductive LossMode where
  /-- convex losses -/
  | convex
  /-- `α`-exp-concave losses -/
  | expConcave (α : ℝ)
  /-- `lam`-strongly convex losses -/
  | stronglyConvex (lam : ℝ)

end IntervalToDynamic


