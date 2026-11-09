-- Prove2me | Definitions.Def_PhiSobBayes_IsOpenInterval
-- name    : PhiSobBayes_IsOpenInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:47.679329+00:00
-- url     : https://prove2.me/theorems/02e69325-5353-49cc-b993-0ffef4ce9e9e
-- title:
--   Open interval $J\subseteq\mathbb R$ (possibly unbounded)
-- statement:
--   A set $J\subseteq\mathbb R$ is a **(possibly unbounded) open interval** if it is open, nonempty and order-connected: whenever $a,b\in J$ and $a\le z\le b$, also $z\in J$.
--
--   Examples are $\mathbb R$, $(0,\infty)$, half-lines and bounded intervals $(a,b)$ with $a<b$. The functions $\Phi$ of the mission are defined on such a $J$, and test functions take their values in $J$.
--
--   **Formalization Note** "Interval" is `Set.OrdConnected`, "open" is `IsOpen`; nonemptiness is part of the notion.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 2.1, p.14 (PDF 14); Section 1, p.3 (PDF 3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `J ⊆ ℝ` is a **(possibly unbounded) open interval**: open, order-connected and nonempty.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 2.1, p.14 (PDF 14): "For a (possibly unbounded) open interval 𝐽 ⊆ ℝ, we test
functional inequalities on the class A^J_0"; also Section 1, p.3 (PDF 3), and Theorem 3.1, p.15.

**Formalization Note** "Interval" is `Set.OrdConnected` (convexity in `ℝ`), "open" is `IsOpen`.
Nonemptiness is part of being an interval here: the paper's open intervals `(a, b)` have `a < b`.
`ℝ`, `(0, ∞)`, `(a, b)` and the half-lines all qualify. -/
def IsOpenInterval (J : Set ℝ) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ J.Nonempty

end PhiSobBayes


