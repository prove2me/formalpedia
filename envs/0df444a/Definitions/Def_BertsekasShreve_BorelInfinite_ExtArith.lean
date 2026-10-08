-- Prove2me | Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
-- name    : BertsekasShreve_BorelInfinite_ExtArith
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:47.267437+00:00
-- url     : https://prove2.me/theorems/977108a3-721c-4d9d-9b34-55eb28bd85b8
-- title:
--   Extended-real arithmetic with ∞ − ∞ = ∞ (Section 2.1 and Eq. (42) of Ch. 7)
-- statement:
--   The book computes in $R^* = [-\infty, \infty]$ with the convention
--   $$-\infty + \infty = \infty - \infty = \infty$$
--   (Section 2.1, and Eq. (42) of Chapter 7). This file provides
--
--   1. the sum $a + b$ of $a, b \in R^*$ with this convention;
--   2. the difference $a - b$ of two numbers $a, b \in [0, \infty]$, again with $\infty - \infty = \infty$.
--
--   The extended integral of Eq. (43) of Chapter 7, $\int f\,dp = \int f^+\,dp - \int f^-\,dp$ with the same convention, is the published definition `DupacovaWets.Consistency.expect`, which this mission references. These are the operations in which the cost $J_\pi$ and the dynamic programming operators $T$ and $T_\mu$ are written.
--
--   **Formalization Note** Mathlib's `EReal` sets $\bot + \top = \bot$, the opposite of the book's convention, so the sum returns $\top$ explicitly whenever a summand is $\top$; otherwise it is `EReal` addition.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 26, Section 2.1 item (6); p. 139, Section 7.4.4, Eq. (42) of Chapter 7

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.BorelInfinite

open MeasureTheory

/-- The difference `a − b` of two nonnegative extended reals with the book's convention
`∞ − ∞ = ∞` (Eq. (42) of Chapter 7), as an element of `R* = EReal`. (The extended integral
`∫ f dp = ∫ f⁺ dp − ∫ f⁻ dp` of Eq. (43) of Chapter 7, which uses the same convention, is the
published definition `DupacovaWets.Consistency.expect`.) -/
noncomputable def bsub (a b : ENNReal) : EReal :=
  if a = ⊤ then ⊤ else (a : EReal) - (b : EReal)

end BertsekasShreve.BorelInfinite


