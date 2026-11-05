-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_eexp
-- name    : BauerleRiederMDP_TransactionCosts_eexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:20.316877+00:00
-- url     : https://prove2.me/theorems/cbe05362-60ec-4530-b9de-bf1a77e2034d
-- title:
--   Expectation of an extended-real random variable
-- statement:
--   For a random variable $f$ with values in $[-\infty,\infty]$,
--   $$\mathbb E f:=\mathbb E f^+-\mathbb E f^-,$$
--   with both terms in $[0,\infty]$. The expectation exists when at least one of the two is finite; it then lies in $[-\infty,\infty]$. This is the expectation used for $[-\infty,\infty)$-valued functions throughout the book (e.g. in $L_nv$, Definition 2.3.1: "whenever the integral exists").
--
--   **Formalization Note** The two parts are lower Lebesgue integrals and the difference is taken in `EReal`. When both are infinite the book's expectation does not exist and the `EReal` value $\bot$ has no meaning; statements that need existence assert it.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.1, p.19 (PDF 34)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.TransactionCosts

/-- The expectation `IE f = IE f⁺ − IE f⁻ ∈ [−∞, ∞]` of an extended-real random variable `f`
(the expectation of a `[−∞, ∞)`-valued function used throughout Bäuerle & Rieder 2011, e.g. in
the operator `L_n v` of Definition 2.3.1, p.19, PDF 34: "whenever the integral exists").

**Formalization Note.** `f⁺` and `f⁻` are integrated as lower Lebesgue integrals in `[0, ∞]`
and the difference is taken in `EReal`. The integral exists in the book's sense iff at least one
of the two is finite; in the remaining case (`IE f⁺ = IE f⁻ = ∞`) the `EReal` difference is `⊥`,
a value without meaning. Statements that need the expectation to exist say so. -/
noncomputable def eexp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → EReal) :
    EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂P : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂P : ENNReal) : EReal)

end BauerleRiederMDP.TransactionCosts


