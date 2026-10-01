-- Prove2me | Definitions.Def_ChapterTotalVariance
-- name    : ChapterTotalVariance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:01:34.329696+00:00
-- url     : https://prove2.me/theorems/5e7590b2-eca3-40fb-b500-58f992bb50a9
-- title:
--   Chapter TotalVariance
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTotalVariance.lean`): generated def bundle for ChapterTotalVariance. See BookProof/ChapterTotalVariance.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTotalVariance.lean

import Mathlib


/-!
# Chapter "Aligned deep learning as a random sampling method", §2
"Systematic uncertainties and Bayesian priors" — **the law of total variance
(within-group / between-group variance decomposition)**

Source: `book.tex`.  The book repeatedly frames *systematic uncertainties* as
Bayesian priors and discusses the decomposition of the uncertainty of a
prediction into a part that is intrinsic to the data ("aleatoric") and a part
that reflects our ignorance of which model / group generated it ("epistemic"):

> *"The systematic uncertainties in Engineering can be defined as Bayesian prior
> probability distributions … which describe previous knowledge about a system."*
> (`book.tex` §2, line ~9793)

and it stresses that ensemble forecasting — a *probability space of probability
spaces* — combines the variability *within* each member with the variability
*between* members (`book.tex` §10, line ~2005; `hullermeier_aleatoric_2021`).

The precise, self-contained mathematical fact underpinning that picture is the
classical **law of total variance**: if the outcomes are partitioned into groups
`X ω` (the "member" / conditioning variable), then the total variance of a
quantity `Y` splits *exactly* into

* the **within-group** ("aleatoric") variance — the mean of the conditional
  variances, and
* the **between-group** ("epistemic") variance — the variance of the conditional
  means.

This module formalizes that identity for a finite sample space, entirely
independently of the surrounding discussion.  For a finite sample space `Ω` with
nonnegative weights `w` (a probability distribution — although the algebraic
identity needs only nonnegativity), a real quantity `Y : Ω → ℝ`, and a grouping
`X : Ω → κ` into finitely many groups:

* `mean`, `groupProb`, `condMean` — the expectation `E[Y]`, the group
  probabilities `P(X = g)`, and the conditional means `E[Y | X = g]`
  (with the convention `0/0 = 0` on zero-probability groups);
* `variance`, `within`, `between` — the total variance `Var[Y]`, the mean of the
  conditional variances `E[Var(Y | X)]`, and the variance of the conditional
  means `Var(E[Y | X])`;
* `groupBalance` — for every group the `w`-weighted residuals `Y − E[Y|X]` sum to
  zero (the defining orthogonality of conditional expectation);
* `crossTerm_zero` — hence the cross term in the Pythagorean expansion vanishes;
* HEADLINE `total_variance` — `Var[Y] = E[Var(Y | X)] + Var(E[Y | X])`, i.e.
  `variance = within + between`;
* `within_nonneg`, `between_nonneg`, `variance_nonneg`, and the consequences
  `within_le_variance`, `between_le_variance`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace ChapterTotalVariance

open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

/-- The expectation `E[Y] = ∑_ω w(ω)·Y(ω)`. -/
def mean (w Y : Ω → ℝ) : ℝ := ∑ ω, w ω * Y ω

/-- The group probability `P(X = g) = ∑_{ω : X ω = g} w(ω)`. -/
def groupProb (w : Ω → ℝ) (X : Ω → κ) (g : κ) : ℝ :=
  ∑ ω, if X ω = g then w ω else 0

/-- The conditional mean `E[Y | X = g]`, with the convention `0/0 = 0` on a
zero-probability group. -/
noncomputable def condMean (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (g : κ) : ℝ :=
  (∑ ω, if X ω = g then w ω * Y ω else 0) / groupProb w X g

/-- The total variance `Var[Y] = ∑_ω w(ω)·(Y(ω) − E[Y])²`. -/
def variance (w Y : Ω → ℝ) : ℝ := ∑ ω, w ω * (Y ω - mean w Y) ^ 2

/-- The within-group (aleatoric) variance `E[Var(Y | X)]`, written in the form
`∑_ω w(ω)·(Y(ω) − E[Y | X = X ω])²` in which the group-probability denominators
cancel. -/
noncomputable def within (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, w ω * (Y ω - condMean w X Y (X ω)) ^ 2

/-- The between-group (epistemic) variance `Var(E[Y | X])`, written as
`∑_ω w(ω)·(E[Y | X = X ω] − E[Y])²`. -/
noncomputable def between (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, w ω * (condMean w X Y (X ω) - mean w Y) ^ 2

















end ChapterTotalVariance


