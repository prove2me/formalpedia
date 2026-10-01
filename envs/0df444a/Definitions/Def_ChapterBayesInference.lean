-- Prove2me | Definitions.Def_ChapterBayesInference
-- name    : ChapterBayesInference
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:23:14.355321+00:00
-- url     : https://prove2.me/theorems/5463ff6a-ad8b-401e-80b5-ff4cd661a685
-- title:
--   Chapter BayesInference
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBayesInference.lean`): generated def bundle for ChapterBayesInference. See BookProof/ChapterBayesInference.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBayesInference.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §2 —
Unitary inference reproduces Bayesian inference

Formalization of the self-contained finite-dimensional core of the book's central
§2 compatibility claim (`book.tex` line ~1338, chapter *"Wave-function
parametrization of a probability measure"*):

> "given a Bayesian model, a prior probability and data that allows to produce a
> posterior probability through Bayesian inference, there is a reversible model
> that produces the same posterior probability as a function of the prior
> probability."

A finite **Bayesian model** is a prior distribution `prior : X → ℝ` on the
hypotheses/parameters together with a likelihood / Markov kernel
`L : X → Y → ℝ` (each row `y ↦ L x y` a probability distribution on the data
`Y`).  Observing data `y`, the **Bayes posterior** is
`posterior y x = prior x · L x y / evidence y`, where
`evidence y = ∑_x prior x · L x y` is the marginal likelihood of the data.

The book's *reversible* (unitary) model reproduces this posterior via the **Born
rule**: the joint density `p(x,y) = prior x · L x y` is `|Ψ(x,y)|²` for the
normalized wave-function `Ψ = √p`, which — by the §3 Gram–Schmidt construction
(`ChapterJointUnitary.exists_unitary_joint`) — is a column of a *unitary* matrix
`U` on `L²(X × Y)`.  Conditioning that column on the observed data (Born-rule
conditioning) returns exactly the Bayes posterior.

Deliverables (all `sorry`-free, `axiom`-free):

* `joint_nonneg`, `joint_sum_one` — the joint density `p(x,y) = prior x · L x y`
  is a genuine probability distribution on `X × Y`;
* `evidence_eq_marginal`, `evidence_nonneg` — the evidence is the `X`-marginal;
* `posterior_nonneg`, `posterior_sum_one` — for data `y` with positive evidence
  the Bayes posterior is a probability distribution on `X`;
* `posterior_eq_joint_div_evidence` — the defining Bayes chain rule
  `posterior y x · evidence y = p(x,y)`;
* **`posterior_eq_born_conditional`** — the posterior equals the Born-rule
  conditional `|Ψ(x,y)|² / ∑_{x'} |Ψ(x',y)|²` of the wave-function `Ψ = √p`;
* **`exists_unitary_reproduces_posterior`** (headline) — there is a *unitary*
  matrix `U` on `X × Y` and a column index `i₀` with `‖U (x,y) i₀‖² = p(x,y)`
  such that for every data point `y` with positive evidence, the Bayes posterior
  is reproduced by Born-rule conditioning of that column:
  `posterior y x = ‖U (x,y) i₀‖² / ∑_{x'} ‖U (x',y) i₀‖²`.
-/

open scoped BigOperators

namespace BookProof.ChapterBayesInference

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The joint probability density `p(x,y) = prior(x) · L(x,y)` of hypothesis `x`
and data `y`. -/
def joint (prior : X → ℝ) (L : X → Y → ℝ) (x : X) (y : Y) : ℝ := prior x * L x y

/-- The evidence (marginal likelihood) `∑_x prior(x) · L(x,y)` of the data `y`. -/
def evidence (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) : ℝ := ∑ x, prior x * L x y

/-- The Bayes posterior `p(x | y) = prior(x) · L(x,y) / evidence(y)`. -/
noncomputable def posterior (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) (x : X) : ℝ :=
  prior x * L x y / evidence prior L y

variable {prior : X → ℝ} {L : X → Y → ℝ}

















/-
**Headline: unitary inference reproduces Bayesian inference.** Given a finite
Bayesian model — a prior `prior` and a likelihood `L` — there is a *unitary*
matrix `U` on `L²(X × Y)` and a column index `i₀` with `‖U (x,y) i₀‖² = p(x,y)`,
such that for every data point `y` with positive evidence the Bayes posterior is
reproduced by Born-rule conditioning of that column of `U`.
-/


end BookProof.ChapterBayesInference


