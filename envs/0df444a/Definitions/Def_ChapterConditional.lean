-- Prove2me | Definitions.Def_ChapterConditional
-- name    : ChapterConditional
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:49:49.883711+00:00
-- url     : https://prove2.me/theorems/6a2eecd5-9eb0-48ea-a6dd-1fa9d7bf2f02
-- title:
--   Chapter Conditional
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterConditional.lean`): generated def bundle for ChapterConditional. See BookProof/ChapterConditional.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterConditional.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §3 — the
converse: marginal and regular conditional probability of a bounded operator

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, §3 *"Any conditional probability measure in a standard measure space
is parametrized by a unitary operator"* (`book.tex` line ~1478, the paragraph
beginning *"The converse also holds"*).

The central theorem of this chapter parametrizes any joint probability density
`p(x,y)` as `|𝒰(y,x,0)|²` for a unitary `𝒰` (the finite version is
`ChapterJointUnitary`; the Hilbert–Schmidt boundedness step is `ChapterKernelBound`;
the singular-value expansion `Ψ = W D U†` is `ChapterB3`/`ChapterB3b`).  The book
then records the **converse**:

> *"Given a bounded operator `B`, such that `tr(BB†)=1`, then it defines a joint
> probability distribution of initial and final states `p(x,y)=|B(y,x)|²`. From
> the joint probability, if `p(x)={B†B}(x,x)>0` for all `x∈X`, then we can define
> a regular conditional probability density."*

`ChapterJointUnitary.sqAbs_isProb_of_frobenius_one` already shows `p(x,y)=|B(y,x)|²`
is a genuine joint distribution.  This file supplies the *marginal / regular
conditional* layer of the converse, over finite index sets (`X`, `Y`), `RCLike`
field-agnostic:

* `pMarg_eq_diagBHB` — the book's `p(x) = {B†B}(x,x)`: the marginal of the joint
  distribution is the diagonal of the Gram matrix `Bᴴ B`;
* `trace_gram_eq_one` — the book's normalization `tr(BᴴB) = tr(BB†) = 1` in trace
  form;
* `pMarg_sum_one` — the marginal is a probability distribution on `X`
  (`∑ₓ p(x) = 1`);
* `pJoint_sum_one` — the joint is a probability distribution on `X × Y`;
* `pCond_nonneg`, `pCond_sum_one` — for every `x` with `p(x) > 0` the conditional
  `p(y|x) = p(x,y)/p(x)` is a genuine probability distribution on `Y`
  (`∑_y p(y|x) = 1`): the *regular conditional probability density*;
* `pJoint_eq_cond_mul_marg` — the chain rule `p(x,y) = p(y|x) · p(x)`, so the
  joint is reconstructed from the marginal and the conditional.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators Matrix
open Finset

namespace BookProof.ChapterConditional

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The joint probability density `p(x,y) = |B(y,x)|²` (`B` has rows indexed by
the "final" state `y` and columns by the "initial" state `x`). -/
noncomputable def pJoint (B : Matrix Y X 𝕜) (x : X) (y : Y) : ℝ := ‖B y x‖ ^ 2

/-- The marginal probability density `p(x) = ∑_y |B(y,x)|²`. -/
noncomputable def pMarg (B : Matrix Y X 𝕜) (x : X) : ℝ := ∑ y, ‖B y x‖ ^ 2

/-- The (regular) conditional probability density `p(y|x) = p(x,y) / p(x)`. -/
noncomputable def pCond (B : Matrix Y X 𝕜) (x : X) (y : Y) : ℝ :=
    pJoint B x y / pMarg B x





















end BookProof.ChapterConditional


