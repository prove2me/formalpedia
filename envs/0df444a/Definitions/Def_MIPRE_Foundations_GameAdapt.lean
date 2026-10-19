-- Prove2me | Definitions.Def_MIPRE_Foundations_GameAdapt
-- name    : MIPRE_Foundations_GameAdapt
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:37.697757+00:00
-- url     : https://prove2.me/theorems/966d2c98-b8fb-4a24-8c35-1e142bd65a36
-- title:
--   Definitions of GameAdapt: Playing a strategy for one game as a strategy for another `MIPRE.Foundations.GameTransport` compares games that share…
-- statement:
--   The definitions of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   **Definitions** (5): `MIPRE.ProjectiveMeasurement.mergeAt` (Merge the outcomes of `P` along a coarse-graining that may depend on the question, while reindexing the questions.); `MIPRE.TensorProductStrategy.adapt` (**Play `S` on `G'`**, through a map `qA`, `qB` of `G'`'s questions into `G`'s and a coarse-graining `rA`, `rB` of `G`'s answers into `G'`'s…); `MIPRE.TensorProductStrategy.born` (The Born-rule probability that `S` answers `(a, b)` to the question pair `(x, y)`.); `MIPRE.TensorProductStrategy.failAt` (The probability that `S` is rejected, given the question pair `(x, y)`.); `MIPRE.TensorProductStrategy.succAt` (The probability that `S` is accepted, given the question pair `(x, y)`.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mergeAt_M`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.GameAdapt` (`MIPRE/Foundations/GameAdapt.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-!
# Playing a strategy for one game as a strategy for another

`MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their
distribution. This file drops both assumptions, which is what a *reduction* between two
genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's
questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt`
plays `S` through them.

## The conditional success probability

Everything is organized around `succAt S x y`, the probability that `S` is accepted *given* the
question pair `(x, y)`, and its complement `failAt`. The value is the `μ`-average of `succAt`
(`value_eq_sum_succAt`), so

`1 - S.value = ∑ x y, μ x y * failAt S x y`  (`one_sub_value_eq_sum_failAt`),

which is the form a reduction compares across two games: an inequality between failure
probabilities, each weighted by its own game's distribution.

## What the adapter costs

`failAt_adapt_le` says the adapted strategy fails no more often at `(x', y')` than `S` does at
`(qA x', qB y')`, provided every tuple `G` accepts is still accepted after coarse-graining
(`hD`). The summed statements ask `hD` only where `G'.μ` is nonzero, and that is not a
convenience: a question pair outside the target's support may well be one the target *rejects*
and the source accepts --- for the seeded CL test, a pair of two line questions, which the
canonical-line test has no subtest for --- so the unrestricted hypothesis would be false. Summing, the price is entirely in the distributions: `one_sub_value_adapt_le` asks that
the push-forward of `G'`'s distribution along `(qA, qB)` be dominated by `C` times `G`'s, and
concludes `1 - (S.adapt …).value ≤ C * (1 - S.value)`.

## Derandomization

A reduction usually cannot choose the question map canonically: the target's question is
typically a *coarser* object than `G`'s — a line rather than a seeded description of a line —
so one has to pick a preimage, and for any fixed choice the push-forward bound is off by the
size of the fibre. `exists_one_sub_value_adapt_le` is the averaged form. It asks only that the
push-forward bound hold on average over a finite family of question maps, and returns one
member of the family achieving the conclusion. That is the "choose the best seed" step, and the
averaging is exactly where the fibre size is paid back.
-/

namespace MIPRE

open Matrix Kronecker Finset

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

/-! ## Question-dependent merging of outcomes -/

namespace ProjectiveMeasurement

/-- Merge the outcomes of `P` along a coarse-graining that may depend on the question, while
reindexing the questions. `GameTransport`'s `merge` is the case of a coarse-graining that does
not depend on the question; a reduction generally needs the dependence, because how an answer
must be converted can depend on which question was asked --- the reparametrization of a line
answer depends on the line. -/
def mergeAt {X X' A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A'] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (qX : X' → X)
    (r : X' → A → A') : ProjectiveMeasurement X' A' (Matrix n n ℂ) where
  M x' a' := ∑ a ∈ Finset.univ.filter (fun a => r x' a = a'), P.M (qX x') a
  selfAdjoint x' a' := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => P.selfAdjoint _ a
  projective x' a' := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => P.mul_eq_zero_of_ne _ (Ne.symm hb))
      (fun h => absurd ha h)]
    exact P.projective _ a
  normalized x' := by
    rw [Finset.sum_fiberwise]
    exact P.normalized _

@[simp] theorem mergeAt_M {X X' A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A']
    {n : Type*} [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ))
    (qX : X' → X) (r : X' → A → A') (x' : X') (a' : A') :
    (P.mergeAt qX r).M x' a'
      = ∑ a ∈ Finset.univ.filter (fun a => r x' a = a'), P.M (qX x') a := rfl

end ProjectiveMeasurement

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-! ## Born-rule probabilities and the conditional success probability -/

/-- The Born-rule probability that `S` answers `(a, b)` to the question pair `(x, y)`. -/
noncomputable def born (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- The probability that `S` is accepted, given the question pair `(x, y)`. -/
noncomputable def succAt (S : TensorProductStrategy G) (x : X) (y : Y) : ℝ :=
  ∑ a, ∑ b, (if G.D x y a b then 1 else 0) * S.born x y a b

/-- The probability that `S` is rejected, given the question pair `(x, y)`. -/
noncomputable def failAt (S : TensorProductStrategy G) (x : X) (y : Y) : ℝ :=
  1 - S.succAt x y

/-! ## The adapted strategy -/

section Adapt

variable [DecidableEq A'] [DecidableEq B']

/-- **Play `S` on `G'`**, through a map `qA`, `qB` of `G'`'s questions into `G`'s and a
coarse-graining `rA`, `rB` of `G`'s answers into `G'`'s that may depend on the question: the
measurement at a question `x'` of `G'` is the one `S` uses at `qA x'`, with its outcomes merged
along `rA x'`. -/
noncomputable def adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') :
    TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.mergeAt qA rA, S.PB.mergeAt qB rB⟩

/-! ## The cost of the adapter is the push-forward of the distribution -/

variable [DecidableEq X] [DecidableEq Y]

/-! ## Derandomization -/

end Adapt

end TensorProductStrategy

end MIPRE


