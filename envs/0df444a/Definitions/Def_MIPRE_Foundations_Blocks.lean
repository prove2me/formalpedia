-- Prove2me | Definitions.Def_MIPRE_Foundations_Blocks
-- name    : MIPRE_Foundations_Blocks
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:45.459611+00:00
-- url     : https://prove2.me/theorems/b69ecff7-05a4-44e6-9983-d382e4df20c0
-- title:
--   Definitions of Blocks: Summing over assignments to a block-decomposed index type A construction that reads only some coordinates of a…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Blocks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Summing over assignments to a block-decomposed index type. A construction that reads only some coordinates of a uniformly random point needs to know that those coordinates are themselves uniform, and independent of the rest. In the form a sum identity takes, that is: when the index type is a sum, summing a function of the blocks' assignments over all assignments to the whole gives the iterated sum over the blocks --- once per assignment of whatever block the function ignores. * `sum_arrow_pair` --- both blocks, which is the product measure written as an iterated sum; * `sum_arrow_inl` --- the…
--
--   **Definitions** (1): `MIPRE.sumArrow` (An assignment to a sum index type is a pair of assignments to the summands.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Blocks` (`MIPRE/Foundations/Blocks.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Blocks.lean; blueprint lem:qld-sublines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Blocks.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Summing over assignments to a block-decomposed index type

A construction that reads only some coordinates of a uniformly random point needs to know that
those coordinates are themselves uniform, and independent of the rest. In the form a sum identity
takes, that is: when the index type is a sum, summing a function of the blocks' assignments over all
assignments to the whole gives the iterated sum over the blocks --- once per assignment of whatever
block the function ignores.

* `sum_arrow_pair` --- both blocks, which is the product measure written as an iterated sum;
* `sum_arrow_inl` --- the left block alone, at the cost of one factor of the right block's count.

Nothing here is about fields, lines or games. The only reason the file exists is that the padded
space of the combining stage (`MIPRE/Background/QLD/Padded.lean`) is `F_q^{4m}` with its coordinates
split into blocks, and every distributional statement about that splitting reduces to these two.
-/

noncomputable section

namespace MIPRE

open Finset

variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]

/-- An assignment to a sum index type is a pair of assignments to the summands. Spelled out rather
than taken from `Equiv.sumArrowEquivProdArrow` so that both directions compute by `rfl`. -/
def sumArrow (α β F : Type*) : (α ⊕ β → F) ≃ (α → F) × (β → F) where
  toFun u := (fun a => u (.inl a), fun b => u (.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv u := by funext j; cases j <;> rfl
  right_inv _ := rfl

/-! ## Rewriting, reordering and scaling nested sums

A block decomposition turns one sum into two, and the new sums appear where the old one was. Getting
from there to a statement about each block's own law is bookkeeping: rewrite a sum that sits under
others, move one sum past its neighbours, and pull a constant multiplier out. These are the three
moves, stated at the arities the padded space needs, so that a proof can name the step it is taking
instead of rebuilding a `Finset.sum_congr` tower each time.
-/

section Bookkeeping

variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]

end Bookkeeping

/-! ## Marginals of a uniform average

A uniform average of a quantity that depends on only part of the sample is the uniform average over
that part. Stated once, for an arbitrary splitting of the sample space given as an equivalence with a
product, it is what relates the Pauli basis test's single content --- which carries both sides' points
but *one* seed and *one* raw direction --- to a product of two independent line-point laws: each
side's own data has the same marginal under both.
-/

section Marginal

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]

end Marginal

end MIPRE


