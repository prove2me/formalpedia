-- Prove2me | Definitions.Def_Rudin_ch01_order
-- name    : Rudin_ch01_order
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T18:01:52.838935+00:00
-- url     : https://prove2.me/theorems/b7a38513-8e68-4045-afac-d5275271ca48
-- title:
--   Rudin's least-upper-bound property of an ordered set
-- statement:
--   An ordered set $S$ has the **least-upper-bound property** when every nonempty subset of $S$ that is bounded above has a least upper bound in $S$ (Rudin, Definition 1.10); dually, it has the greatest-lower-bound property when every nonempty subset bounded below has a greatest lower bound. Mathlib's `IsLUB`, `IsGLB`, `BddAbove` and `BddBelow` already express Rudin's Definitions 1.7–1.9 and are reused unchanged. What Mathlib lacks is the *property* as a proposition: its `ConditionallyCompleteLinearOrder` is a structure carrying chosen `sSup`/`sInf` operations. These two predicates state the property itself, so that a theorem may assume it of an arbitrary ordered set, exactly as Rudin does.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, pp. 3-5, Definitions 1.7, 1.8, 1.10

import Mathlib

/-!
# Rudin, Chapter 1 — order-theoretic vocabulary

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*,
3rd edition, Chapter 1 (Definitions 1.7, 1.8, 1.10).

Mathlib already provides `upperBounds`, `lowerBounds`, `BddAbove`, `BddBelow`,
`IsLUB` and `IsGLB`, which are mathematically the same notions Rudin introduces in
1.7–1.9, so they are reused verbatim.  The only notion missing from Mathlib as a
standalone predicate is Rudin's *least-upper-bound property* of an ordered set
(Definition 1.10); Mathlib packages it as the class
`ConditionallyCompleteLinearOrder`, whose data also fixes the choice functions
`sSup`/`sInf`.  The predicate below is the property itself, stated exactly as in
Rudin, so that theorems may assume it of an arbitrary ordered set.
-/

namespace Rudin

/-- Rudin, Definition 1.10: an ordered set `S` has the **least-upper-bound property**
if every nonempty subset of `S` that is bounded above has a least upper bound in `S`. -/
def HasLeastUpperBoundProperty (S : Type*) [Preorder S] : Prop :=
  ∀ E : Set S, E.Nonempty → BddAbove E → ∃ x : S, IsLUB E x

/-- The dual of `Rudin.HasLeastUpperBoundProperty`: every nonempty subset that is
bounded below has a greatest lower bound.  (Rudin, Theorem 1.11.) -/
def HasGreatestLowerBoundProperty (S : Type*) [Preorder S] : Prop :=
  ∀ E : Set S, E.Nonempty → BddBelow E → ∃ x : S, IsGLB E x

end Rudin


