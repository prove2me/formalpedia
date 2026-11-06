-- Prove2me | Definitions.Def_TC433_Data_List_Involutive_f828ca7f4f
-- name    : TC433_Data_List_Involutive_f828ca7f4f
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:28:47.182629+00:00
-- url     : https://prove2.me/theorems/e00df433-1784-402a-ab3a-27ba8423f096
-- title:
--   TauCeti: Data / List / Involutive
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Data.List.Involutive for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Data/List/Involutive.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lists of involutions

This file provides an elementary invariance result for predicates transported along lists of
involutions.

## Main results

* `TauCeti.predicate_foldl_iff_of_involutive`: a predicate preserved by involutive steps is
  invariant along a list of steps.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- A predicate preserved by a family of involutions is invariant under every list of those
involutions. -/
theorem predicate_foldl_iff_of_involutive {I J : Type*} (p : I → Prop)
    (reflect : J → I → I) (hinvolutive : ∀ j, Function.Involutive (reflect j))
    (hreflect : ∀ a j, p a → p (reflect j a)) (l : List J) (a : I) :
    p (l.foldl (fun b j ↦ reflect j b) a) ↔ p a := by
  constructor
  · intro h
    induction l generalizing a with
    | nil => exact h
    | cons j l ih =>
        have hnext := ih (reflect j a) h
        simpa only [hinvolutive j a] using hreflect (reflect j a) j hnext
  · intro h
    induction l generalizing a with
    | nil => exact h
    | cons j l ih => exact ih _ (hreflect a j h)

end TauCeti


