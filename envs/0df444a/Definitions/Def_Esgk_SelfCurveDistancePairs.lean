-- Prove2me | Definitions.Def_Esgk_SelfCurveDistancePairs
-- name    : Esgk_SelfCurveDistancePairs
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:11.177988+00:00
-- url     : https://prove2.me/theorems/ebeec821-dfdb-4f29-8a5a-4ab2787e66b9
-- title:
--   Deleting ordered pairs involving exceptional points
-- statement:
--   For finite sets of sample and exceptional points, this defines the union of ordered pairs with one coordinate in each set. A second definition adds an arbitrary further set of ordered pairs to be deleted.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk


def exceptionalOrderedPairs {α : Type*} [DecidableEq α]
    (S E : Finset α) : Finset (α × α) :=
  (E ×ˢ S) ∪ (S ×ˢ E)


def deletedIndexedPairs {α : Type*} [DecidableEq α]
    (S E : Finset α) (Γ : Finset (α × α)) : Finset (α × α) :=
  exceptionalOrderedPairs S E ∪ Γ


end Esgk


