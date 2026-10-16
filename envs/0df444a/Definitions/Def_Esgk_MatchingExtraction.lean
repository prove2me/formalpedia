-- Prove2me | Definitions.Def_Esgk_MatchingExtraction
-- name    : Esgk_MatchingExtraction
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:22.990998+00:00
-- url     : https://prove2.me/theorems/33b96383-22c8-49b4-8e41-f35301ee971f
-- title:
--   Conflicts between ordered pairs
-- statement:
--   This defines when two ordered pairs conflict by sharing an endpoint and provides the corresponding decidable relation.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceDesign
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

 
def OrderedPairConflict {V : Type*} (edge other : V × V) : Prop :=
  edge.1 = other.1 ∨ edge.1 = other.2 ∨
    edge.2 = other.1 ∨ edge.2 = other.2

instance instDecidableOrderedPairConflict {V : Type*} [DecidableEq V] :
    DecidableRel (@OrderedPairConflict V) := by
  intro edge other
  unfold OrderedPairConflict
  infer_instance


end Esgk


