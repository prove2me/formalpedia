-- Prove2me | Definitions.Def_Esgk_FiniteBoundaryCurveComponents
-- name    : Esgk_FiniteBoundaryCurveComponents
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:49.276262+00:00
-- url     : https://prove2.me/theorems/2269ee9d-5bca-4634-a243-0b724a14fe1e
-- title:
--   A selected connected component on one side of a boundary
-- statement:
--   This chooses the connected component of an open set containing a chosen point of its intersection with another set, returning the empty set when that intersection is empty.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk

variable {M : Type*} [TopologicalSpace M] [T1Space M]


omit [T1Space M] in
 
def bundle_Esgk_FiniteBoundaryCurveComponents_chosenSideComponent (U A : Set M) : Set M :=
  if h : (A ∩ U).Nonempty then connectedComponentIn U h.choose else ∅


end Esgk


