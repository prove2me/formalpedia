-- Prove2me | Definitions.Def_TreeStack_UpperBound
-- name    : TreeStack_UpperBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:15:33.825821+00:00
-- url     : https://prove2.me/theorems/0a2dc70e-94bf-5f43-b910-4f87d6ba0dee
-- title:
--   Upper Bound
-- statement:
--   Definitions and structural lemmas for Upper Bound, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean

import Mathlib
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
end OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
end TreeStack


