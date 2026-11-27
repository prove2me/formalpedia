-- Prove2me | Definitions.Def_TreeStack_Stacking
-- name    : TreeStack_Stacking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:17:17.936924+00:00
-- url     : https://prove2.me/theorems/56bbb612-f96b-4fac-be1f-84e1ae38758d
-- title:
--   Stacking
-- statement:
--   Definitions and structural lemmas for Stacking, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean

import Mathlib
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
def StackingCandidate (T : FiniteTree V) (t : ℕ) : Prop :=
  2 ≤ t ∧ UniversalStackable T.graph t
noncomputable def stack (T : FiniteTree V) : ℕ :=
  sInf {t : ℕ | StackingCandidate T t}
end TreeStack


