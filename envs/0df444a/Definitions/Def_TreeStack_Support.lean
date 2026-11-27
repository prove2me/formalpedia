-- Prove2me | Definitions.Def_TreeStack_Support
-- name    : TreeStack_Support
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:47:23.627485+00:00
-- url     : https://prove2.me/theorems/95626454-88a2-46d2-b6c6-2bcaf99950f7
-- title:
--   Support
-- statement:
--   Definitions and structural lemmas for Support, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean

import Mathlib
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
def SupportEdge (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C ∧ B.reverseBranch.Occupied C
inductive SupportDescent (C : Configuration V) :
    (B : OrientedBranch T) → V → Prop
  | root (B : OrientedBranch T) :
      SupportDescent C B B.root
  | child (B : OrientedBranch T) (c : B.Child) {x : V}
      (hEdge : (B.childBranch c).SupportEdge C)
      (hTail : SupportDescent C (B.childBranch c) x) :
      SupportDescent C B x
def DefectArrow (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.SupportEdge C ∧
    0 ≤ messageContribution (branchMessage C B)
def DefectiveSupportEdge (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.SupportEdge C ∧
    ((0 ≤ messageContribution (branchMessage C B) ∧
        0 < scoreDefect T C B.parent) ∨
      (0 ≤ messageContribution (branchMessage C B.reverseBranch) ∧
        0 < scoreDefect T C B.root) ∨
      ((messageContribution (branchMessage C B) < 0 ∧
          messageContribution (branchMessage C B.reverseBranch) < 0) ∧
        (0 < scoreDefect T C B.root ∨
          0 < scoreDefect T C B.parent)))
end OrientedBranch
end TreeStack


