-- Prove2me | Definitions.Def_TreeStack_Message
-- name    : TreeStack_Message
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:17:28.152261+00:00
-- url     : https://prove2.me/theorems/d48e380b-4d52-5f0e-8074-e964657c5466
-- title:
--   Message
-- statement:
--   Definitions and structural lemmas for Message, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt

set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
def Occupied (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∃ v ∈ B.vertices, 0 < C v
noncomputable instance (C : Configuration V) (B : OrientedBranch T) :
    Decidable (B.Occupied C) := Classical.dec _
def messageContribution : Message → ℤ
  | none => 0
  | some d => d
noncomputable def branchMessage (C : Configuration V) (B : OrientedBranch T) :
    Message :=
  if hB : B.Occupied C then
    some <| F <|
      (C B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            messageContribution
              (branchMessage C
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }))
          else
            0
  else
    EMPTY
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }
noncomputable def childMessageSum (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      messageContribution
        (branchMessage C
          (B.childBranch
            { vertex := v
              adj := h.1
              ne_parent := h.2 }))
    else
      0
noncomputable def effectiveInput (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  (C B.root : ℤ) + childMessageSum C B
end OrientedBranch
end TreeStack


