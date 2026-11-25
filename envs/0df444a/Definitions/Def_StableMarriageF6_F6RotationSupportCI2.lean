-- Prove2me | Definitions.Def_StableMarriageF6_F6RotationSupportCI2
-- name    : StableMarriageF6_F6RotationSupportCI2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:31:13.029525+00:00
-- url     : https://prove2.me/theorems/ccccb766-36f6-44f4-a49a-a1fa6e66e94f
-- title:
--   F6 Rotation Support CI2
-- statement:
--   Definitions and structural lemmas for F6 Rotation Support CI2, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/F6RotationSupportCI2.lean

import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
namespace F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
def supportUnion (supp : R → Finset M) (Q : Finset R) : Finset M :=
  Q.biUnion supp
def OrderConvex (Q : Finset R) : Prop :=
  ∀ x ∈ Q, ∀ z ∈ Q, ∀ y, x ≤ y → y ≤ z → y ∈ Q
def interval (alpha beta : R) : Finset R :=
  univ.filter (fun rho => alpha ≤ rho ∧ rho ≤ beta)
def commonInc (alpha beta : R) : Finset R :=
  F6ConvexWindow.Inc alpha ∩ F6ConvexWindow.Inc beta
end F6RotationSupport


