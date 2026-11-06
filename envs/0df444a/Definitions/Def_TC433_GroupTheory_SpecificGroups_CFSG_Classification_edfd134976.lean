-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Classification_edfd134976
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_Classification_edfd134976
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:08:35.456608+00:00
-- url     : https://prove2.me/theorems/a533c44e-4ebe-4b4b-8479-79146dac1b62
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / Classification
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.Classification for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/Classification.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Definitions.Def_TC433_GroupTheory_SimpleGroupUniverse_75905d753d
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Assembly_LieType_b8402d9d1b
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Presentation_b3756de6ad
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The statement of the classification of finite simple groups

This file assembles the explicit cyclic, alternating, Lie-type, and sporadic carriers indexed by
`TauCeti.CFSGIndex`. It then records the classification as a named proposition. No finiteness or
simplicity property of a listed carrier is asserted here, and the classification proposition is
not proved. The Lie-type branches use explicit carriers; their identification with the pinned
simply connected group schemes remains separate. The sporadic branches use the recorded
finite presentations, without assuming any recognition theorem for the presented groups.

## Main definitions

* `TauCeti.CFSGIndex.Group`: the concrete carrier selected by an index on the classification list.
* `TauCeti.ClassificationStatement`: every finite simple group is isomorphic to a listed carrier,
  with `TauCeti.classificationStatement_iff` stating the quantified proposition it names.

## Main results

* `TauCeti.classificationStatement_of_zero`: the universe-zero statement implies the statement in
  every universe.

-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- The concrete carrier type represented by an index on the classification list. -/
abbrev CFSGIndex.Group : CFSGIndex → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating degree _ => alternatingGroup (Fin degree)
  | .lie index => index.Group
  | .sporadic name => name.Group

noncomputable instance (i : CFSGIndex) : Group i.Group := by
  cases i <;> infer_instance

universe u

/-- **Classification of finite simple groups, statement only.** Every finite simple group is
isomorphic to one of the explicitly constructed groups on the classification list. -/
def ClassificationStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group)

/-- The classification statement holds exactly when every finite simple group is isomorphic to
one of the indexed carriers. -/
theorem classificationStatement_iff :
    ClassificationStatement.{u} ↔
      ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
        ∃ i : CFSGIndex, Nonempty (G ≃* i.Group) :=
  Iff.rfl

/-- The universe-zero classification statement implies the statement in every universe. -/
theorem classificationStatement_of_zero (h : ClassificationStatement.{0}) :
    ClassificationStatement.{u} :=
  exists_mulEquiv_of_forall_finite_isSimpleGroup_zero CFSGIndex.Group h

end TauCeti


