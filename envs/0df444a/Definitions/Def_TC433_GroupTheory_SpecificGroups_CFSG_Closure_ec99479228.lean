-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Closure_ec99479228
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_Closure_ec99479228
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:40:34.825859+00:00
-- url     : https://prove2.me/theorems/3f01ea36-90ab-4edc-88d5-ab4640a38cf6
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / Closure
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.Closure for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/Closure.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Index_08374d0e8b
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Algebraic closures for finite groups of Lie type

This file attaches to every valid Lie-type index the algebraically closed field over which its
ambient pinned algebraic group will be evaluated. The field is Mathlib's algebraic closure of the
prime field in the characteristic recorded by the index. Consequently its field, algebraic-closure,
and characteristic structures are the canonical Mathlib instances rather than parallel data.

## Main definition

* `TauCeti.ValidLieTypeIndex.Closure`: the algebraic closure of the index's prime field.

## Roadmap

This is the algebraic-closure part of item I0 in
`TauCetiRoadmap/CFSGStatement/README.md`. Milestone L0 uses this carrier when it base-changes the
pinned Chevalley--Demazure group scheme to the characteristic of a valid Lie-type index and takes
its algebraic-closure-valued points.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.ValidLieTypeIndex

/-- The algebraic closure of the prime field in the characteristic attached to a valid Lie-type
index. -/
abbrev Closure (d : ValidLieTypeIndex) : Type :=
  AlgebraicClosure (ZMod d.characteristic)

/-! The instances used by the later ambient-group construction are inherited from Mathlib. -/

noncomputable section

example (d : ValidLieTypeIndex) : Field d.Closure := inferInstance

example (d : ValidLieTypeIndex) : IsAlgClosed d.Closure := inferInstance

example (d : ValidLieTypeIndex) : CharP d.Closure d.characteristic := inferInstance

end

end TauCeti.ValidLieTypeIndex

namespace TauCeti.SuzukiLieIndex

/-- The algebraic closure attached to a Suzuki index has characteristic two. -/
instance charP_closure_two (d : SuzukiLieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

end TauCeti.SuzukiLieIndex


