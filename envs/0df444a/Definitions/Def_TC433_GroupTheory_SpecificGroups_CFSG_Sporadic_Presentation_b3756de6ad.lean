-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Presentation_b3756de6ad
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Presentation_b3756de6ad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:41:29.397734+00:00
-- url     : https://prove2.me/theorems/ce7e98d1-9d43-46dc-8e6b-96f2625702a4
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / Sporadic / Presentation
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Presentation.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Index_08374d0e8b
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_BabyMonster_5540a8875e
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Conway_One_0dca22062d
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Conway_Three_390cf7e683
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Conway_Two_4062b3057a
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Fischer_TwentyFour_5d9ccd0560
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Fischer_TwentyThree_eb2ecbbd88
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Fischer_TwentyTwo_0a10ab2f44
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_HaradaNorton_64bdf799b0
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Held_74c689a2a0
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_HigmanSims_589c81a1c5
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Janko_Four_8c973b6f6a
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Janko_One_a7c398e3a6
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Janko_Three_1346d01978
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Janko_Two_4ffa107ca3
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Lyons_466c8573f9
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Mathieu_eb4b56e833
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Mathieu_TwentyFour_2d353d08aa
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Mathieu_TwentyThree_1a9deaff5a
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_McLaughlin_673e2bc5fa
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Monster_0ecae297c2
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_ONan_df6904c771
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Rudvalis_2897abd4cb
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Suzuki_c5638600d4
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Sporadic_Thompson_b435ecb4e6

/-!
# Presentations of the sporadic groups

This file assembles the twenty-six independently transcribed sporadic-group presentations into the
total function `TauCeti.SporadicName.presentation`. Each branch is the explicit, cited
`TauCeti.GroupPresentation` defined in its group-specific module. The theorem
`TauCeti.presentation_matchesMetadata` combines the individual generator- and
relator-count checks, while `TauCeti.SporadicName.Group` is the concrete group defined by the
selected presentation.

This is milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md`. The dispatcher and its interface
follow the target signatures in the human-authored roadmap's `CFSGStatement/Suggested.lean`; the
mathematical and bibliographic sources for each presentation are recorded in the corresponding
imported module.

## Main definitions

* `TauCeti.SporadicName.presentation`: the complete presentation attached to a sporadic name.
* `TauCeti.SporadicName.Group`: the group defined by that presentation.

## Main results

* `TauCeti.presentation_matchesMetadata`: every selected presentation has the stated
  number of generators and relators.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- The explicit, cited finite presentation attached to each sporadic-group name. -/
@[simp]
def SporadicName.presentation : SporadicName → GroupPresentation
  | .M11 => Sporadic.m11Presentation
  | .M12 => Sporadic.m12Presentation
  | .M22 => Sporadic.m22Presentation
  | .M23 => Sporadic.m23Presentation
  | .M24 => Sporadic.m24Presentation
  | .J1 => Sporadic.j1Presentation
  | .J2 => Sporadic.j2Presentation
  | .J3 => Sporadic.j3Presentation
  | .J4 => Sporadic.j4Presentation
  | .HS => Sporadic.hsPresentation
  | .McL => Sporadic.mclPresentation
  | .He => Sporadic.hePresentation
  | .Ru => Sporadic.ruPresentation
  | .Suz => Sporadic.suzPresentation
  | .ONan => Sporadic.onanPresentation
  | .Co1 => Sporadic.co1Presentation
  | .Co2 => Sporadic.co2Presentation
  | .Co3 => Sporadic.co3Presentation
  | .Fi22 => Sporadic.fi22Presentation
  | .Fi23 => Sporadic.fi23Presentation
  | .Fi24Prime => Sporadic.fi24PrimePresentation
  | .HN => Sporadic.hnPresentation
  | .Ly => Sporadic.Lyons.presentation
  | .Th => Sporadic.Thompson.presentation
  | .B => Sporadic.BabyMonster.presentation
  | .M => Sporadic.Monster.presentation

/-- Every sporadic presentation has the generator and relator counts stated in its metadata.

This is deliberately not `@[simp]`: `GroupPresentation.matchesMetadata_iff` is itself a `simp`
lemma, so the left-hand side `s.presentation.matchesMetadata` simplifies to the pair of count
equations and is not in simp normal form, which the `simpNF` linter rejects. Apply the theorem
directly, or pass it to `simp` as an argument. -/
theorem presentation_matchesMetadata (s : SporadicName) :
    s.presentation.matchesMetadata := by
  cases s with
  | M11 => exact Sporadic.m11Presentation_matchesMetadata
  | M12 => exact Sporadic.m12Presentation_matchesMetadata
  | M22 => exact Sporadic.m22Presentation_matchesMetadata
  | M23 => exact Sporadic.m23Presentation_matchesMetadata
  | M24 => exact Sporadic.m24Presentation_matchesMetadata
  | J1 => exact Sporadic.j1Presentation_matchesMetadata
  | J2 => exact Sporadic.j2Presentation_matchesMetadata
  | J3 => exact Sporadic.j3Presentation_matchesMetadata
  | J4 => exact Sporadic.j4Presentation_matchesMetadata
  | HS => exact Sporadic.hsPresentation_matchesMetadata
  | McL => exact Sporadic.mclPresentation_matchesMetadata
  | He => exact Sporadic.hePresentation_matchesMetadata
  | Ru => exact Sporadic.ruPresentation_matchesMetadata
  | Suz => exact Sporadic.suzPresentation_matchesMetadata
  | ONan => exact Sporadic.onanPresentation_matchesMetadata
  | Co1 => exact Sporadic.co1Presentation_matchesMetadata
  | Co2 => exact Sporadic.co2Presentation_matchesMetadata
  | Co3 => exact Sporadic.co3Presentation_matchesMetadata
  | Fi22 => exact Sporadic.fi22Presentation_matchesMetadata
  | Fi23 => exact Sporadic.fi23Presentation_matchesMetadata
  | Fi24Prime => exact Sporadic.fi24PrimePresentation_matchesMetadata
  | HN => exact Sporadic.hnPresentation_matchesMetadata
  | Ly => exact Sporadic.Lyons.matchesMetadata_presentation
  | Th => exact Sporadic.Thompson.matchesMetadata_presentation
  | B => exact Sporadic.BabyMonster.matchesMetadata_presentation
  | M => exact Sporadic.Monster.presentation_matchesMetadata

/-- The sporadic group concretely defined by its selected finite presentation. -/
abbrev SporadicName.Group (s : SporadicName) : Type := s.presentation.Group

end TauCeti


