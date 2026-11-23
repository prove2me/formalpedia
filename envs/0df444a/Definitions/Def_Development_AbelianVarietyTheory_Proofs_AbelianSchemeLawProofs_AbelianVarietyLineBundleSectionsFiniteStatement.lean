-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFiniteStatement
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFiniteStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:23.598795+00:00
-- url     : https://prove2.me/theorems/9819ae5b-a08d-49b3-a8d7-12150d7d3a3d
-- title:
--   Abelian Variety Line Bundle Sections Finite Statement
-- statement:
--   Definitions and structural lemmas for Abelian Variety Line Bundle Sections Finite Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AbelianVarietyLineBundleSectionsFiniteStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw


