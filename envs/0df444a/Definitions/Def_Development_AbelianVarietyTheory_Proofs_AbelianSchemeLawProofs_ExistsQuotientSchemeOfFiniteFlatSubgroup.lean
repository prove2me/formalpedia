-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:02.100813+00:00
-- url     : https://prove2.me/theorems/d0a11747-3547-4fa6-a3ef-ecc2350cd809
-- title:
--   Exists Quotient Scheme Of Finite Flat Subgroup
-- statement:
--   Definitions and structural lemmas for Exists Quotient Scheme Of Finite Flat Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsQuotientSchemeOfFiniteFlatSubgroup.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
end GlobalTheory.AffineQuotient
namespace GlobalTheory
open AffineQuotient
end GlobalTheory


