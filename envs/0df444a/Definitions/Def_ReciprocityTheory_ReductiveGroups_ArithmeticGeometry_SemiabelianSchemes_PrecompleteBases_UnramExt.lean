-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_UnramExt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_UnramExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:14.041809+00:00
-- url     : https://prove2.me/theorems/35209548-13b2-4774-9e8a-75c6ca84bf00
-- title:
--   Unram Ext
-- statement:
--   Definitions and structural lemmas for Unram Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/UnramExt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Unramified.LocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing Polynomial
open scoped IntermediateField
namespace ReciprocityTheory.ChartRestriction.G.Semi.Unr
open ReciprocityTheory.ChartRestriction.G.Semi.Nb
end ReciprocityTheory.ChartRestriction.G.Semi.Unr


