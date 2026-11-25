-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:17:22.505024+00:00
-- url     : https://prove2.me/theorems/536b3826-7a3b-465f-80cc-c9a7e8607209
-- title:
--   Exists Measurable Roots Enumeration
-- statement:
--   Definitions and structural lemmas for Exists Measurable Roots Enumeration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
open Polynomial
end GlobalTheory


