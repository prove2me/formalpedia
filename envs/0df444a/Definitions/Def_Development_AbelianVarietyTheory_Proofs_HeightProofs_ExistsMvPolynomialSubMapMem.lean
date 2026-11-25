-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMvPolynomialSubMapMem
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMvPolynomialSubMapMem
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:19.603505+00:00
-- url     : https://prove2.me/theorems/bc1c6448-31fe-4ca9-95c1-d726503659ed
-- title:
--   Exists Mv Polynomial Sub Map Mem
-- statement:
--   Definitions and structural lemmas for Exists Mv Polynomial Sub Map Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMvPolynomialSubMapMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
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
open IsLocalRing
end GlobalTheory


