-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_SplitPlacesDiscriminantDepthOfSplitAt
-- name    : Development_AutomorphicArithmetic_CMTraceForms_SplitPlacesDiscriminantDepthOfSplitAt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:27.572467+00:00
-- url     : https://prove2.me/theorems/d16ac3dd-4144-45eb-ac4d-e59a1cea450a
-- title:
--   Split Places Discriminant Depth Of Split At
-- statement:
--   Definitions and structural lemmas for Split Places Discriminant Depth Of Split At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/SplitPlacesDiscriminantDepthOfSplitAt.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_TraceFormDecompositionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
namespace UpperTheory.Depth.SplitPl
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end UpperTheory.Depth.SplitPl


