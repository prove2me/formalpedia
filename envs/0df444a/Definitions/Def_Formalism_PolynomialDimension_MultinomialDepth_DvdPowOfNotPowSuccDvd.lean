-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DvdPowOfNotPowSuccDvd
-- name    : Formalism_PolynomialDimension_MultinomialDepth_DvdPowOfNotPowSuccDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:59.994574+00:00
-- url     : https://prove2.me/theorems/6280cd49-66aa-4c86-b1b9-a14012601a3e
-- title:
--   Dvd Pow Of Not Pow Succ Dvd
-- statement:
--   Definitions and structural lemmas for Dvd Pow Of Not Pow Succ Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DvdPowOfNotPowSuccDvd.lean

import Definitions.Def_Formalism_PolynomialDimension_EdgeSumGoodRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open Finset
namespace Formalism.CountingSumsFrames
section Partner
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Partner
end Formalism.CountingSumsFrames


