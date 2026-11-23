-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
-- name    : ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:17.483171+00:00
-- url     : https://prove2.me/theorems/f3b6cf03-b512-49b7-b29d-b0fb6b30a5cb
-- title:
--   Exists Torus Point One Le Norm Sum
-- statement:
--   Definitions and structural lemmas for Exists Torus Point One Le Norm Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
noncomputable abbrev unitBallRing (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring
end ReciprocityTheory.MultiplicativeHeights


