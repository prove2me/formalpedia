-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
-- name    : ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:03.476402+00:00
-- url     : https://prove2.me/theorems/94c2dc82-b371-40a8-bad4-ed571e45f539
-- title:
--   Valuation Pairwise Difference Product Pow Le Colength S
-- statement:
--   Definitions and structural lemmas for Valuation Pairwise Difference Product Pow Le Colength S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
variable {n s : ℕ}
end DeterminantValuationBounds
end ReciprocityTheory.PGsh.Up


