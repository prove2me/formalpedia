-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:49.832729+00:00
-- url     : https://prove2.me/theorems/28c3569c-6ade-422e-9fa1-060056dfd955
-- title:
--   Weighted Least Squares Bound
-- statement:
--   Definitions and structural lemmas for Weighted Least Squares Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
namespace GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}
end GlobalTheory.WeightedLS


