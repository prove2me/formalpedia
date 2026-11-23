-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IffNum
-- name    : Development_AutomorphicArithmetic_WeightCongruences_IffNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:18.487409+00:00
-- url     : https://prove2.me/theorems/69a78e73-fdd4-4566-a712-b5c66cdec743
-- title:
--   Iff Num
-- statement:
--   Definitions and structural lemmas for Iff Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IffNum.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.MUQ
variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {φ : ι → E →+* K} {e : ι → ℚ}
end UpperTheory.MUQ


