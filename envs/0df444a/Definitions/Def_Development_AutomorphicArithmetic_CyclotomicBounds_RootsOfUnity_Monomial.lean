-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:25.845664+00:00
-- url     : https://prove2.me/theorems/a2cb9d7d-a3be-4620-9a0b-59d37f5525c1
-- title:
--   Monomial
-- statement:
--   Definitions and structural lemmas for Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
namespace UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
end UpperTheory.Mu


