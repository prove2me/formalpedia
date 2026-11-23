-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
-- name    : GroundTheory_AutomorphicForms_HermitianWittExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:28.211402+00:00
-- url     : https://prove2.me/theorems/63841c4c-90e6-4696-94c2-ca471da87054
-- title:
--   Hermitian Witt Extension
-- statement:
--   Definitions and structural lemmas for Hermitian Witt Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWittExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
namespace HermitianForm
end HermitianForm
end GroundTheory.Automorphic
end


