-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
-- name    : GroundTheory_AutomorphicForms_HermitianClassification
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:46.725295+00:00
-- url     : https://prove2.me/theorems/498c614f-f9c3-44e5-ba77-0f3ff0f37f49
-- title:
--   Hermitian Classification
-- statement:
--   Definitions and structural lemmas for Hermitian Classification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
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
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
section General
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
end General
section Local
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
namespace HermitianForm
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
end HermitianForm
end Local
end GroundTheory.Automorphic
end


