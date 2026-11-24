-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:51.826141+00:00
-- url     : https://prove2.me/theorems/9e5c12f2-59f9-4585-b788-a31a59d1ebe5
-- title:
--   Exists Nsmul Mul Vec Mem Hat
-- statement:
--   Definitions and structural lemmas for Exists Nsmul Mul Vec Mem Hat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/NefEffectiveCones/ExistsNsmulMulVecMemHat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.CompanionTheory.HatBound
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
end GlobalTheory.CompanionTheory.HatBound


