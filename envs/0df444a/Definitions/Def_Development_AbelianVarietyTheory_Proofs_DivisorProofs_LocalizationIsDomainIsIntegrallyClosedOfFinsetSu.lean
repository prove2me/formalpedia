-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:27.65701+00:00
-- url     : https://prove2.me/theorems/346d806f-8148-48c3-8e8f-a03f088b5dc4
-- title:
--   Localization Is Domain Is Integrally Closed Of Finset Su
-- statement:
--   Definitions and structural lemmas for Localization Is Domain Is Integrally Closed Of Finset Su, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
namespace LocalizationIntegrallyClosedDomain
variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
variable {Q}
end LocalizationIntegrallyClosedDomain
end GlobalTheory
namespace GlobalTheory
namespace LocalizationIntegrallyClosedDomain
variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]
end LocalizationIntegrallyClosedDomain
end GlobalTheory


