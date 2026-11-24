-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankFixedSubmoduleComplexification
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankFixedSubmoduleComplexification
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:55.500327+00:00
-- url     : https://prove2.me/theorems/ef5dde9e-8116-47da-a056-384acb658ebc
-- title:
--   Finrank Fixed Submodule Complexification
-- statement:
--   Definitions and structural lemmas for Finrank Fixed Submodule Complexification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankFixedSubmoduleComplexification.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry
universe u
namespace GlobalTheory.GaloisDescent
section Instances
variable (K L G V : Type*) [CommSemiring K] [Semiring L] [Algebra K L] [Monoid G]
  [MulSemiringAction G L]
end Instances
section Group
variable {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
end Group
section AlgEquiv
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Algebra K ℂ]
end AlgEquiv
end GlobalTheory.GaloisDescent


