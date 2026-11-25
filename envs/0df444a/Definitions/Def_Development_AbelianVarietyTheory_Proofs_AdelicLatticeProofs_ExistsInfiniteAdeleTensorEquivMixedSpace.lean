-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInfiniteAdeleTensorEquivMixedSpace
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInfiniteAdeleTensorEquivMixedSpace
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:13.054196+00:00
-- url     : https://prove2.me/theorems/43affbf5-5832-4213-a727-d1f5a809c107
-- title:
--   Exists Infinite Adele Tensor Equiv Mixed Space
-- statement:
--   Definitions and structural lemmas for Exists Infinite Adele Tensor Equiv Mixed Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInfiniteAdeleTensorEquivMixedSpace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory.InfAdeleMixed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def toMixed [IsTotallyComplex E] {R : Type} [CommRing R]
    (θ : {w : InfinitePlace E // w.IsComplex} → (R →+* ℂ)) : R →+* mixedSpace E :=
  RingHom.prod
    (Pi.ringHom fun w : {w : InfinitePlace E // w.IsReal} =>
      (False.elim (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2) : R →+* ℝ))
    (Pi.ringHom θ)
end GlobalTheory.InfAdeleMixed


