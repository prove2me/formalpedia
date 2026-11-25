-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
-- name    : GroundTheory_GlobalFields_KummerTheory_Splitting
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:32.909686+00:00
-- url     : https://prove2.me/theorems/f0890ba0-5517-4705-a2e5-307fadd66d01
-- title:
--   Splitting
-- statement:
--   Definitions and structural lemmas for Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
section Algebra
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
def algEquivOfFinrankEqOne (h : finrank F E = 1) : F ≃ₐ[F] E :=
  AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)
end Algebra
section Finite
open SemiLocal
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
def SplitsCompletely (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1
variable {L} (v : HeightOneSpectrum (𝓞 K))
end Finite
end GroundTheory.Global


