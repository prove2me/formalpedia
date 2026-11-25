-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_FiniteHZeroOfExact
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_FiniteHZeroOfExact
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:43.809206+00:00
-- url     : https://prove2.me/theorems/b39b55b3-b57a-5e33-b5ee-01932db69eb3
-- title:
--   Finite HZero Of Exact
-- statement:
--   Definitions and structural lemmas for Finite HZero Of Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/FiniteHZeroOfExact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w v₁ v₂ v₃
namespace Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
end Cech
end
end GroundTheory.Heights₂.Heights.Kleiman


