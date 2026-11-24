-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehler
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:24.914806+00:00
-- url     : https://prove2.me/theorems/89d5a89f-d10c-4f13-af25-18911aacc268
-- title:
--   Frobenius Derivation Factors Through Kaehler
-- statement:
--   Definitions and structural lemmas for Frobenius Derivation Factors Through Kaehler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusDerivationFactorsThroughKaehler.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI.FrobDeriv
def FrobTwist (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (M : Type) : Type := M
variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]
instance : AddCommGroup (FrobTwist K p M) := inferInstanceAs (AddCommGroup M)
noncomputable instance : Module K (FrobTwist K p M) :=
  Module.compHom M (frobenius K p)
end GlobalTheory.DI.FrobDeriv


