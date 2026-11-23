-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:46.003893+00:00
-- url     : https://prove2.me/theorems/2fce8d11-681f-4b8e-aa98-a1a7cf3b09e6
-- title:
--   Unramified Ideal Locus Characterization
-- statement:
--   Definitions and structural lemmas for Unramified Ideal Locus Characterization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
namespace GlobalTheory.SS.Dil
def dd (R B S : Type) [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S] (b : B) :
    S ⊗[B] (KaehlerDifferential R B) := (1 : S) ⊗ₜ[B] KaehlerDifferential.D R B b
section
variable {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
end
def gr {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)
    (p : MvPolynomial (Fin n) R) : Fin n → S := fun i => σ (pderiv i p)
section
variable {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)
end
end GlobalTheory.SS.Dil
namespace GlobalTheory.SS
open Dil
end GlobalTheory.SS
end


