-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:22.727454+00:00
-- url     : https://prove2.me/theorems/59d6fa33-0627-419f-a9b0-95131900cd54
-- title:
--   Galois
-- statement:
--   Definitions and structural lemmas for Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Galois
section Roots
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
end Roots
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
theorem layer_galois (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    IsGalois ℚ L ∧ Module.finrank ℚ L = 2 ^ (e + 2 + 1) ∧
    (∀ σ τ : Gal(L/ℚ), galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ) ∧
    Function.Bijective (galMap h.1 a b) :=
  layerGalois (e + 2) q d (by omega) hqd L ζ a b h
def tau0 (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : Gal(L/ℚ) :=
  ((layer_galois hqd h).2.2.2.2 ((-1, 1, 1) : GalL (e + 2))).choose
end Layer
section Host
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Host
end Galois
open Galois
end Formalism.FrobeniusOrbits


