-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
-- name    : Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:35.79381+00:00
-- url     : https://prove2.me/theorems/2de15f50-e8d9-49b2-b645-4d53b056f40e
-- title:
--   Real Subfield Le Compositum
-- statement:
--   Definitions and structural lemmas for Real Subfield Le Compositum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois

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
section Hcl
variable {e : ℕ}
end Hcl
section Subfields
variable {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
end Subfields
section Signs
variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
end Signs
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
theorem galE_mul (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ :=
  (hostGalois e q d hqd L ζ a b h).2.2.1 σ τ
theorem galE_bijective (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Function.Bijective (galE e ζ a b) :=
  (hostGalois e q d hqd L ζ a b h).2.2.2
def galEquiv (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ≃* GG e :=
  MulEquiv.ofBijective (MonoidHom.mk' (galE e ζ a b) (galE_mul hqd h)) (galE_bijective hqd h)
def conjE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b :=
  (galEquiv hqd h).symm (cc e)
end Layer
end Formalism.FrobeniusOrbits


