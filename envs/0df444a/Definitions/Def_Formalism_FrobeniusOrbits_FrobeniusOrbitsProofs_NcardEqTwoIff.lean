-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:07.044827+00:00
-- url     : https://prove2.me/theorems/dcfba802-0c8f-4412-9285-32b0e98fc514
-- title:
--   Ncard Eq Two Iff
-- statement:
--   Definitions and structural lemmas for Ncard Eq Two Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_isCMField_hostE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Eta
section CM
variable (K : Type) [Field K] [NumberField K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K
instance isGaloisGroup : IsGaloisGroup (K ≃ₐ[K⁺] K) (𝓞 K⁺) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ K⁺ K
end CM
section Host
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
def cQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b :=
  haveI := isCMField_hostE hqd h
  (IsCMField.complexConj (hostE ζ a b)).restrictScalars ℚ
end Host
end Eta
open Eta
end Formalism.FrobeniusOrbits


