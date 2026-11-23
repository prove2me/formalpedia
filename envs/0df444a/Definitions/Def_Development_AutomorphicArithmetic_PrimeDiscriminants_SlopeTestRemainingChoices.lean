-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:11.756263+00:00
-- url     : https://prove2.me/theorems/d48544e7-1daa-47de-ba1c-8b67d4b850bb
-- title:
--   Slope Test Remaining Choices
-- statement:
--   Definitions and structural lemmas for Slope Test Remaining Choices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SlopeTestRemainingChoices.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))
def maxPrime (Q : ℕ) : ℕ := Q.primeFactors.sup id
def primeChoiceOfBound (Q : ℕ) : ℕ := if Nat.Coprime Q 15 then 3 else nextPrime (maxPrime Q)
def secondPrimeChoiceOfBound (Q : ℕ) : ℕ := if Nat.Coprime Q 15 then 5 else nextPrime (nextPrime (maxPrime Q))
namespace HostRaw
variable {φ : Frame} (H : HostRaw φ)
def rr : ℕ := primeChoiceOfBound H.QS
def rr' : ℕ := secondPrimeChoiceOfBound H.QS
def radS : ℕ := ∏ l ∈ H.small, l
def bigP : ℕ := ∏ p ∈ (∏ l ∈ H.small, l * (l - 1)).primeFactors.erase 2, p
def vdH (p : ℕ) : ℝ := (padicValNat p (NumberField.discr H.E).natAbs : ℝ) / (Module.finrank ℚ H.E : ℝ)
def vdS : ℝ := ((H.small.sup fun l => padicValNat l (NumberField.discr H.E).natAbs : ℕ) : ℝ) / (Module.finrank ℚ H.E : ℝ)
end HostRaw
end Formalism.HC
end


