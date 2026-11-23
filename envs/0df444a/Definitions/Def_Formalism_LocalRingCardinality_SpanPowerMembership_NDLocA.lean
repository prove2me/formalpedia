-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:24.436803+00:00
-- url     : https://prove2.me/theorems/3a23dfa9-c476-4523-8153-67fada9338d4
-- title:
--   NDLoc A
-- statement:
--   Definitions and structural lemmas for NDLoc A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
def ball : ValuationSubring (PadicAlgCl l) :=
  (Valued.v : Valuation (PadicAlgCl l) NNReal).valuationSubring
variable {l} {Ω : Type} [Field Ω]
def placeJ (j : Ω →+* PadicAlgCl l) : ValuationSubring Ω := (ball l).comap j
variable (l) in
theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv]
  simpa using h
variable (l) in

def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero
end Formalism.BasicNotions.Examples₂.LB


