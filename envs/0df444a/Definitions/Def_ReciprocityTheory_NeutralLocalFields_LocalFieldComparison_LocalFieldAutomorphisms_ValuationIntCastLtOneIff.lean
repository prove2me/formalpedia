-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:04.077663+00:00
-- url     : https://prove2.me/theorems/ac6be803-db74-4ff8-9fd8-9962a1d76d2f
-- title:
--   Valuation Int Cast Lt One Iff
-- statement:
--   Definitions and structural lemmas for Valuation Int Cast Lt One Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ValuationIntCastLtOneIff.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
def ratPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)})
  isPrime := by
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.mem_comap, map_natCast, Ideal.mem_span_singleton]
    rw [h, Ideal.mem_bot] at hmem
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hmem)
end ReciprocityTheory.Neutral.Cmp


