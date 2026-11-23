-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:35.921429+00:00
-- url     : https://prove2.me/theorems/105ab7a9-c957-47b6-90cc-f55099f7bb34
-- title:
--   Mem Prime Compl Iff
-- statement:
--   Definitions and structural lemmas for Mem Prime Compl Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace LocBasisPlaceWork
variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p])
theorem norm_le_one (a : 𝓞 E) : ‖ρ (a : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))
  have h2 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (ρ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe a)
  have h3 := hv.mem_of_integral h2
  have h4 : ‖ρ (a : E)‖₊ ≤ 1 := h3
  exact_mod_cast h4
def plc : Ideal (𝓞 E) where
  carrier := {a | ‖ρ (a : E)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖ρ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖ρ ((0 : 𝓞 E) : E)‖ < 1
    simp
  smul_mem' c a ha := by
    show ‖ρ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one ρ c)) ha
theorem mem_plc (a : 𝓞 E) : a ∈ plc ρ ↔ ‖ρ (a : E)‖ < 1 := Iff.rfl
instance plc_isPrime : (plc ρ).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 E) ∈ plc ρ := h ▸ Submodule.mem_top
    rw [mem_plc] at h1
    simp at h1
  mem_or_mem' {a b} hab := by
    rw [mem_plc, mem_plc]
    have hab' : ‖ρ (algebraMap (𝓞 E) E (a * b))‖ < 1 := hab
    rw [map_mul, map_mul, norm_mul] at hab'
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (le_trans zero_le_one h.1)
    change ‖ρ (algebraMap (𝓞 E) E a)‖ * ‖ρ (algebraMap (𝓞 E) E b)‖ < 1 at hab'
    linarith
end LocBasisPlaceWork


