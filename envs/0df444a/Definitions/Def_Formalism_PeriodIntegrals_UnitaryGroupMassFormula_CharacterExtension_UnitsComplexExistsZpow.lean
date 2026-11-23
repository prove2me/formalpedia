-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterExtension_UnitsComplexExistsZpow
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterExtension_UnitsComplexExistsZpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:43.114849+00:00
-- url     : https://prove2.me/theorems/bf16b943-163b-421d-8b5d-4b20260718d8
-- title:
--   Units Complex Exists Zpow
-- statement:
--   Definitions and structural lemmas for Units Complex Exists Zpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterExtension/UnitsComplexExistsZpow.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.CharExtendWork
theorem units_complex_exists_zpow (a : ℂˣ) (n : ℤ) (hn : n ≠ 0) : ∃ x : ℂˣ, x ^ n = a := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact a.ne_zero hz.symm
  set u : ℂˣ := Units.mk0 z hz0 with hu
  have hu' : u ^ n.natAbs = a := by
    ext
    simp [hu, hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨u, ?_⟩
    rw [h, zpow_natCast, hu']
  · refine ⟨u⁻¹, ?_⟩
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu']
noncomputable def divisibleUnitsComplex : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if h : n = 0 then 0 else
    Additive.ofMul (Classical.choose (units_complex_exists_zpow a.toMul n h))
  div_zero a := by simp
  div_cancel {n} a hn := by
    rw [dif_neg hn, ← ofMul_zpow, Classical.choose_spec (units_complex_exists_zpow a.toMul n hn)]
    rfl
end PI.CharExtendWork


