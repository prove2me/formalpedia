-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_ValOneOfNotMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_ValOneOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:42.961995+00:00
-- url     : https://prove2.me/theorems/ae16ae14-1f96-47b3-a344-f5bcfd48222d
-- title:
--   Val One Of Not Mem
-- statement:
--   Definitions and structural lemmas for Val One Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/ValOneOfNotMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CntNotIntW
open NumberField IsDedekindDomain ValuativeRel
section Val
variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [ValuativeRel K]
theorem sig_int (σ : E →+* K) (o : 𝓞 E) : σ (o : E) ∈ 𝒪[K] :=
  (Valuation.integer.integers (valuation K)).mem_of_integral
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe o)).tower_top)
theorem sig_le_one (σ : E →+* K) (o : 𝓞 E) : valuation K (σ (o : E)) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (sig_int σ o)
def vIdeal (σ : E →+* K) : Ideal (𝓞 E) where
  carrier := {o | valuation K (σ (o : E)) < 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, map_add] at hx hy ⊢
    exact Valuation.map_add_lt _ hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, map_zero, Valuation.map_zero]
    exact zero_lt_one
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, map_mul, Valuation.map_mul] at hx ⊢
    exact mul_lt_of_le_one_of_lt (sig_le_one σ c) hx
theorem mem_vIdeal (σ : E →+* K) (o : 𝓞 E) : o ∈ vIdeal σ ↔ valuation K (σ (o : E)) < 1 := Iff.rfl
theorem vIdeal_prime (σ : E →+* K) : (vIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_vIdeal]
    simp
  · intro x y hxy
    rw [mem_vIdeal, mem_vIdeal]
    rw [mem_vIdeal] at hxy
    by_contra hc
    push Not at hc
    have hx : valuation K (σ (x : E)) = 1 := le_antisymm (sig_le_one σ x) hc.1
    have hy : valuation K (σ (y : E)) = 1 := le_antisymm (sig_le_one σ y) hc.2
    simp only [MulMemClass.coe_mul, map_mul, Valuation.map_mul, hx, hy, mul_one] at hxy
    exact lt_irrefl _ hxy
def vPrime (σ : E →+* K) (l : ℕ) (hl0 : l ≠ 0) (hl : valuation K (l : K) < 1) : HeightOneSpectrum (𝓞 E) where
  asIdeal := vIdeal σ
  isPrime := vIdeal_prime σ
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 E) ∈ vIdeal σ := by
      rw [mem_vIdeal]
      simpa using hl
    rw [h, Ideal.mem_bot] at hm
    exact hl0 (by exact_mod_cast hm)
end Val
end PI.CntNotIntW


