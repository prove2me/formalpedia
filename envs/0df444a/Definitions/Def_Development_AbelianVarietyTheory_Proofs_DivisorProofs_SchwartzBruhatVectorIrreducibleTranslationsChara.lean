-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:01.00846+00:00
-- url     : https://prove2.me/theorems/5829338e-9ab2-4f47-b45f-493d2eaae7ed
-- title:
--   Schwartz Bruhat Vector Irreducible Translations Chara
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Vector Irreducible Translations Chara, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatVectorIrreducibleTranslationsChara.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Theorems.Thm_GlobalTheory_SBUnif_exists_nat_mem_mul_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.IrredSBVec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem norm_char_eq_one (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) : ‖ψ0 x‖ = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn, hxn⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at hxn
  have hp : ψ0 x ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
    exact h1 _ hxn
  have := congrArg norm hp
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
def toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (norm_char_eq_one ψ0 h1 x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ0 a b)
end GlobalTheory.IrredSBVec


