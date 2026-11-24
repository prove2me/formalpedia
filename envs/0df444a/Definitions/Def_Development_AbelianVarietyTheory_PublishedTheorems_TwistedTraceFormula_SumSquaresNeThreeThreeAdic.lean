-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:07.784355+00:00
-- url     : https://prove2.me/theorems/cb3cd932-3926-486c-8a3a-a96ed519f7d0
-- title:
--   Sum Squares Ne Three Three Adic
-- statement:
--   Definitions and structural lemmas for Sum Squares Ne Three Three Adic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal
namespace GlobalTheory.HermLocal.Model
section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
noncomputable def conjSqrt : QuadraticAlgebra K d 0 ≃ₐ[K] QuadraticAlgebra K d 0 :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by
    change star _ = _
    ext <;> simp
end Quad
instance two_not_sq : Fact (∀ r : ℚ_[2], r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg Padic.valuation h
  have h2 : (2 : ℚ_[2]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
  rw [Padic.valuation_pow, h2] at h1
  omega⟩
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
theorem norm_one_add_sq (t : ℚ_[3]) (ht : ‖t‖ ≤ 1) : ‖1 + t ^ 2‖ = 1 := by
  let s : ℤ_[3] := ⟨t, ht⟩
  have hu : IsUnit (1 + s ^ 2) := by
    by_contra h
    have h1 : 1 + s ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := 3)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, map_add, map_pow, map_one] at h1
    revert h1
    generalize PadicInt.toZMod s = z
    revert z; decide
  exact PadicInt.isUnit_iff.1 hu
instance neg_one_not_sq : Fact (∀ r : ℚ_[3], r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 : ‖r‖ ^ 2 = 1 := by rw [← norm_pow, h]; simp
  have h2 : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
  have := norm_one_add_sq r h2
  rw [h] at this
  simp at this⟩
section Global
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end Global
end GlobalTheory.HermLocal.Model


