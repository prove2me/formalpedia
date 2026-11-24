-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:02.590603+00:00
-- url     : https://prove2.me/theorems/925cb8b7-f74a-48cb-8875-fa5edd70de31
-- title:
--   Even Card Of Not Lone
-- statement:
--   Definitions and structural lemmas for Even Card Of Not Lone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EvenCardOfNotLone.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_nm_mul_adicCompletion
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
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
namespace GlobalTheory.HilbertRecip
abbrev Place (F : Type) [Field F] [NumberField F] : Type :=
  HeightOneSpectrum (𝓞 F) ⊕ (F →+* ℝ)
variable {F : Type} [Field F] [NumberField F]
def nrm : Place F → Fˣ → Subgroup Fˣ
  | .inl v, δ => normSub (algebraMap F (v.adicCompletion F)) (δ : F)
  | .inr σ, δ => normSub σ (δ : F)
def sqr : Place F → Subgroup Fˣ
  | .inl v => sqSub (algebraMap F (v.adicCompletion F))
  | .inr σ => sqSub σ
def Over (S : Finset (HeightOneSpectrum (𝓞 F))) : Place F → Prop
  | .inl v => v ∈ S
  | .inr _ => True
def Lone (p : Place F) : Prop := ∃ a b : Fˣ, a ∉ nrm p b ∧ ∀ q, q ≠ p → a ∈ nrm q b
open Classical in

def hs (p : Place F) (a b : Fˣ) : ℤˣ := if a ∈ nrm p b then 1 else -1
theorem exists_field (p : Place F) : ∃ (A : Type) (_ : Field A) (_ : CharZero A) (φ : F →+* A),
    (∀ δ : Fˣ, nrm p δ = normSub φ (δ : F)) ∧ sqr p = sqSub φ ∧
    ∀ d x y : A, d ≠ 0 → x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  rcases p with v | σ
  · haveI : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    refine ⟨v.adicCompletion F, inferInstance, inferInstance, algebraMap F (v.adicCompletion F),
      fun δ => rfl, rfl, ?_⟩
    intro d x y hd hx hy hnx hny
    exact nm_mul_adicCompletion F v hd hx hy hnx hny
  · refine ⟨ℝ, inferInstance, inferInstance, σ, fun δ => rfl, rfl, ?_⟩
    intro d x y _ _ _ hnx hny
    have key : ∀ z : ℝ, 0 ≤ z → Nm d z := fun z hz =>
      ⟨Real.sqrt z, 0, by rw [Real.sq_sqrt hz]; ring⟩
    have hx' : x < 0 := by
      by_contra h
      exact hnx (key x (not_lt.mp h))
    have hy' : y < 0 := by
      by_contra h
      exact hny (key y (not_lt.mp h))
    exact key _ (mul_pos_of_neg_of_neg hx' hy').le
theorem mul_mem_nrm_of_not {p : Place F} {a a' b : Fˣ} (h : a ∉ nrm p b) (h' : a' ∉ nrm p b) :
    a * a' ∈ nrm p b := by
  obtain ⟨A, _, _, φ, hn, -, hm⟩ := exists_field p
  simp only [hn, mem_normSub] at h h' ⊢
  simp only [Units.val_mul, map_mul]
  exact hm _ _ _ ((map_ne_zero φ).mpr b.ne_zero) ((map_ne_zero φ).mpr a.ne_zero)
    ((map_ne_zero φ).mpr a'.ne_zero) h h'
theorem hs_mul_left (p : Place F) (a a' b : Fˣ) : hs p (a * a') b = hs p a b * hs p a' b := by
  unfold hs
  by_cases h : a ∈ nrm p b <;> by_cases h' : a' ∈ nrm p b
  · rw [if_pos h, if_pos h', if_pos (mul_mem h h'), mul_one]
  · rw [if_pos h, if_neg h', if_neg, one_mul]
    intro hm
    exact h' (by simpa using mul_mem (inv_mem h) hm)
  · rw [if_neg h, if_pos h', if_neg, mul_one]
    intro hm
    exact h (by simpa using mul_mem hm (inv_mem h'))
  · rw [if_neg h, if_neg h', if_pos (mul_mem_nrm_of_not h h')]
    decide
def hsLeft (p : Place F) (b : Fˣ) : Fˣ →* ℤˣ := MonoidHom.mk' (fun a => hs p a b)
  fun a a' => hs_mul_left p a a' b
end GlobalTheory.HilbertRecip
namespace GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
end GlobalTheory.QuadSymbol
end


