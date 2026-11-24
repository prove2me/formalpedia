-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DetCoverMatrixValuationOne
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_DetCoverMatrixValuationOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:49.513256+00:00
-- url     : https://prove2.me/theorems/8663d3d1-0cd7-475d-bd89-518e1ac309ab
-- title:
--   Det Cover Matrix Valuation One
-- statement:
--   Definitions and structural lemmas for Det Cover Matrix Valuation One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DetCoverMatrixValuationOne.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.UG (GLint)
noncomputable section
namespace GlobalTheory.GLintCover
section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
theorem entry_mem {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v))
    (i j : Fin n) : (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v := by
  obtain ⟨y, rfl⟩ := hX
  exact ((y : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)) i j).2
variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}
end
end GlobalTheory.GLintCover
noncomputable section
namespace GlobalTheory.GLintCover
section Count
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
def ent (k : GLint (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) :=
  Matrix.of fun i j => ⟨((k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j,
    entry_mem k.2 i j⟩
theorem coe_ent (k : GLint (Fin n) (Formalism.UG.Ov F v)) (i j : Fin n) :
    ((ent k i j : v.adicCompletionIntegers F) : v.adicCompletion F) =
      ((k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := rfl
theorem ent_one : ent (1 : GLint (Fin n) (Formalism.UG.Ov F v)) = 1 := by
  ext i j : 2
  rw [coe_ent]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]
theorem ent_mul (k k' : GLint (Fin n) (Formalism.UG.Ov F v)) : ent (k * k') = ent k * ent k' := by
  ext i j : 2
  rw [coe_ent, Matrix.mul_apply]
  simp [Matrix.mul_apply, coe_ent]
def redHom (I : Ideal (v.adicCompletionIntegers F)) :
    GLint (Fin n) (Formalism.UG.Ov F v) →* Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F ⧸ I) where
  toFun k := (Ideal.Quotient.mk I).mapMatrix (ent k)
  map_one' := by simp [ent_one]
  map_mul' k k' := by simp [ent_mul]
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}
def X0 (π : v.adicCompletionIntegers F) (c : Fin n → Fin n → ℕ) (y : Fin n → Fin n → v.adicCompletionIntegers F) :
    Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := 1 + Matrix.of fun i j => π ^ c i j * y i j
theorem det_cover_matrix_valuation_one (hϖO : ϖ ∈ v.adicCompletionIntegers F) (hϖ : Formalism.UG.IsUnifV F v ϖ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ i j, 1 ≤ c i j) (y : Fin n → Fin n → v.adicCompletionIntegers F) :
    Valued.v (((X0 ⟨ϖ, hϖO⟩ c y).det : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
  set π : v.adicCompletionIntegers F := ⟨ϖ, hϖO⟩
  have hπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π)
  have hmk : (Ideal.Quotient.mk (Ideal.span {π})).mapMatrix (X0 π c y) = 1 := by
    ext i j
    have h0 : c i j ≠ 0 := by have := hc i j; omega
    by_cases h : i = j
    · subst h; simp [X0, hπ, zero_pow h0]
    · simp [X0, hπ, zero_pow h0, Matrix.one_apply_ne h]
  have hd : Ideal.Quotient.mk (Ideal.span {π}) ((X0 π c y).det) = Ideal.Quotient.mk (Ideal.span {π}) 1 := by
    rw [RingHom.map_det, hmk, Matrix.det_one, map_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hd)
  have hdet : (X0 π c y).det = 1 + z * π := by rw [hz]; ring
  rw [hdet]
  have : (((1 + z * π : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 + (z : v.adicCompletion F) * ϖ := by
    push_cast; rfl
  rw [this]
  apply Valuation.map_one_add_of_lt
  rw [map_mul, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ]
  have hz1 : Valued.v (z : v.adicCompletion F) ≤ 1 := z.2
  calc Valued.v (z : v.adicCompletion F) * WithZero.exp (-1 : ℤ) ≤ 1 * WithZero.exp (-1 : ℤ) := by gcongr
    _ < 1 := by rw [one_mul, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
end Count
end GlobalTheory.GLintCover
noncomputable section
namespace GlobalTheory.GLintCover
section Main
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}
theorem det_map_cover_matrix (π : v.adicCompletionIntegers F) (c : Fin n → Fin n → ℕ)
    (y : Fin n → Fin n → v.adicCompletionIntegers F) :
    ((X0 π c y).map (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F))).det =
      (((X0 π c y).det : v.adicCompletionIntegers F) : v.adicCompletion F) :=
  (RingHom.map_det (v.adicCompletionIntegers F).toSubring.subtype (X0 π c y)).symm
def gOf (hϖO : ϖ ∈ v.adicCompletionIntegers F) (hϖ : Formalism.UG.IsUnifV F v ϖ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ i j, 1 ≤ c i j) (y : Fin n → Fin n → v.adicCompletionIntegers F) : GL (Fin n) (v.adicCompletion F) :=
  Matrix.GeneralLinearGroup.mk'' ((X0 ⟨ϖ, hϖO⟩ c y).map (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)))
    (by
      rw [isUnit_iff_ne_zero, det_map_cover_matrix]
      intro h
      have := det_cover_matrix_valuation_one hϖO hϖ c hc y
      rw [h, map_zero] at this
      exact zero_ne_one this)
end Main
end GlobalTheory.GLintCover


