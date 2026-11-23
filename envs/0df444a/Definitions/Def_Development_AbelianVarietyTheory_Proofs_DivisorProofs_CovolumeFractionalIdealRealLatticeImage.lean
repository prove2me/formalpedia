-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:44.888019+00:00
-- url     : https://prove2.me/theorems/4f4a9aa1-b814-4c7a-8988-f2427794e698
-- title:
--   Covolume Fractional Ideal Real Lattice Image
-- statement:
--   Definitions and structural lemmas for Covolume Fractional Ideal Real Lattice Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImage.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply


set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
namespace GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
def embPlace : (F →+* ℝ) ≃ {w : InfinitePlace F // IsReal w} where
  toFun τ := ⟨mk (Complex.ofRealHom.comp τ), IsTotallyReal.isReal _⟩
  invFun w := embedding_of_isReal w.2
  left_inv τ := by
    have h : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
      isReal_of_mk_isReal (IsTotallyReal.isReal _)
    ext x
    apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal h]
    rfl
  right_inv w := by
    apply Subtype.ext
    have : Complex.ofRealHom.comp (embedding_of_isReal w.2) = embedding w.1 := by
      ext x; simp
    simp only [this, mk_embedding]
instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
def toMixed : RSp F ≃ₗ[ℝ] mixedSpace F where
  toFun x := (fun w => x (embPlace.symm w), 0)
  invFun p := WithLp.toLp 2 (fun τ => p.1 (embPlace τ))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by ext τ; simp
  right_inv p := by
    refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
    simp
end GlobalTheory.LipschitzCovol


