-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:19.902531+00:00
-- url     : https://prove2.me/theorems/69b7fe9a-f219-4163-99e9-1a7cbf2cc7a6
-- title:
--   Tensor Norm Le Iff Tensor Norm Bound
-- statement:
--   Definitions and structural lemmas for Tensor Norm Le Iff Tensor Norm Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TensorNormLeIffTensorNormBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorPlaceNorm_fockS_self_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.TensorNormCompare
open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke
variable {ι : Type} [Fintype ι] {n n' : ℕ}
theorem fockS_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockS f f).re := by
  obtain ⟨r, hr, h⟩ := TensorPlaceNorm.fockS_self_nonneg f
  rw [h, Complex.ofReal_re]; exact hr
theorem fockS_re_pos' {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  have : (fockS f f).re = ∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) := by
    have e : fockS f f = ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) : ℝ) : ℂ) := by
      unfold fockS
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Complex.conj_mul']
      rfl
    rw [e, Complex.ofReal_re]
  rw [this]
  refine Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr (mem_support_iff.mp hm)) 2) ?_)
    (support_nonempty.mpr hf)
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
theorem fockS_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : (starRingEnd ℂ) (fockS g f) = fockS f g := by
  classical
  rw [fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
    fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, Complex.star_def, Complex.conj_conj]
  ring
def fockCore (σ : Type) : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) where
  inner f g := fockS f g
  conj_inner_symm f g := fockS_conj_symm f g
  re_inner_nonneg f := fockS_re_nonneg f
  add_left f f' g := by
    change fockL (f + f') g = fockL f g + fockL f' g
    rw [map_add, LinearMap.add_apply]
  smul_left f g r := by
    change fockL (r • f) g = _ * fockL f g
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite f h := by
    by_contra hf
    have h' : fockS f f = 0 := h
    have := fockS_re_pos' hf
    rw [h'] at this
    simp at this
end GlobalTheory.TensorNormCompare


