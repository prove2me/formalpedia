-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:54:01.018046+00:00
-- url     : https://prove2.me/theorems/d8dceddb-39de-43bf-b80a-fb63246cf44e
-- title:
--   Elementary Generator Adjoint
-- statement:
--   Definitions and structural lemmas for Elementary Generator Adjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace HermitianAdjointLemmas
section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Linfty
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def Out (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop := p.val < i.val ∨ 2 * r + k < p.val + i.val
def SuppV (i : Fin (r + 1)) (W : Mx k r) : Prop := ∀ p q, (Out i p ∨ Out i q) → W p q = 0
lemma hpart1_add (A B : Mx k r) :
    hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
  unfold hpart1
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel
lemma hpart2_add (A B : Mx k r) :
    hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
  unfold hpart2
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel
lemma two_I_inv : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero) two_ne_zero]
  linear_combination (2 : ℂ) * Complex.I_sq
lemma star_re_im (c : ℂ) : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp
lemma hpart1_smul (c : ℂ) (W : Mx k r) :
    hpart1 (Hpk k r) (c • W) = c.re • hpart1 (Hpk k r) W - c.im • hpart2 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> ring_nf
lemma hpart2_smul (c : ℂ) (W : Mx k r) :
    hpart2 (Hpk k r) (c • W) = c.re • hpart2 (Hpk k r) W + c.im • hpart1 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> (ring_nf; (try simp only [Complex.I_sq]); (try ring))
def phiL (L : Mx k r →L[ℝ] ℂ) (g : Mx k r) : Mx k r →ₗ[ℂ] ℂ where
  toFun W := L (g * hpart1 (Hpk k r) W) + Complex.I * L (g * hpart2 (Hpk k r) W)
  map_add' A B := by
    simp only [hpart1_add, hpart2_add, Matrix.mul_add, map_add]
    ring
  map_smul' c W := by
    simp only [RingHom.id_apply, smul_eq_mul, hpart1_smul, hpart2_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.mul_smul, map_sub, map_add, map_smul, Complex.real_smul]
    set L1 := L (g * hpart1 (Hpk k r) W)
    set L2 := L (g * hpart2 (Hpk k r) W)
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    linear_combination (-((c.im : ℂ) * L2)) * Complex.I_sq
end HermitianAdjointLemmas
end PI.QnHermHaar


