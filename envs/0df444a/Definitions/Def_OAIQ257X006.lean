-- Prove2me | Definitions.Def_OAIQ257X006
-- name    : OAIQ257X006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:49:50.086366+00:00
-- url     : https://prove2.me/theorems/4febaf6e-f553-4123-9b0a-47029980725d
-- title:
--   Definitions bundle OAIQ257X006 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 61 definitions and 66 theorems. The definitions and types are `OAI.AtomicTriangular.Analysis.dampedEntireSchwartz`, `OAI.AtomicTriangular.Analysis.gaussianSchwartz`, `OAI.AtomicTriangular.Construction.AallKernel`, `OAI.AtomicTriangular.Construction.AallOperator`, `OAI.AtomicTriangular.Construction.Akernel`, `OAI.AtomicTriangular.Construction.Aoperator`, `OAI.AtomicTriangular.Construction.Boperator`, `OAI.AtomicTriangular.Construction.CallKernel`, `OAI.AtomicTriangular.Construction.CallOperator`, `OAI.AtomicTriangular.Construction.Coperator`, `OAI.AtomicTriangular.Construction.Doperator`, `OAI.AtomicTriangular.Construction.FiniteCoefficients`, `OAI.AtomicTriangular.Construction.Lminus`, `OAI.AtomicTriangular.Construction.Lplus`, `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients`, `OAI.AtomicTriangular.Construction.actualFiniteError`, `OAI.AtomicTriangular.Construction.actualFiniteSplit`, `OAI.AtomicTriangular.Construction.actualInput`, `OAI.AtomicTriangular.Construction.actualSchwartz`, `OAI.AtomicTriangular.Construction.actualTail`, `OAI.AtomicTriangular.Construction.actualTailSplit`, `OAI.AtomicTriangular.Construction.actualTrigonometric`, `OAI.AtomicTriangular.Construction.approximationTailResidual`, `OAI.AtomicTriangular.Construction.coefficientInput`, `OAI.AtomicTriangular.Construction.complexInputSchwartz`, `OAI.AtomicTriangular.Construction.correctionFinite`, `OAI.AtomicTriangular.Construction.correctionTail`, `OAI.AtomicTriangular.Construction.extendFiniteError`, `OAI.AtomicTriangular.Construction.finiteApprox`, `OAI.AtomicTriangular.Construction.finiteResidual`, `OAI.AtomicTriangular.Construction.gaussianTarget`, `OAI.AtomicTriangular.Construction.inputSchwartz`, `OAI.AtomicTriangular.Construction.otherSide`, `OAI.AtomicTriangular.Construction.pairSchwartz`, `OAI.AtomicTriangular.Construction.repetitionEntry`, `OAI.AtomicTriangular.Construction.repetitionEnvelope`, `OAI.AtomicTriangular.Construction.repetitionKernel`, `OAI.AtomicTriangular.Construction.repetitionNorm`, `OAI.AtomicTriangular.Construction.repetitionRatio` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_MatrixNorm`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualCorrection`, `Triangular_Construction_ActualInput`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_L1Kernel`, `Triangular_Construction_L1Matrix`, `Triangular_Construction_Normalization`, `Triangular_Construction_Repetition`, `Triangular_Construction_RepetitionOperators`, `Triangular_Construction_Schur`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_Gaussian`, `Triangular_Schwartz_Realness`, `Triangular_Schwartz_Regularity`, `Triangular_Taylor_Taylor`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ257X002` and `OAIQ257X004` of this split; the published statements `OAI.AtomicTriangular.Construction.Bkernel_bound_x`, `OAI.AtomicTriangular.Construction.Ckernel_bound_x`, `OAI.AtomicTriangular.Construction.Ckernel_summable_x`, `OAI.AtomicTriangular.Construction.Dkernel_bound_x`, `OAI.AtomicTriangular.Construction.Dkernel_summable_x`, `OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x` and `OAI.AtomicTriangular.Construction.tail_finite_column_bound_x`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ257X008`, `OAIQ257X028` and `OAIQ257X032`; the statements `OAI.AtomicTriangular.Construction.actualFiniteError_norm_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_radial_x`, `OAI.AtomicTriangular.Construction.actualTail_full_equations_x`, `OAI.AtomicTriangular.Construction.actualTail_norm_x`, `OAI.AtomicTriangular.Construction.actualTrigonometric_norm_x`, `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_x` and `OAI.AtomicTriangular.FiniteCertificate.minusInverse_bound_x`; the proofs of `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_x` and `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X002
import Definitions.Def_OAIQ257X004
import Theorems.Thm_OAI_AtomicTriangular_Construction_Bkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_summable_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_summable_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_finite_column_bound_x

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_MatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.MatrixBounds
def colNorm {m n : Type*} [Fintype m] (A : Matrix m n ℝ) (j : n) : ℝ := ∑ i, |A i j|
def matNorm {m n : Type*} [Fintype m] [Fintype n] [Nonempty n] (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' (by classical exact Finset.univ_nonempty) (colNorm A)

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma colNorm_le_matNorm [Nonempty n] (A : Matrix m n ℝ) (j : n) :
    colNorm A j ≤ matNorm A := by
  classical
  exact Finset.le_sup' (f := colNorm A) (Finset.mem_univ j)

end AtomicTriangular.MatrixBounds

end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction

def rootProduct (s : ℂ) : ℂ := ∏ a : Fin 15, sineFactor a s

theorem P_eq_square (s : ℂ) : P s = rootProduct s ^ 2 := by
  simp only [P, rootProduct, Finset.prod_pow]

theorem differentiable_rootProduct : Differentiable ℂ rootProduct := by
  unfold rootProduct sineFactor
  fun_prop

theorem differentiable_P : Differentiable ℂ P := by
  unfold P sineFactor
  fun_prop

theorem rootProduct_node (n : Node) : rootProduct n.val = 0 := by
  obtain ⟨a,ha⟩ := node_residue n
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hn : (n.val : ℂ) - residue a = 36 * (n.val / 36 : ℤ) := by
    have hh := Int.emod_add_mul_ediv n.val 36
    rw [ha] at hh
    have hc := congrArg (fun x : ℤ => (x : ℂ)) hh
    push_cast at hc
    linear_combination -hc
  unfold sineFactor
  rw [hn]
  have he : (kappa : ℂ) * (36 * (n.val / 36 : ℤ)) =
      (n.val / 36 : ℤ) * (Real.pi : ℂ) := by
    unfold kappa
    push_cast
    ring
  rw [he]
  have hz := congrArg Complex.ofReal (Real.sin_int_mul_pi (n.val / 36))
  have hh : Complex.sin ((n.val / 36 : ℤ) * (Real.pi : ℂ)) = 0 := by
    simpa only [Complex.ofReal_zero, Complex.ofReal_sin, Complex.ofReal_mul,
      Complex.ofReal_intCast] using hz
  rw [hh, mul_zero]

theorem P_node (n : Node) : P n.val = 0 := by
  rw [P_eq_square, rootProduct_node]
  norm_num

theorem hasDerivAt_P_node (n : Node) : HasDerivAt P 0 (n.val : ℂ) := by
  have hh := (differentiable_rootProduct (n.val : ℂ)).hasDerivAt.pow 2
  have he : (rootProduct ^ 2) = P := funext fun s => (P_eq_square s).symm
  simpa [he, rootProduct_node] using hh

theorem deriv_P_node (n : Node) : deriv P n.val = 0 := (hasDerivAt_P_node n).deriv

theorem differentiable_dBasis (n : Node) : Differentiable ℂ (dBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    differentiable_P.differentiableOn

theorem differentiable_cBasis (n : Node) : Differentiable ℂ (cBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    (differentiable_dBasis n).differentiableOn

theorem dBasis_node (n : Node) : dBasis n n.val = 0 := by
  simp [dBasis, dslope_same, deriv_P_node]

theorem dBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    dBasis n s = P s / (s-n.val) := by
  simp [dBasis, dslope_of_ne _ hs, slope_def_field, P_node]

theorem cBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    cBasis n s = P s / (s-n.val)^2 := by
  rw [cBasis, dslope_of_ne _ hs, slope_def_field, dBasis_node,
    sub_zero, dBasis_eq n hs, div_div, pow_two]

theorem differentiable_finiteC (a : Fin 15) : Differentiable ℂ (finiteC a) := by
  unfold finiteC sineFactor
  fun_prop

theorem differentiable_finiteD (a : Fin 15) : Differentiable ℂ (finiteD a) := by
  unfold finiteD sineFactor
  fun_prop

open Polynomial

theorem finiteC_spectral (a : Fin 15) (s : ℂ) :
    finiteC a s = phase (-s)^14 * (cAtomPolynomial a).eval (phase s) := by
  unfold finiteC cAtomPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hp : (∏ r ∈ Finset.univ.erase a, sineFactor r s ^ 2) =
      phase (-s)^14 * ∏ r ∈ Finset.univ.erase a, (atomFactor r).eval (phase s) := by
    calc
      _ = ∏ r ∈ Finset.univ.erase a, phase (-s) * (atomFactor r).eval (phase s) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact (eval_atomFactor r s).symm
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hp]
  ring

theorem finiteD_factor (a : Fin 15) (s : ℂ) :
    2 * (kappa : ℂ) * sineFactor a s *
      Complex.cos ((kappa : ℂ) * (s - (residue a : ℂ))) =
    Complex.I * (kappa : ℂ) *
      (phase ((residue a : ℂ)-s)-phase (s-(residue a : ℂ))) := by
  let z : ℂ := (kappa : ℂ) * (s-(residue a : ℂ))
  have hpos : phase (s-(residue a : ℂ)) = Complex.exp ((2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  have hneg : phase ((residue a : ℂ)-s) = Complex.exp (-(2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  rw [hpos,hneg]
  change 2 * (kappa : ℂ) * (2 * Complex.sin z) * Complex.cos z = _
  have hs := Complex.two_sin (2*z)
  rw [Complex.sin_two_mul] at hs
  linear_combination (kappa : ℂ)*hs

theorem rest_spectral (a : Fin 15) (s : ℂ) :
    (∏ r ∈ Finset.univ.erase a, sineFactor r s ^ 2) =
      phase (-s)^14 * ∏ r ∈ Finset.univ.erase a, (atomFactor r).eval (phase s) := by
  calc
    _ = ∏ r ∈ Finset.univ.erase a, phase (-s) * (atomFactor r).eval (phase s) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact (eval_atomFactor r s).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem finiteD_spectral (a : Fin 15) (s : ℂ) :
    finiteD a s = phase (-s)^15 * (dAtomPolynomial a).eval (phase s) := by
  unfold finiteD dAtomPolynomial
  rw [finiteD_factor a s, rest_spectral a s]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  have hh : phase (-s) *
      (phase (residue a) - phase (-residue a) * phase s^2) =
      phase ((residue a : ℂ)-s) - phase (s-(residue a : ℂ)) := by
    have h1 : phase (-s) * phase (residue a) = phase ((residue a : ℂ)-s) := by
      rw [← phase_add]
      congr 1
      ring
    have h2 : phase (-residue a) * phase s = phase (s-(residue a : ℂ)) := by
      rw [← phase_add]
      congr 1
      ring
    have h0 := phase_neg_mul s
    linear_combination h1 - phase (-residue a) * phase s * h0 - h2
  rw [← hh]
  ring

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

lemma restPolynomial_degree (a : Fin 15) : (restPolynomial a).natDegree ≤ 28 := by
  unfold restPolynomial
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  calc
    ∑ r ∈ Finset.univ.erase a, (atomFactor r).natDegree ≤
        ∑ r ∈ Finset.univ.erase a, 2 := Finset.sum_le_sum (fun r _ => atomFactor_degree r)
    _ = 28 := by simp

lemma cShift_degree (a : Fin 15) : (cShiftPolynomial a).natDegree ≤ 30 := by
  have hr := restPolynomial_degree a
  change (X * (C (4*(kappa:ℂ)^2) * restPolynomial a)).natDegree ≤ 30
  calc
    _ ≤ X.natDegree + (C (4*(kappa:ℂ)^2) * restPolynomial a).natDegree := natDegree_mul_le
    _ ≤ 1 + 28 := add_le_add (by simp) ((natDegree_C_mul_le _ _).trans hr)
    _ ≤ 30 := by norm_num

lemma dAtom_degree (a : Fin 15) : (dAtomPolynomial a).natDegree ≤ 30 := by
  have hr := restPolynomial_degree a
  have hf : (C (I*(kappa:ℂ)) *
    (C (phase (residue a)) - C (phase (-(residue a:ℂ))) * X^2)).natDegree ≤ 2 := by
    compute_degree!
  exact (natDegree_mul_le).trans (add_le_add hf hr)

lemma polynomial_fourier {p : Polynomial ℂ} (hp : p.natDegree ≤ 30) (s : ℂ) :
    phase (-s)^15 * p.eval (phase s) =
      ∑ j : Fin 31, p.coeff j.val * exp (I*Real.pi*frequency j*s) := by
  rw [Polynomial.eval_eq_sum_range' (n:=31) (by omega)]
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, phase_offset]

lemma finiteC_fourier (a : Fin 15) (s : ℂ) : finiteC a s =
    ∑ j : Fin 31, cCoefficient a j * exp (I*Real.pi*frequency j*s) := by
  change finiteC a s = ∑ j : Fin 31, (cShiftPolynomial a).coeff j.val * _
  rw [← polynomial_fourier (cShift_degree a) s, finiteC_spectral]
  simp only [cShiftPolynomial, eval_mul, eval_X]
  have hp := phase_neg_mul s
  have he : phase (-s)^15 * phase s = phase (-s)^14 := by
    nth_rw 1 [show 15=14+1 by norm_num]
    rw [pow_succ, mul_assoc, hp, mul_one]
  rw [← mul_assoc, he]

lemma finiteD_fourier (a : Fin 15) (s : ℂ) : finiteD a s =
    ∑ j : Fin 31, dCoefficient a j * exp (I*Real.pi*frequency j*s) := by
  rw [finiteD_spectral, polynomial_fourier (dAtom_degree a)]
  rfl

end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology lp
namespace AtomicTriangular.L1Kernel
variable {α β : Type*}

lemma l1_norm (a : ℓ¹(α,ℝ)) : ‖a‖ = ∑' i, |a i| := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs] using
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ENNReal).toReal) a
lemma l1_summable (a : ℓ¹(α,ℝ)) : Summable (fun i => |a i|) := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using
    a.property.summable (by norm_num : 0 < (1:ENNReal).toReal)

def column (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) : ℓ¹(β,ℝ) :=
  ⟨fun i => K i j, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using hK j⟩
lemma column_norm (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) :
    ‖column K hK j‖ = ∑' i, |K i j| := l1_norm _

variable (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|))
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ j, ∑' i, |K i j| ≤ C)
include C hB
lemma summable_columns (a : ℓ¹(α,ℝ)) :
    Summable (fun j => a j • column K hK j) := by
  apply Summable.of_norm_bounded ((l1_summable a).mul_right C)
  intro j
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _)

omit C hB in
def applyKernel (a : ℓ¹(α,ℝ)) : ℓ¹(β,ℝ) := ∑' j, a j • column K hK j
lemma applyKernel_norm (a : ℓ¹(α,ℝ)) : ‖applyKernel K hK a‖ ≤ C*‖a‖ := by
  have hs : Summable (fun j => ‖a j • column K hK j‖) :=
    ((l1_summable a).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
  calc
    _ ≤ ∑' j, ‖a j • column K hK j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j, |a j| * C := hs.tsum_le_tsum (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
      ((l1_summable a).mul_right C)
    _ = C*‖a‖ := by rw [tsum_mul_right,l1_norm,mul_comm]

lemma applyKernel_add (a b : ℓ¹(α,ℝ)) :
    applyKernel K hK (a+b) = applyKernel K hK a + applyKernel K hK b := by
  simp only [applyKernel,lp.coeFn_add,Pi.add_apply,add_smul]
  exact (summable_columns K hK C hB a).tsum_add (summable_columns K hK C hB b)
lemma applyKernel_smul (r : ℝ) (a : ℓ¹(α,ℝ)) :
    applyKernel K hK (r • a) = r • applyKernel K hK a := by
  simp only [applyKernel,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
  exact (summable_columns K hK C hB a).tsum_const_smul r

def operator : ℓ¹(α,ℝ) →L[ℝ] ℓ¹(β,ℝ) :=
  LinearMap.mkContinuous
    { toFun := applyKernel K hK
      map_add' := applyKernel_add K hK C hB
      map_smul' := fun r a => applyKernel_smul K hK C hB r a }
    C (applyKernel_norm K hK C hB)
end AtomicTriangular.L1Kernel
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
def l1Matrix (A : Matrix m n ℝ) : ℓ¹(n,ℝ) →L[ℝ] ℓ¹(m,ℝ) :=
  operator A (fun j => (hasSum_fintype _).summable) (matNorm A)
    (fun j => by simpa [tsum_fintype,colNorm] using colNorm_le_matNorm A j)
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
abbrev FiniteCoefficients := ℓ¹(Fin 20,ℝ)
abbrev TailCoefficients := ℓ¹(TailNode × Fin 2,ℝ)
def Boperator : TailCoefficients →L[ℝ] FiniteCoefficients :=
  operator Bkernel (fun _ => (hasSum_fintype _).summable) 335 Bkernel_bound_x
def Coperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Ckernel Ckernel_summable_x (7/10^15) Ckernel_bound_x
def Doperator : TailCoefficients →L[ℝ] TailCoefficients :=
  operator Dkernel Dkernel_summable_x (23/10^9) Dkernel_bound_x
def tailFixedColumn (c : Fin 23) : TailCoefficients :=
  column (fun p (_ : Unit) => jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c))
    (fun _ => by
      by_cases hc : c.val=22
      · have hh := (tail_atom_column_bounds_x 0 0 (finiteColumn c)).1
        simpa [hc,damping] using hh
      · have hh := (tail_atom_column_bounds_x 1 0 (finiteColumn c)).1
        simpa [hc,damping] using hh) ()
def Lplus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1-R)⁻¹
def Lminus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1+R)⁻¹
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Repetition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma pi_eta_pos : 0<Real.pi*eta := mul_pos Real.pi_pos (by norm_num [eta])
def repetitionRatio : ℝ := Real.exp (-36*Real.pi*eta)
def repetitionNorm : ℝ := (1+Real.pi*eta)*repetitionRatio/(1-repetitionRatio)
lemma repetitionRatio_pos : 0 < repetitionRatio := Real.exp_pos _
lemma repetitionRatio_lt : repetitionRatio<1 := by
  rw [repetitionRatio,Real.exp_lt_one_iff]
  nlinarith [pi_eta_pos]

def repetitionEnvelope (a : Fin 11) (n : TailNode) : ℝ :=
  if n.val.val%36=residue ⟨a.val,by omega⟩ then
    (1+Real.pi*eta)*Real.exp (-Real.pi*eta*n.val.val) else 0
lemma repetitionEnvelope_nonneg (a : Fin 11) (n : TailNode) : 0 ≤ repetitionEnvelope a n := by
  unfold repetitionEnvelope
  split_ifs
  · exact mul_nonneg (by linarith [pi_eta_pos]) (Real.exp_pos _).le
  · rfl
lemma repetitionEnvelope_enumerate (a : Fin 11) (r : Fin 15) (l : ℕ) :
    repetitionEnvelope a (enumerateTail (r,l)) =
      if r=⟨a.val,by omega⟩ then
        (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase r)*repetitionRatio^l else 0 := by
  have hm : (enumerateTail (r,l)).val.val%36=residue r := by
    change (tailBase r+36*(l:ℤ))%36=residue r
    simp [Int.add_emod,tailBase_mod,residue_mod]
  unfold repetitionEnvelope
  simp only [hm,residue_injective.eq_iff]
  split_ifs
  · change _ * Real.exp (-Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ)) = _
    rw [show -Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ) =
      -Real.pi*eta*(tailBase r:ℝ)+(l:ℝ)*(-36*Real.pi*eta) by push_cast; ring,
      Real.exp_add,Real.exp_nat_mul]
    simp only [repetitionRatio] <;> ring
  · rfl
lemma summable_repetitionEnvelope (a : Fin 11) : Summable (repetitionEnvelope a) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => repetitionEnvelope_nonneg a _)).mpr
  refine ⟨fun r => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => repetitionEnvelope a (enumerateTail (r,l)))
  simp_rw [repetitionEnvelope_enumerate]
  split_ifs
  · exact (summable_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt).mul_left _
  · exact summable_zero
lemma tsum_repetitionEnvelope (a : Fin 11) :
    (∑' n, repetitionEnvelope a n) =
      (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase ⟨a.val,by omega⟩)/(1-repetitionRatio) := by
  rw [← tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_repetitionEnvelope a)
  change Summable (fun p : Fin 15 × ℕ => repetitionEnvelope a (enumerateTail p)) at hs
  change (∑' p : Fin 15 × ℕ, repetitionEnvelope a (enumerateTail p)) = _
  rw [hs.tsum_prod,tsum_fintype]
  simp_rw [repetitionEnvelope_enumerate]
  have hi (P : Prop) [Decidable P] (f : ℕ → ℝ) :
      (∑' l, if P then f l else 0) = if P then ∑' l, f l else 0 := by
    by_cases hh : P <;> simp [hh]
  simp_rw [hi]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,tsum_mul_left,
    tsum_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt,div_eq_mul_inv]
lemma repetitionEnvelope_bound (a : Fin 11) : (∑' n, repetitionEnvelope a n) ≤ repetitionNorm := by
  rw [tsum_repetitionEnvelope]
  have ht : 36 ≤ tailBase ⟨a.val,by omega⟩ := by revert a; decide +kernel
  have he : Real.exp (-Real.pi*eta*(tailBase ⟨a.val,by omega⟩:ℝ)) ≤ repetitionRatio := by
    unfold repetitionRatio
    apply Real.exp_le_exp.mpr
    have ht' : (36:ℝ) ≤ (tailBase ⟨a.val,by omega⟩:ℝ) := by exact_mod_cast ht
    nlinarith [pi_eta_pos]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr repetitionRatio_lt).le
  exact mul_le_mul_of_nonneg_left he (by linarith [pi_eta_pos])

def repetitionEntry (c d : Fin 2) : ℝ :=
  if c.val=0 then if d.val=0 then 1 else -Real.pi*eta
  else if d.val=0 then 0 else 1
lemma repetitionEntry_bound (c : Fin 2) : (∑ d : Fin 2, |repetitionEntry c d|) ≤ 1+Real.pi*eta := by
  fin_cases c <;> norm_num [Fin.sum_univ_succ,repetitionEntry,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num [eta] : 0<eta)]
  exact pi_eta_pos.le
def repetitionKernel (p : TailNode × Fin 2) (a : Fin 11) (c : Fin 2) : ℝ :=
  if p.1.val.val%36=residue ⟨a.val,by omega⟩ then
    Real.exp (-Real.pi*eta*p.1.val.val)*repetitionEntry c p.2 else 0
lemma repetitionKernel_pair (a : Fin 11) (c : Fin 2) (n : TailNode) :
    (∑ d : Fin 2, |repetitionKernel (n,d) a c|) ≤ repetitionEnvelope a n := by
  unfold repetitionKernel repetitionEnvelope
  split_ifs with hh
  · simp only [abs_mul,abs_of_pos (Real.exp_pos _),←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (repetitionEntry_bound c) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · simp
lemma repetitionKernel_bounds (a : Fin 11) (c : Fin 2) :
    Summable (fun p => |repetitionKernel p a c|) ∧
      (∑' p, |repetitionKernel p a c|) ≤ repetitionNorm := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun n d => repetitionKernel (n,d) a c)
    (repetitionEnvelope a) (summable_repetitionEnvelope a) (repetitionKernel_pair a c)
  exact ⟨hs,hb.trans (repetitionEnvelope_bound a)⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
abbrev TrigonometricCoefficients := ℓ¹(Fin 22,ℝ)
def AallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  repetitionKernel p ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩
def AallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator AallKernel (fun _ => (repetitionKernel_bounds _ _).1) repetitionNorm
    (fun _ => (repetitionKernel_bounds _ _).2)
def Akernel (p : TailNode × Fin 2) (i : Fin 20) : ℝ :=
  repetitionKernel p ⟨i.val/2+1,by omega⟩ ⟨i.val%2,by omega⟩
def Aoperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Akernel (fun _ => (repetitionKernel_bounds _ _).1) repetitionNorm
    (fun _ => (repetitionKernel_bounds _ _).2)
def CallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val,by omega⟩)
def CallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator CallKernel (fun _ => (tail_atom_column_bounds_x 1 0 _).1) (7/10^15)
    (fun i => (tail_finite_column_bound_x i).le)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

def gaussianTarget (v z : ℝ) (n : ℤ) (d : Fin 2) : ℝ :=
  Q 1/Q n * Real.exp (Real.pi*(v-h)*n+(1-n)/z) *
    (if d.val=0 then z else -1+(Real.pi*(v-h)-D n)*z)
def targetEnvelope (v : ℝ) (n : ℤ) : ℝ :=
  Q 1/Q n * (1+Z+Z*|Real.pi*(v-h)-D n|) *
    Real.exp (Real.pi*(v-h)*n+(1-n)/Z)
lemma Q_one_pos : 0<Q 1 := by linarith [Q_1_bounds.1]
lemma targetEnvelope_nonneg (v : ℝ) (n : Node) : 0≤targetEnvelope v n.val := by
  have hn : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  unfold targetEnvelope
  exact mul_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hn.le) (by positivity)) (Real.exp_pos _).le
lemma gaussianTarget_pair_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) (v : ℝ)
    (n : Node) (hn : 1≤n.val) :
    (∑ d : Fin 2, |gaussianTarget v z n.val d|) ≤ targetEnvelope v n.val := by
  have hQ : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  have hn' : 0≤(n.val:ℝ)-1 := by
    have hi : (1:ℝ)≤(n.val:ℝ) := by exact_mod_cast hn
    linarith
  have he : Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) ≤
      Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left hn' hz hzB
    have hnz : (1-(n.val:ℝ))/z = -(((n.val:ℝ)-1)/z) := by ring
    have hnZ : (1-(n.val:ℝ))/Z = -(((n.val:ℝ)-1)/Z) := by ring
    rw [hnz,hnZ]
    linarith
  have hb : z+|-1+(Real.pi*(v-h)-D n.val)*z| ≤ 1+Z+Z*|Real.pi*(v-h)-D n.val| := by
    have ha := abs_add_le (-1:ℝ) ((Real.pi*(v-h)-D n.val)*z)
    rw [abs_mul,abs_of_pos hz] at ha
    norm_num at ha
    have hm := mul_le_mul_of_nonneg_left hzB (abs_nonneg (Real.pi*(v-h)-D n.val))
    linarith
  have hp : 0≤Q 1/Q n.val := div_nonneg Q_one_pos.le hQ.le
  simp only [Fin.sum_univ_succ,gaussianTarget,Fin.val_zero,Fin.val_succ,Fin.isValue,
    ↓reduceIte,Nat.one_ne_zero,Nat.reduceAdd,abs_mul,abs_of_nonneg hp,abs_of_pos (Real.exp_pos _),abs_of_pos hz]
  unfold targetEnvelope
  calc
    _ = (Q 1/Q n.val)*(z+|-1+(Real.pi*(v-h)-D n.val)*z|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) := by ring
    _ ≤ (Q 1/Q n.val)*(1+Z+Z*|Real.pi*(v-h)-D n.val|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb hp) he (Real.exp_pos _).le
        (by positivity)
lemma targetEnvelope_enumerate (a : Fin 15) (l : ℕ) :
    targetEnvelope h (enumerateTail (a,l)).val.val =
      targetEnvelope h (tailBase a)*(Real.exp (-36/Z))^l := by
  unfold targetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  simp only [sub_self,mul_zero,zero_mul,zero_add,zero_sub,abs_neg]
  change _ * Real.exp ((1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z) = _
  rw [show (1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z =
    (1-(tailBase a:ℝ))/Z+(l:ℝ)*(-36/Z) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma targetRatio_lt : Real.exp (-36/Z)<1 := by
  rw [Real.exp_lt_one_iff]; norm_num [Z]
lemma summable_targetEnvelope : Summable (fun n : TailNode => targetEnvelope h n.val.val) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => targetEnvelope_nonneg h (enumerateTail p).val)).mpr
  refine ⟨fun a => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => targetEnvelope h (enumerateTail (a,l)).val.val)
  simp_rw [targetEnvelope_enumerate]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt).mul_left _
def tailTargetEnvelope : ℝ := (∑ a : Fin 15, targetEnvelope h (tailBase a))/(1-Real.exp (-36/Z))
lemma tsum_targetEnvelope : (∑' n : TailNode, targetEnvelope h n.val.val)=tailTargetEnvelope := by
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr summable_targetEnvelope
  change Summable (fun p : Fin 15 × ℕ => targetEnvelope h (enumerateTail p).val.val) at hs
  change (∑' p : Fin 15 × ℕ, targetEnvelope h (enumerateTail p).val.val)=_
  rw [hs.tsum_prod]
  simp_rw [targetEnvelope_enumerate,tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
lemma tailTarget_bounds {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    Summable (fun p : TailNode × Fin 2 => |gaussianTarget h z p.1.val.val p.2|) ∧
      (∑' p : TailNode × Fin 2, |gaussianTarget h z p.1.val.val p.2|) ≤ tailTargetEnvelope := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun (n : TailNode) d => gaussianTarget h z n.val.val d)
    (fun n => targetEnvelope h n.val.val) summable_targetEnvelope
    (fun n => gaussianTarget_pair_bound hz hzB h n.val (by have := n.val.property.1; omega))
  exact ⟨hs,hb.trans_eq tsum_targetEnvelope⟩
def tailTarget (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℓ¹(TailNode × Fin 2,ℝ) :=
  column (fun p (_ : Unit) => gaussianTarget h z p.1.val.val p.2)
    (fun _ => (tailTarget_bounds hz hzB).1) ()
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def neumann (T : F →L[ℝ] F) : F →L[ℝ] F := ∑' n : ℕ, T^n

def tailOperator (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) : F →L[ℝ] F := D+K.comp (L.comp B)
def tailSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : F :=
  neumann (tailOperator L B K D) (s+K (L r))
def finiteSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : E :=
  L (r+B (tailSolution L B K D r s))
end AtomicTriangular.Schur
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitL (e : Fin 2) : FiniteCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Lplus else Lminus
def splitB (e : Fin 2) : TailCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Boperator else -Boperator
def splitK (e : Fin 2) : FiniteCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Coperator-Aoperator else -Coperator-Aoperator
def splitD (e : Fin 2) : TailCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Doperator else -Doperator

def correctionTail (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : TailCoefficients :=
  tailSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
def correctionFinite (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : FiniteCoefficients :=
  AtomicTriangular.Schur.finiteSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

def finiteResidual (z : ℝ) : FiniteCoefficients :=
  column (fun i (_ : Unit) => if i.val<8 then 0 else
    gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩)
    (fun _ => (hasSum_fintype _).summable) ()

def finiteApprox (side : Fin 2) (e : Fin 8 → ℝ) : TrigonometricCoefficients :=
  column (fun i (_ : Unit) => ∑ j : Fin 8, Acoefficient side ⟨i.val,by omega⟩ j*e j)
    (fun _ => (hasSum_fintype _).summable) ()

def approximationTailResidual (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  tailTarget z hz hzB +
  (if e.val=0 then CallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z))
    else CallOperator (finiteApprox 1 (actualParameter z)-finiteApprox 0 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)-finiteApprox 1 (actualParameter z)) +
      (12/1000:ℝ) • tailFixedColumn 22)

def actualTailSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  correctionTail e (finiteResidual z) (approximationTailResidual e z hz hzB)
def actualFiniteSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  correctionFinite e (finiteResidual z) (approximationTailResidual e z hz hzB)

def actualTail (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  (1/2:ℝ) • (actualTailSplit 0 z hz hzB + (if side.val=0 then actualTailSplit 1 z hz hzB else -actualTailSplit 1 z hz hzB))
def actualFiniteError (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  (1/2:ℝ) • (actualFiniteSplit 0 z hz hzB + (if side.val=0 then actualFiniteSplit 1 z hz hzB else -actualFiniteSplit 1 z hz hzB))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma tail_pairs_summable (w : TailCoefficients) :
    Summable (fun n => |w (n,0)|+|w (n,1)|) := by
  have hh := (l1_summable w).prod
  simpa [tsum_fintype,Fin.sum_univ_succ] using hh

def coefficientInput (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) : InputCoefficients where
  C := C
  finiteC j := a ⟨2*j.val,by omega⟩
  finiteD j := a ⟨2*j.val+1,by omega⟩
  tailC n := w (n,0)
  tailD n := w (n,1)
  summable := tail_pairs_summable w

def extendFiniteError (u : FiniteCoefficients) : TrigonometricCoefficients :=
  column (fun i (_ : Unit) => if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)
    (fun _ => (hasSum_fintype _).summable) ()

def actualTrigonometric (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TrigonometricCoefficients :=
  finiteApprox side (actualParameter z)+extendFiniteError (actualFiniteError side z hz hzB)
def actualInput (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : InputCoefficients :=
  coefficientInput (if side.val=0 then -(3/500) else 3/500)
    (actualTrigonometric side z hz hzB) (actualTail side z hz hzB)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

lemma polynomial_gaussian_bound {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (1+r)^m * Real.exp (-c*r^2) ≤ C := by
  let B : ℝ := 2+c⁻¹
  refine ⟨B^m*(m.factorial:ℝ)*Real.exp 1, by positivity, ?_⟩
  intro r hr
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have h : 1+r ≤ B*(1+c*r^2) := by
    dsimp [B]
    have hsq := sq_nonneg (r-1)
    have hmul : c⁻¹*c=1 := inv_mul_cancel₀ hc.ne'
    nlinarith [sq_nonneg r, mul_nonneg hc.le (sq_nonneg r)]
  have hp : (1+c*r^2)^m ≤ (m.factorial:ℝ)*Real.exp (1+c*r^2) := by
    have hh := Real.pow_div_factorial_le_exp (1+c*r^2) (by positivity : 0 ≤ 1+c*r^2) m
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))).mp hh |>.trans_eq (mul_comm _ _)
  calc
    (1+r)^m * Real.exp (-c*r^2) ≤ (B*(1+c*r^2))^m * Real.exp (-c*r^2) := by gcongr
    _ = B^m * ((1+c*r^2)^m * Real.exp (-c*r^2)) := by rw [mul_pow]; ring
    _ ≤ B^m * (((m.factorial:ℝ)*Real.exp (1+c*r^2))*Real.exp (-c*r^2)) := by gcongr
    _ = B^m*(m.factorial:ℝ)*Real.exp 1 := by
      rw [mul_assoc (m.factorial:ℝ), ← Real.exp_add]
      rw [show 1+c*r^2 + -c*r^2 = 1 by ring]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gaussian_schwartz_decay {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖^k * ‖iteratedFDeriv ℝ n (fun y : E => Real.exp (-c*‖y‖^2)) x‖ ≤ C := by
  have ht : (fun x : E => -c*‖x‖^2).HasTemperateGrowth := by fun_prop
  obtain ⟨l,B,hB,hder⟩ := ht.norm_iteratedFDeriv_le_uniform n
  obtain ⟨C,hC,hCbound⟩ := polynomial_gaussian_bound hc (k+l*n)
  refine ⟨(n.factorial:ℝ)*(B+1)^n*C, fun x => ?_⟩
  have hw : 1 ≤ (B+1)*(1+‖x‖)^l := by
    have hh : 1 ≤ (1+‖x‖)^l := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun x : E => -c*‖x‖^2) x‖ ≤ ((B+1)*(1+‖x‖)^l)^i := by
    calc
      _ ≤ B*(1+‖x‖)^l := hder i hin x
      _ ≤ (B+1)*(1+‖x‖)^l := by gcongr; linarith
      _ ≤ ((B+1)*(1+‖x‖)^l)^i := le_self_pow₀ hw (by omega)
  have hexp (i : ℕ) (_hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Real.exp (-c*‖x‖^2)‖ ≤ Real.exp (-c*‖x‖^2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp]
    exact le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp ht.1 (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) x hexp hD
  calc
    _ ≤ ‖x‖^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (1+‖x‖)^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) := by gcongr; linarith
    _ = (n.factorial:ℝ)*(B+1)^n*((1+‖x‖)^(k+l*n)*Real.exp (-c*‖x‖^2)) := by
      rw [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ (n.factorial:ℝ)*(B+1)^n*C := by gcongr; exact hCbound ‖x‖ (norm_nonneg _)

def gaussianSchwartz (c : ℝ) (hc : 0 < c) : 𝓢(E,ℝ) where
  toFun x := Real.exp (-c*‖x‖^2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' := gaussian_schwartz_decay hc

@[simp] lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := rfl

def dampedEntireSchwartz (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (_hf : Differentiable ℂ f) (_hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) : 𝓢(E,ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : E => (f (b*‖x‖^2)).re) (gaussianSchwartz c hc)

end AtomicTriangular.Analysis
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma norm_two_sin_le (z : ℂ) : ‖2 * sin z‖ ≤ 2 * Real.exp |z.im| := by
  rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  calc
    ‖exp (-z * I) - exp (z * I)‖ ≤ ‖exp (-z * I)‖ + ‖exp (z * I)‖ := norm_sub_le _ _
    _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _))
        (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = 2 * Real.exp |z.im| := by ring

def stripBound (R : ℝ) : ℝ := (2 * Real.exp (Real.pi * R / 36))^30

lemma stripBound_nonneg (R : ℝ) : 0 ≤ stripBound R := by unfold stripBound; positivity

lemma P_strip_bound (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) : ‖P s‖ ≤ stripBound R := by
  unfold P sineFactor
  rw [norm_prod]
  calc
    ∏ a : Fin 15, ‖(2 * sin ((kappa : ℂ) * (s-residue a)))^2‖ ≤
        ∏ _a : Fin 15, (2 * Real.exp (Real.pi * R / 36))^2 := by
      apply Finset.prod_le_prod (by intros; positivity)
      intro a _
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine (norm_two_sin_le _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have he : (((kappa : ℂ) * (s-residue a))).im = Real.pi * s.im / 36 := by
        simp [kappa, div_eq_mul_inv] <;> ring
      rw [he, abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 36)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (by norm_num)
    _ = stripBound R := by simp [stripBound, ← pow_mul]

lemma im_le_dist_int (w : ℂ) (n : ℤ) : |w.im| ≤ dist w (n : ℂ) := by
  simpa [dist_eq_norm] using Complex.abs_im_le_norm (w - (n : ℂ))

lemma uniform_basis_bound (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M := by
  let A := max R 2
  let M := stripBound A
  have hM : 0 ≤ M := stripBound_nonneg A
  refine ⟨M,hM,?_⟩
  intro n s hs
  have hmapP : Set.MapsTo P (Metric.ball (n.val : ℂ) 2) (Metric.closedBall (P n.val) M) := by
    intro w hw
    simp only [Metric.mem_closedBall, P_node, dist_zero_right]
    exact P_strip_bound A w ((im_le_dist_int w n.val).trans
      ((Metric.mem_ball.mp hw).le.trans (le_max_right _ _)))
  have hd : ∀ w ∈ Metric.ball (n.val : ℂ) 2, ‖dBasis n w‖ ≤ M/2 := by
    intro w hw
    exact Complex.norm_dslope_le_div_of_mapsTo_ball differentiable_P.differentiableOn hmapP hw
  have hmapD : Set.MapsTo (dBasis n) (Metric.ball (n.val : ℂ) 1)
      (Metric.closedBall (dBasis n n.val) (M/2)) := by
    intro w hw
    simp only [Metric.mem_closedBall, dBasis_node, dist_zero_right]
    apply hd w
    exact (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
  have hc : ∀ w ∈ Metric.ball (n.val : ℂ) 1, ‖cBasis n w‖ ≤ M/2 := by
    intro w hw
    simpa [cBasis] using Complex.norm_dslope_le_div_of_mapsTo_ball
      (differentiable_dBasis n).differentiableOn hmapD hw
  have hPs : ‖P s‖ ≤ M := P_strip_bound A s (hs.trans (le_max_left _ _))
  have hhalf : M/2 ≤ M := by linarith
  by_cases hnear : dist s (n.val : ℂ) < 1
  · exact ⟨(hc s hnear).trans hhalf,
      (hd s (lt_trans hnear (by norm_num : (1 : ℝ) < 2))).trans hhalf⟩
  · have hfar : 1 ≤ ‖s - (n.val : ℂ)‖ := by simpa [dist_eq_norm] using le_of_not_gt hnear
    have hne : s ≠ (n.val : ℂ) := by intro he; norm_num [he] at hfar
    rw [cBasis_eq n hne, dBasis_eq n hne, norm_div, norm_div, norm_pow]
    constructor
    · exact (div_le_self (norm_nonneg _) (one_le_pow₀ hfar)).trans hPs
    · exact (div_le_self (norm_nonneg _) hfar).trans hPs

def spectralBound (S : Fin 31 → ℂ) (R : ℝ) : ℝ :=
  ∑ j : Fin 31, ‖S j‖*Real.exp (|Real.pi*frequency j| *R)
lemma finiteSpectral_strip (S : Fin 31 → ℂ) (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖∑ j : Fin 31, S j*exp (I*Real.pi*frequency j*s)‖ ≤ spectralBound S R := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hi : (I*Real.pi*frequency j*s).re = -(Real.pi*frequency j)*s.im := by simp
  rw [hi]
  calc
    -(Real.pi*frequency j)*s.im ≤ |-(Real.pi*frequency j)*s.im| := le_abs_self _
    _ = |Real.pi*frequency j| *|s.im| := by rw [abs_mul,abs_neg]
    _ ≤ |Real.pi*frequency j| *R := mul_le_mul_of_nonneg_left hs (abs_nonneg _)

lemma tail_summand_norm_bound (a : InputCoefficients) {R M : ℝ}
    (hM : ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M)
    (n : TailNode) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖(a.tailC n:ℂ)*cBasis n.val s+(a.tailD n:ℂ)*dBasis n.val s‖ ≤
      (|a.tailC n|+|a.tailD n|)*M := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |a.tailC n| *M+|a.tailD n| *M :=
      add_le_add (mul_le_mul_of_nonneg_left (hM n.val s hs).1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hM n.val s hs).2 (abs_nonneg _))
    _ = _ := by ring

lemma differentiable_tailInput (a : InputCoefficients) : Differentiable ℂ (tailInput a) := by
  intro s
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound (|s.im|+1)
  let U : Set ℂ := {w | |w.im| < |s.im|+1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hs : s ∈ U := by dsimp [U] <;> linarith
  have hd : DifferentiableOn ℂ
      (fun w => ∑' n : TailNode, ((a.tailC n:ℂ)*cBasis n.val w+(a.tailD n:ℂ)*dBasis n.val w)) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (a.summable.mul_right M)
    · intro n
      exact ((differentiable_cBasis n.val).const_mul _ |>.add
        ((differentiable_dBasis n.val).const_mul _)).differentiableOn
    · exact hU
    · intro n w hw
      exact tail_summand_norm_bound a hB n w (le_of_lt hw)
  exact ((differentiable_P s).const_mul _).add (hd.differentiableAt (hU.mem_nhds hs))

lemma tailInput_strip (a : InputCoefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖tailInput a s‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound R
  refine ⟨|a.C| *stripBound R + ∑' n : TailNode, (|a.tailC n|+|a.tailD n|)*M,?_⟩
  intro s hs
  have hsum := (a.summable.mul_right M).of_norm_bounded
    (fun n => tail_summand_norm_bound a hB n s hs)
  unfold tailInput
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (P_strip_bound R s hs) (abs_nonneg a.C)
  · exact (norm_tsum_le_tsum_norm hsum.norm).trans
      (hsum.norm.tsum_le_tsum (fun n => tail_summand_norm_bound a hB n s hs) (a.summable.mul_right M))

lemma differentiable_finiteInput (a : InputCoefficients) : Differentiable ℂ (finiteInput a) := by
  unfold finiteInput
  apply Differentiable.fun_sum
  intro j _
  exact ((differentiable_finiteC _).const_mul _).add ((differentiable_finiteD _).const_mul _)

lemma finiteInput_strip (a : InputCoefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖finiteInput a s‖ ≤ M := by
  refine ⟨∑ j : Fin 11, (|a.finiteC j| *spectralBound (FiniteCertificate.cCoefficient ⟨j.val,by omega⟩) R +
    |a.finiteD j| *spectralBound (FiniteCertificate.dCoefficient ⟨j.val,by omega⟩) R), ?_⟩
  intro s hs
  unfold finiteInput
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [FiniteCertificate.finiteC_fourier,FiniteCertificate.finiteD_fourier]
  exact add_le_add (mul_le_mul_of_nonneg_left (finiteSpectral_strip _ R s hs) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (finiteSpectral_strip _ R s hs) (abs_nonneg _))

def inputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℝ) :=
  Analysis.dampedEntireSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [h])) b_pos) b
    (tailInput a) (differentiable_tailInput a) (tailInput_strip a 1) +
  Analysis.dampedEntireSchwartz (Real.pi*H*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [H])) b_pos) b
    (finiteInput a) (differentiable_finiteInput a) (finiteInput_strip a 1)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

def complexInputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (inputSchwartz a)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

def pairSchwartz (a₁ a₂ : InputCoefficients) : 𝓢(Plane,ℝ) :=
  (complexInputSchwartz a₁ + 𝓕 (complexInputSchwartz a₂)).postcompCLM Complex.reCLM
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def otherSide (i : Fin 2) : Fin 2 := if i.val=0 then 1 else 0

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
def actualSchwartz (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : 𝓢(Plane,ℝ) :=
  (normalizingDen z)⁻¹ • pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)
end AtomicTriangular.Construction
end

end OAI
end


