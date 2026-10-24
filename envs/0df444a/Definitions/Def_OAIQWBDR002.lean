-- Prove2me | Definitions.Def_OAIQWBDR002
-- name    : OAIQWBDR002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T20:38:12.766076+00:00
-- url     : https://prove2.me/theorems/091d7547-377d-434c-b7cd-04edaab0ec4a
-- title:
--   OpenAI bounded modular recovery split: definitions bundle OAIQWBDR002
-- statement:
--   A definitions bundle of the split of OpenAI's proof of the bounded recovery theorem for modular spectral averages (`OAI.BoundedRecovery.bounded_recovery`, the paper's Theorem 4.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/ModularRecovery` (OpenAI, *Bounded recovery for modular spectral averages*, OpenAI Math Release, September 23, 2026, result family 290, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the Fourier filters and modular averages: the von Neumann algebra instances needed for continuous functional calculus, the kernel averages of the modular group (`kernelAverageOp`, `kernelAverage`, `gramKernelPairing`), the Fourier kernels (`fourierKernel`, `normalizedFourier`), the finite modular averages (`modularAverage`), the spectral band multipliers (`bandMultiplier`) and the $L^1$ norm constant of the localizing filter (`filterL1`), which bounds the norms of the recovered elements.
--
--   The definitions of the published statement (`StandardModularData`, `RealSpectralCalculus`, `fixedMean`, `RecoveryConclusion` and the rest) are not repeated: the bundle imports them from the published bundle `Def_BoundedRecovery`. It also imports the bundles `OAIQWBDR000`, `OAIQWBDR001` of this split.
--
--   Modules: `FiniteMoments`, `FourierKernels`, `FourierLocalization`, `FourierOperators`, `GaussianAverages`, `KernelContinuity`, `PositiveKernels`, `StrongIntegrals`, `TomitaFundamental`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWBDR002` (and through it the other two) and proves `OAI.BoundedRecovery.bounded_recovery`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Bounded recovery for modular spectral averages, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 290; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-recovery-for-modular-spectral-averages-September-23-2026/Bounded-recovery-for-modular-spectral-averages-September-23-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/ModularRecovery at commit adc7f12

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAIQWBDR000
import Definitions.Def_OAIQWBDR001

section
-- module Solutions.OAIQW_BoundedRecovery.TomitaFundamental
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed Tomita relations and bounded transforms. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma isClosed_bounded_orbit (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    {C : ℝ} (hC : 0 ≤ C) :
    IsClosed {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v} := by
  rw [← closure_subset_iff_isClosed]
  intro h hh
  exact bounded_orbit_lift M xi hsep hC hh

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.PositiveKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive operator kernels, matrix pairings, and norm bounds. -/

universe u uA uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open scoped ComplexConjugate
namespace BoundedRecovery

section Matrices
variable {A : Type uA} {n : Type uN} [CStarAlgebra A] [Fintype n]

lemma weightedMatrixFunctional_star_mul (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (a : CStarMatrix n n A) :
    (weightedMatrixFunctional φ w (star a*a)).re =
      ∑ i, w i * ∑ j, (φ (star (a j i) * a j i)).re := by
  simp [weightedMatrixFunctional, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply, Complex.mul_re]

lemma weightedMatrixFunctional_nonneg (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ a : A, 0 ≤ (φ (star a*a)).re)
    (a : CStarMatrix n n A) :
    0 ≤ (weightedMatrixFunctional φ w (star a*a)).re := by
  rw [weightedMatrixFunctional_star_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Finset.sum_nonneg (fun j _ => hp _)))

lemma weightedMatrixFunctional_faithful (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (hw : ∀ i, 0 < w i) (hp : ∀ a : A, 0 ≤ (φ (star a*a)).re)
    (hf : ∀ a : A, (φ (star a*a)).re = 0 → a = 0)
    (a : CStarMatrix n n A) (ha : (weightedMatrixFunctional φ w (star a*a)).re = 0) : a = 0 := by
  rw [weightedMatrixFunctional_star_mul] at ha
  have hh (i : n) : ∑ j, (φ (star (a j i)*a j i)).re = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hw k).le
      (Finset.sum_nonneg (fun j _ => hp (a j k))))).mp ha i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hs).resolve_left (hw i).ne'
  ext i j
  apply hf
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hp (a k j))).mp (hh j) i (Finset.mem_univ i)

end Matrices
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannAlgebra_complete (M : VonNeumannAlgebra H) : CompleteSpace M.toStarSubalgebra :=
  (vonNeumannAlgebra_isClosed M).completeSpace_coe

namespace StandardModularData

lemma modularKernel_star (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.modularKernel r b) = S.modularKernel (-r) (star b) := by
  apply S.eq_of_weakEquation (-r)
  intro c
  rw [S.modularKernel_weakEquation]
  have hh := congrArg star (S.modularKernel_weakEquation r b (star c))
  simp only [star_add, star_mul, ← S.phi_star, star_star,
    ← S.commutingPairing_star] at hh
  simp only [Complex.star_def, Complex.conj_ofReal] at hh
  have he : (Real.exp (-r):ℂ)*(Real.exp r:ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have heh : (Real.exp (-r):ℂ)*(Real.exp (r/2):ℂ) = (Real.exp (-r/2):ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  linear_combination (Real.exp (-r):ℂ)*hh -
    S.phi (star (S.modularKernel r b)*c)*he + S.commutingPairing (star b) c*heh

lemma modularKernel_one (S : StandardModularData H) (r : ℝ) :
    S.modularKernel r 1 = ((Real.exp (r/2)/(Real.exp r+1):ℝ):ℂ) • 1 := by
  apply S.eq_of_weakEquation r
  intro c
  rw [S.modularKernel_weakEquation]
  have hc : S.commutingPairing 1 c = S.phi c := rfl
  rw [hc]
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,map_smul,smul_eq_mul]
  have hn : (Real.exp r:ℂ)+1 ≠ 0 := by exact_mod_cast (ne_of_gt (add_pos (Real.exp_pos r) zero_lt_one))
  rw [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one]
  field_simp

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma vonNeumannAlgebra_sqrt_mem (M : VonNeumannAlgebra H) {a : H →L[ℂ] H}
    (ha : a ∈ M) (hp : 0 ≤ a) : CFC.sqrt a ∈ M := by
  let _ : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  change CFC.sqrt a ∈ M.toStarSubalgebra
  rw [CFC.sqrt_eq_real_sqrt _ hp]
  exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt (show a ∈ M.toStarSubalgebra from ha)

instance vonNeumannAlgebra_starOrdered (M : VonNeumannAlgebra H) : StarOrderedRing M.toStarSubalgebra := by
  apply StarOrderedRing.of_le_iff
  intro x y
  constructor
  · intro h
    have hp : 0 ≤ (y:H →L[ℂ] H)-(x:H →L[ℂ] H) := sub_nonneg.mpr h
    refine ⟨⟨CFC.sqrt ((y:H →L[ℂ] H)-(x:H →L[ℂ] H)),
      vonNeumannAlgebra_sqrt_mem M (sub_mem y.property x.property) hp⟩, ?_⟩
    exact Subtype.ext (sqrt_factor_eq (x:H →L[ℂ] H) (y:H →L[ℂ] H) h)
  · rintro ⟨z,rfl⟩
    change (x:H →L[ℂ] H) ≤ (x:H →L[ℂ] H)+star (z:H →L[ℂ] H)*(z:H →L[ℂ] H)
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

namespace StandardModularData

lemma modularGram_selfAdjoint {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) : IsSelfAdjoint (S.modularGram r b) := by
  apply CStarMatrix.ext
  intro i j
  change star (S.modularKernel (r j-r i) (star (b i)*b j)) = _
  rw [S.modularKernel_star,star_mul,star_star,neg_sub]
  rfl

lemma modularGram_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ) (b : n → S.M.commutant.toStarSubalgebra) :
    0 ≤ S.modularGram r b := by
  apply nonneg_of_jordan_pairing (weightedMatrixFunctional S.phi (fun i => Real.exp (-r i)))
    (weightedMatrixFunctional_nonneg S.phi _ (fun i => (Real.exp_pos _).le) S.phi_nonneg)
    (weightedMatrixFunctional_faithful S.phi _ (fun i => Real.exp_pos _) S.phi_nonneg S.phi_faithful)
    _ (S.modularGram_selfAdjoint r b)
  intro Y hY
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n S.M.toStarSubalgebra) IsSelfAdjoint :=
    (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
      (A := CStarMatrix n n S.M.toStarSubalgebra)).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix n n S.M.toStarSubalgebra) :=
    CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨Z, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY
  rw [S.modularGram_pairing]
  simp only [Complex.re_sum]
  exact Finset.sum_nonneg (fun k _ => @inner_self_nonneg ℂ H _ _ _ _)

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannAlgebra_realCFC (M : VonNeumannAlgebra H) :
    NonUnitalContinuousFunctionalCalculus ℝ M.toStarSubalgebra IsSelfAdjoint :=
  (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
    (A := M.toStarSubalgebra)).toNonUnitalContinuousFunctionalCalculus

instance vonNeumannAlgebra_nonnegSpectrum (M : VonNeumannAlgebra H) :
    NonnegSpectrumClass ℝ M.toStarSubalgebra := CStarAlgebra.instNonnegSpectrumClass'

namespace StandardModularData

lemma kernelMatrix_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) : 0 ≤ S.kernelMatrix r b := by
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  exact S.modularGram_nonneg r (fun _ => d)

lemma kernelMatrix_smul {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.kernelMatrix r (c • b) = c • S.kernelMatrix r b := by
  apply CStarMatrix.ext
  intro i j
  exact S.modularKernel_smul _ b c

lemma kernelMatrix_mono {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ)
    {b c : S.M.commutant.toStarSubalgebra} (hbc : b ≤ c) :
    S.kernelMatrix r b ≤ S.kernelMatrix r c := by
  have he : S.kernelMatrix r (c-b)+S.kernelMatrix r b = S.kernelMatrix r c := by
    rw [← S.kernelMatrix_add, sub_add_cancel]
  exact he ▸ le_add_of_nonneg_left (S.kernelMatrix_nonneg r _ (sub_nonneg.mpr hbc))

lemma modularKernel_one' (S : StandardModularData H) (r : ℝ) :
    S.modularKernel r 1 = (kernelScalar r:ℂ) • 1 := by
  rw [S.modularKernel_one]
  simp only [kernelScalar, Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one]

lemma norm_kernelMatrix_one_le {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ) :
    ‖S.kernelMatrix r 1‖ ≤ (Fintype.card n:ℝ)^2/2 := by
  apply (cstarMatrix_norm_le_sum _).trans
  calc
    (∑ j, ∑ i, ‖S.kernelMatrix r 1 i j‖) ≤ ∑ _j : n, ∑ _i : n, (1/2:ℝ) := by
      gcongr with j _ i _
      rw [S.kernelMatrix_apply,S.modularKernel_one',norm_smul,Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (kernelScalar_pos _)]
      exact (mul_le_of_le_one_right (kernelScalar_pos _).le ContinuousLinearMap.norm_id_le).trans (kernelScalar_le _)
    _ = _ := by simp; ring

lemma norm_modularKernel_of_nonneg (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) :
    ‖S.modularKernel r b‖ ≤ 2*‖b‖ := by
  let rs : Fin 2 → ℝ := ![r,0]
  have heq : algebraMap ℝ S.M.commutant.toStarSubalgebra ‖b‖ =
      (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    apply Subtype.ext
    ext h
    simp [Algebra.algebraMap_eq_smul_one]
  have hle : b ≤ (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    rw [← heq]
    exact hb.isSelfAdjoint.le_algebraMap_norm_self
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le (S.kernelMatrix_nonneg rs b hb)
    (S.kernelMatrix_mono rs hle)
  have he : ‖S.modularKernel r b‖ ≤ ‖S.kernelMatrix rs b‖ := by
    simpa only [kernelMatrix_apply,rs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
      sub_zero] using (CStarMatrix.norm_entry_le_norm (M := S.kernelMatrix rs b) (i := 0) (j := 1))
  refine he.trans (hn.trans ?_)
  rw [S.kernelMatrix_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  have hk := S.norm_kernelMatrix_one_le rs
  norm_num at hk
  nlinarith [norm_nonneg b]

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.KernelContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar kernel bounds, continuity, and spectral representations. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma norm_modularKernel_le (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : ‖S.modularKernel r b‖ ≤ 8*‖b‖ := by
  obtain ⟨x,hx,hxn,he⟩ := CStarAlgebra.exists_sum_four_nonneg b
  nth_rw 1 [he]
  rw [S.modularKernel_sum]
  calc
    ‖∑ i : Fin 4, S.modularKernel r (Complex.I ^ (i:ℕ) • x i)‖ ≤
        ∑ i : Fin 4, 2*‖b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [S.modularKernel_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
      exact (S.norm_modularKernel_of_nonneg r (x i) (hx i)).trans (by gcongr; exact hxn i)
    _ = 8*‖b‖ := by simp; ring

end StandardModularData

namespace StandardModularData

lemma continuous_modularKernel_apply (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (h : H) :
    Continuous (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) h) := by
  rw [continuous_iff_continuousAt]
  intro r
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hd := commutant_cyclic S.M S.xi S.separating
  obtain ⟨_,⟨c,hc,rfl⟩,hclose⟩ := hd.exists_dist_lt h (by positivity : 0 < ε/(3*(8*‖b‖+1)))
  have hcont : Continuous (fun s : ℝ => (S.modularKernel s b:H →L[ℂ] H) (c S.xi)) := by
    have hm : ∀ s, (S.modularKernel s b:H →L[ℂ] H) (c S.xi) =
        c ((S.modularKernel s b:H →L[ℂ] H) S.xi) := by
      intro s
      exact congrArg (fun a : H →L[ℂ] H => a S.xi)
        (VonNeumannAlgebra.mem_commutant_iff.mp hc _ (S.modularKernel s b).property)
    simp_rw [hm]
    exact c.continuous.comp (S.continuous_modularKernel_xi b)
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s hs
  have hbound : ∀ u, ‖(S.modularKernel u b:H →L[ℂ] H) (h-c S.xi)‖ < ε/3 := by
    intro u
    apply (ContinuousLinearMap.le_opNorm _ _).trans_lt
    apply (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le u b) (norm_nonneg _)).trans_lt
    rw [dist_eq_norm] at hclose
    have hp : 0 < 8*‖b‖+1 := by positivity
    have hh := (lt_div_iff₀ (by positivity : 0 < 3*(8*‖b‖+1))).mp hclose
    nlinarith [norm_nonneg (h-c S.xi)]
  have hh := norm_add_le ((S.modularKernel s b:H →L[ℂ] H) (h-c S.xi))
    ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi))
  have ht := norm_add_le
    ((S.modularKernel s b:H →L[ℂ] H) (h-c S.xi)+
      ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi)))
    (- (S.modularKernel r b:H →L[ℂ] H) (h-c S.xi))
  simp only [map_sub,sub_add_sub_cancel,norm_neg] at ht hh ⊢
  rw [dist_eq_norm]
  have hm := hd hs
  rw [dist_eq_norm] at hm
  have hs' := hbound s
  have hr' := hbound r
  simp only [map_sub] at hs' hr'
  have he : (S.modularKernel s b:H →L[ℂ] H) h-(S.modularKernel r b:H →L[ℂ] H) h =
    ((S.modularKernel s b:H →L[ℂ] H) h-(S.modularKernel s b:H →L[ℂ] H) (c S.xi))+
    ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi))+
    -((S.modularKernel r b:H →L[ℂ] H) h-(S.modularKernel r b:H →L[ℂ] H) (c S.xi)) := by abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  simp only [sub_add_sub_cancel, norm_neg]
  linarith

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma translatedKernel_eq_mixed (r : ℝ) :
    translatedKernel r = (Real.exp (r/2):ℂ) • modularMixedResolvent r := by
  ext u
  change ((Real.exp ((r-u)/2)/(Real.exp (r-u)+1):ℝ):ℂ) =
    (Real.exp (r/2):ℂ)*((Real.exp (u/2)/(Real.exp r+Real.exp u):ℝ):ℂ)
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [show (r-u)/2=r/2-u/2 by ring,Real.exp_sub,Real.exp_sub,exp_eq_sq_exp_half u]
  have hp : Real.exp (u/2) ≠ 0 := (Real.exp_pos _).ne'
  have hq : Real.exp r+Real.exp (u/2)^2 ≠ 0 := by positivity
  field_simp

namespace StandardModularData
lemma modularKernel_xi (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    (S.modularKernel r b:H →L[ℂ] H) S.xi =
      S.D.calculus (translatedKernel r) (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  have hg := S.commutant_halfGraph (↑(star b)) (star b).property
  simp only [StarMemClass.coe_star,star_star] at hg
  have hh := S.D.halfGraph_calculus hg (modularResolvent r)
  have hq := S.D.modularResolvent_halfGraph r (S.J ((star (b:H →L[ℂ] H)) S.xi))
  have he := S.D.halfGraph_unique hh hq
  change (Real.exp (r/2):ℂ) • (S.modularLift r b:H →L[ℂ] H) S.xi = _
  rw [S.modularLift_xi,he,translatedKernel_eq_mixed,map_smul]
  rfl
end StandardModularData
end BoundedRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.StrongIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong operator integrals and positivity under Gaussian integration. -/

universe uE uX uY

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

lemma gaussianVariance_pos (n : ℕ) : 0 < gaussianVariance n := by
  unfold gaussianVariance
  positivity

lemma gaussianNormalization_pos (n : ℕ) : 0 < gaussianNormalization n := by
  apply inv_pos.mpr
  exact gaussianPDFReal_pos _ _ _ (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)))

lemma gaussianNormalization_pdf (n : ℕ) (r : ℝ) :
    gaussianNormalization n * gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) r =
      gaussianCutoff n r := by
  unfold gaussianNormalization gaussianPDFReal
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one]
  rw [inv_inv,mul_inv_cancel_left₀]
  · unfold gaussianCutoff
    congr 1
    simp only [gaussianVariance,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    congr 1
    ring
  · apply Real.sqrt_ne_zero'.mpr
    have hv : (0:ℝ) < (gaussianVariance n+gaussianVariance n:ℝ≥0) :=
      by exact_mod_cast add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)
    positivity

lemma integral_gaussianCutoff_eq {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) :
    (∫ r, gaussianCutoff n r • f r) = gaussianNormalization n •
      ∫ r, f r ∂gaussianReal 0 (gaussianVariance n+gaussianVariance n) := by
  rw [integral_gaussianReal_eq_integral_smul
    (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n))), ← integral_smul]
  simp_rw [smul_smul,gaussianNormalization_pdf]

lemma gaussianCutoff_positive_definite (n : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hpos : ∀ (ι : Type) [Fintype ι] (r : ι → ℝ) (c : ι → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * f (r i-r j)).re) :
    0 ≤ (∫ r, (gaussianCutoff n r:ℂ)*f r).re := by
  change 0 ≤ (∫ r, gaussianCutoff n r • f r).re
  rw [integral_gaussianCutoff_eq]
  rw [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (gaussianNormalization_pos n).le
    (gaussian_positive_definite (gaussianVariance n) f hf C hC hpos)

end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.GaussianAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian operator averages and their positivity and adjoint identities. -/

universe u uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

lemma spectralCharacter_arg_neg (t r : ℝ) :
    spectralCharacter t (-r) = star (spectralCharacter t r) := by
  simp [← Complex.exp_conj]

lemma spectralCharacter_arg_sub (t r s : ℝ) :
    spectralCharacter t (r-s) = spectralCharacter t r*star (spectralCharacter t s) := by
  rw [sub_eq_add_neg,spectralCharacter_arg_add,spectralCharacter_arg_neg]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def kernelAverageOp (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : H →L[ℂ] H :=
  strongIntegral (gaussianFourierWeight n t) (integrable_gaussianFourierWeight n t)
    (fun r => (S.modularKernel r b:H →L[ℂ] H)) (S.continuous_modularKernel_apply b)
    (8*‖b‖) (fun r => S.norm_modularKernel_le r b)

lemma kernelAverageOp_mem (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.kernelAverageOp n t b ∈ S.M := by
  rw [← S.M.commutant_commutant,VonNeumannAlgebra.mem_commutant_iff]
  intro d hd
  ext h
  have hi := integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
    (S.continuous_modularKernel_apply b h) (C := 8*‖b‖*‖h‖)
    (fun r => (S.modularKernel r b:H →L[ℂ] H).le_opNorm h |>.trans
      (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r b) (norm_nonneg _)))
  change d (∫ r, gaussianFourierWeight n t r • (S.modularKernel r b:H →L[ℂ] H) h) = _
  rw [← d.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [map_smul]
  congr 1
  exact (congrArg (fun a : H →L[ℂ] H => a h)
    (VonNeumannAlgebra.mem_commutant_iff.mp hd _ (S.modularKernel r b).property)).symm

def kernelAverage (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  ⟨S.kernelAverageOp n t b,S.kernelAverageOp_mem n t b⟩

lemma kernelAverage_apply (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (h : H) :
    (S.kernelAverage n t b:H →L[ℂ] H) h =
      ∫ r, gaussianFourierWeight n t r • (S.modularKernel r b:H →L[ℂ] H) h := rfl

lemma kernelAverage_xi (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    (S.kernelAverage n t b:H →L[ℂ] H) S.xi =
      S.D.calculus (kernelMultiplier n t) (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  change (∫ r, gaussianFourierWeight n t r • (S.modularKernel r b:H →L[ℂ] H) S.xi) = _
  simp_rw [S.modularKernel_xi]
  have hc := S.D.calculusCLM.integral_comp_comm (integrable_weight_translatedKernel n t)
  change _ = S.D.calculusCLM (∫ r, gaussianFourierWeight n t r • translatedKernel r) _
  rw [← hc,ContinuousLinearMap.integral_apply
    (S.D.calculusCLM.integrable_comp (integrable_weight_translatedKernel n t))]
  simp only [map_smul,smul_apply]
  rfl

lemma kernelAverage_add (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.kernelAverage n t (b+c) = S.kernelAverage n t b + S.kernelAverage n t c := by
  apply S.eq_of_xi
  change (S.kernelAverage n t (b+c):H →L[ℂ] H) S.xi =
    (S.kernelAverage n t b:H →L[ℂ] H) S.xi + (S.kernelAverage n t c:H →L[ℂ] H) S.xi
  simp only [S.kernelAverage_xi,star_add]
  change S.D.calculus (kernelMultiplier n t) (S.J ((star (b:H →L[ℂ] H)+star (c:H →L[ℂ] H)) S.xi)) = _
  simp only [add_apply, map_add,StarMemClass.coe_star]

lemma kernelAverage_smul (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (z : ℂ) :
    S.kernelAverage n t (z • b) = z • S.kernelAverage n t b := by
  apply S.eq_of_xi
  change (S.kernelAverage n t (z • b):H →L[ℂ] H) S.xi =
    z • (S.kernelAverage n t b:H →L[ℂ] H) S.xi
  simp only [S.kernelAverage_xi,star_smul]
  change S.D.calculus (kernelMultiplier n t) (S.J ((star z • star (b:H →L[ℂ] H)) S.xi)) = _
  simp only [smul_apply,map_smulₛₗ,Complex.star_def,starRingEnd_self_apply,
    RingHom.id_apply,StarMemClass.coe_star]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cstarMatrix_vector_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (M : VonNeumannAlgebra H) (A : CStarMatrix n n M.toStarSubalgebra) (hA : 0 ≤ A)
    (h : n → H) : 0 ≤ (∑ i, ∑ j, inner ℂ (h i) ((A i j:H →L[ℂ] H) (h j))).re := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n M.toStarSubalgebra) IsSelfAdjoint :=
    (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
      (A := CStarMatrix n n M.toStarSubalgebra)).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix n n M.toStarSubalgebra) :=
    CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨Z,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have hmul (a b : M.toStarSubalgebra) : (↑(a*b):H →L[ℂ] H) = (a:H →L[ℂ] H)*(b:H →L[ℂ] H) := rfl
  have he : (∑ i, ∑ j, inner ℂ (h i) (((star Z*Z) i j:H →L[ℂ] H) (h j))) =
      ∑ k, inner ℂ (∑ i, (Z k i:H →L[ℂ] H) (h i)) (∑ j, (Z k j:H →L[ℂ] H) (h j)) := by
    simp only [CStarMatrix.mul_apply,CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply,AddSubmonoidClass.coe_finsetSum,hmul,
      StarMemClass.coe_star,sum_apply,mul_apply_eq_comp,
      inner_sum,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
      sum_inner]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he,Complex.re_sum]
  exact Finset.sum_nonneg (fun _ _ => @inner_self_nonneg ℂ H _ _ _ _)

namespace StandardModularData
lemma modularGram_vector_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ) (b : n → S.M.commutant.toStarSubalgebra)
    (h : n → H) : 0 ≤ (∑ i, ∑ j,
      inner ℂ (h i) ((S.modularKernel (r i-r j) (star (b j)*b i):H →L[ℂ] H) (h j))).re :=
  cstarMatrix_vector_nonneg S.M _ (S.modularGram_nonneg r b) h
end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {m : Type uM} [Fintype m]

def gramKernelPairing (S : StandardModularData H)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) (r : ℝ) : ℂ :=
  ∑ i, ∑ j, inner ℂ (h i) ((S.modularKernel r (star (b j)*b i):H →L[ℂ] H) (h j))

lemma continuous_gramKernelPairing (S : StandardModularData H)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    Continuous (S.gramKernelPairing b h) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.inner (S.continuous_modularKernel_apply _ _)

lemma norm_gramKernelPairing_le (S : StandardModularData H)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) (r : ℝ) :
    ‖S.gramKernelPairing b h r‖ ≤ ∑ i, ∑ j, ‖h i‖*(8*‖star (b j)*b i‖*‖h j‖) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_inner_le_norm _ _).trans
  gcongr
  exact (S.modularKernel r (star (b j)*b i):H →L[ℂ] H).le_opNorm (h j) |>.trans
    (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r _) (norm_nonneg _))

lemma gramKernelPairing_twisted_positive_definite (S : StandardModularData H)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) (t : ℝ)
    (n : Type) [Fintype n] (r : n → ℝ) (c : n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)*c j*
      (spectralCharacter t (r i-r j)*S.gramKernelPairing b h (r i-r j))).re := by
  classical
  have hp := S.modularGram_vector_nonneg (n := n×m)
    (fun p => r p.1) (fun p => b p.2)
    (fun p => (c p.1*star (spectralCharacter t (r p.1))) • h p.2)
  have he : (∑ i : n×m, ∑ j : n×m,
      inner ℂ ((c i.1*star (spectralCharacter t (r i.1))) • h i.2)
        ((S.modularKernel (r i.1-r j.1) (star (b j.2)*b i.2):H →L[ℂ] H)
          ((c j.1*star (spectralCharacter t (r j.1))) • h j.2))) =
      ∑ i, ∑ j, (starRingEnd ℂ) (c i)*c j*
        (spectralCharacter t (r i-r j)*S.gramKernelPairing b h (r i-r j)) := by
    simp only [Fintype.sum_prod_type,gramKernelPairing,spectralCharacter_arg_sub,
      map_smul,inner_smul_left,inner_smul_right,map_mul,Complex.star_def,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro d _
    simp only [starRingEnd_self_apply]
    ring
  exact he ▸ hp

lemma kernelAverage_gram_vector_nonneg (S : StandardModularData H)
    (n : ℕ) (t : ℝ) (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    0 ≤ (∑ i, ∑ j, inner ℂ (h i)
      ((S.kernelAverage n t (star (b j)*b i):H →L[ℂ] H) (h j))).re := by
  have hp := gaussianCutoff_positive_definite n
    (fun r => spectralCharacter t r*S.gramKernelPairing b h r)
    ((spectralCharacter t).continuous.mul (S.continuous_gramKernelPairing b h))
    (∑ i, ∑ j, ‖h i‖*(8*‖star (b j)*b i‖*‖h j‖))
    (fun r => by rw [norm_mul,spectralCharacter_norm,one_mul]; exact S.norm_gramKernelPairing_le b h r)
    (S.gramKernelPairing_twisted_positive_definite b h t)
  have he : (∫ r, (gaussianCutoff n r:ℂ)*
      (spectralCharacter t r*S.gramKernelPairing b h r)) =
      ∑ i, ∑ j, inner ℂ (h i)
        ((S.kernelAverage n t (star (b j)*b i):H →L[ℂ] H) (h j)) := by
    simp only [gramKernelPairing,Finset.mul_sum,← mul_assoc]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        change (∫ r, gaussianFourierWeight n t r*inner ℂ (h i)
          ((S.modularKernel r (star (b j)*b i):H →L[ℂ] H) (h j))) = _
        rw [S.kernelAverage_apply]
        simpa only [innerSL_apply_apply,inner_smul_right] using
          (innerSL ℂ (h i)).integral_comp_comm
          (integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
            (S.continuous_modularKernel_apply _ _) (C := 8*‖star (b j)*b i‖*‖h j‖)
            (fun r => (S.modularKernel r (star (b j)*b i):H →L[ℂ] H).le_opNorm (h j) |>.trans
              (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r _) (norm_nonneg _))))
      · intro j _
        apply integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
          (continuous_const.inner (S.continuous_modularKernel_apply _ _))
          (C := ‖h i‖*(8*‖star (b j)*b i‖*‖h j‖))
        intro r
        exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          ((S.modularKernel r (star (b j)*b i):H →L[ℂ] H).le_opNorm (h j) |>.trans
            (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r _) (norm_nonneg _))) (norm_nonneg _))
    · intro i _
      apply integrable_finsetSum
      intro j _
      apply integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
        (continuous_const.inner (S.continuous_modularKernel_apply _ _))
        (C := ‖h i‖*(8*‖star (b j)*b i‖*‖h j‖))
      intro r
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((S.modularKernel r (star (b j)*b i):H →L[ℂ] H).le_opNorm (h j) |>.trans
          (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r _) (norm_nonneg _))) (norm_nonneg _))
  rwa [he] at hp

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma gaussianCutoff_even (n : ℕ) (r : ℝ) : gaussianCutoff n (-r) = gaussianCutoff n r := by
  simp only [gaussianCutoff,neg_sq]

lemma gaussianFourierWeight_neg (n : ℕ) (t r : ℝ) :
    gaussianFourierWeight n t (-r) = star (gaussianFourierWeight n t r) := by
  simp only [gaussianFourierWeight,gaussianCutoff_even,spectralCharacter_arg_neg,
    star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma kernelAverage_inner (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (h k : H) :
    inner ℂ h ((S.kernelAverage n t b:H →L[ℂ] H) k) =
      ∫ r, gaussianFourierWeight n t r*inner ℂ h ((S.modularKernel r b:H →L[ℂ] H) k) := by
  rw [S.kernelAverage_apply]
  symm
  simpa only [innerSL_apply_apply,inner_smul_right] using
    (innerSL ℂ h).integral_comp_comm
      (integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
        (S.continuous_modularKernel_apply b k) (C := 8*‖b‖*‖k‖)
        (fun r => (S.modularKernel r b:H →L[ℂ] H).le_opNorm k |>.trans
          (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le r b) (norm_nonneg _))))

lemma kernelAverage_star (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.kernelAverage n t b) = S.kernelAverage n t (star b) := by
  apply Subtype.ext
  ext k
  apply ext_inner_left ℂ
  intro h
  rw [StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,← inner_conj_symm]
  rw [S.kernelAverage_inner,← integral_conj,S.kernelAverage_inner]
  rw [← integral_neg_eq_self (fun r => gaussianFourierWeight n t r*
    inner ℂ h ((S.modularKernel r (star b):H →L[ℂ] H) k)) volume]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [gaussianFourierWeight_neg,← S.modularKernel_star,StarMemClass.coe_star,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [map_mul,Complex.star_def,inner_conj_symm]

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier kernels and uniform bounds for Gaussian multipliers. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma kernelAverage_nonneg (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) : 0 ≤ S.kernelAverage n t b := by
  change 0 ≤ (S.kernelAverage n t b:H →L[ℂ] H)
  rw [ContinuousLinearMap.nonneg_iff_isPositive,ContinuousLinearMap.isPositive_def']
  refine ⟨?_,fun h => ?_⟩
  · show star (S.kernelAverage n t b:H →L[ℂ] H) = _
    rw [← StarMemClass.coe_star,S.kernelAverage_star,hb.isSelfAdjoint.star_eq]
  · obtain ⟨d,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    have hp := S.kernelAverage_gram_vector_nonneg n t (fun _ : Unit => d) (fun _ => h)
    change 0 ≤ (inner ℂ ((S.kernelAverage n t (star d*d):H →L[ℂ] H) h) h).re
    rw [← inner_conj_symm,Complex.conj_re]
    simpa only [Fintype.sum_unique] using hp

lemma kernelAverage_mono (S : StandardModularData H) (n : ℕ) (t : ℝ)
    {b c : S.M.commutant.toStarSubalgebra} (hbc : b ≤ c) :
    S.kernelAverage n t b ≤ S.kernelAverage n t c := by
  have he : S.kernelAverage n t (c-b)+S.kernelAverage n t b = S.kernelAverage n t c := by
    rw [← S.kernelAverage_add,sub_add_cancel]
  exact he ▸ le_add_of_nonneg_left (S.kernelAverage_nonneg n t _ (sub_nonneg.mpr hbc))

lemma kernelAverage_one (S : StandardModularData H) (n : ℕ) (t : ℝ) :
    S.kernelAverage n t 1 = (kernelMultiplier n t 0) • 1 := by
  apply Subtype.ext
  ext h
  rw [S.kernelAverage_apply]
  simp_rw [S.modularKernel_one']
  change (∫ r, gaussianFourierWeight n t r • ((kernelScalar r:ℂ) • h)) = _
  simp_rw [smul_smul]
  rw [integral_smul_const]
  congr 1
  simp only [kernelMultiplier_apply,sub_zero]

lemma norm_kernelAverage_one_le (S : StandardModularData H) (n : ℕ) (t : ℝ) :
    ‖S.kernelAverage n t 1‖ ≤ kernelMass := by
  rw [S.kernelAverage_one,norm_smul]
  apply (mul_le_mul_of_nonneg_right
    (BoundedContinuousFunction.norm_coe_le_norm (kernelMultiplier n t) 0) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_right (norm_kernelMultiplier_le n t) (norm_nonneg _)).trans
  exact mul_le_of_le_one_right kernelMass_pos.le ContinuousLinearMap.norm_id_le

lemma norm_kernelAverage_of_nonneg (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) :
    ‖S.kernelAverage n t b‖ ≤ kernelMass*‖b‖ := by
  have heq : algebraMap ℝ S.M.commutant.toStarSubalgebra ‖b‖ =
      (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    apply Subtype.ext
    ext h
    simp [Algebra.algebraMap_eq_smul_one]
  have hle : b ≤ (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    rw [← heq]
    exact hb.isSelfAdjoint.le_algebraMap_norm_self
  apply (CStarAlgebra.norm_le_norm_of_nonneg_of_le (S.kernelAverage_nonneg n t b hb)
    (S.kernelAverage_mono n t hle)).trans
  rw [S.kernelAverage_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  nlinarith [S.norm_kernelAverage_one_le n t,norm_nonneg b]

lemma kernelAverage_sum {ι : Type uι} (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (s : Finset ι) (b : ι → S.M.commutant.toStarSubalgebra) :
    S.kernelAverage n t (∑ i ∈ s, b i) = ∑ i ∈ s, S.kernelAverage n t (b i) := by
  classical
  have hz : S.kernelAverage n t 0 = 0 := by simpa using S.kernelAverage_smul n t 0 0
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih => simp only [Finset.sum_insert hi, S.kernelAverage_add, ih]

lemma norm_kernelAverage_le (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : ‖S.kernelAverage n t b‖ ≤ 4*kernelMass*‖b‖ := by
  obtain ⟨x,hx,hxn,he⟩ := CStarAlgebra.exists_sum_four_nonneg b
  nth_rw 1 [he]
  rw [S.kernelAverage_sum]
  calc
    ‖∑ i : Fin 4, S.kernelAverage n t (Complex.I ^ (i:ℕ) • x i)‖ ≤
        ∑ i : Fin 4, kernelMass*‖b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [S.kernelAverage_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
      exact (S.norm_kernelAverage_of_nonneg n t (x i) (hx i)).trans
        (mul_le_mul_of_nonneg_left (hxn i) kernelMass_pos.le)
    _ = 4*kernelMass*‖b‖ := by simp; ring

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Fourier operators, Schwarz inequalities, and multiplication. -/

universe u uA uB uM

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma exists_fourierKernel_lift (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    ∃ a : H →L[ℂ] H, a ∈ S.M ∧ ‖a‖ ≤ 4*kernelMass*‖b‖ ∧
      a S.xi = kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  have ht : Tendsto (fun n => (S.kernelAverage n t b:H →L[ℂ] H) S.xi) atTop
      (𝓝 (kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)))) := by
    simpa only [S.kernelAverage_xi] using S.D.kernelMultiplier_strong_tendsto t
      (S.J ((↑(star b):H →L[ℂ] H) S.xi))
  exact (isClosed_bounded_orbit S.M S.xi S.separating
    (mul_nonneg (mul_nonneg (by norm_num) kernelMass_pos.le) (norm_nonneg b))).mem_of_tendsto ht
    (Filter.Eventually.of_forall fun n => ⟨S.kernelAverage n t b,(S.kernelAverage n t b).property,
      S.norm_kernelAverage_le n t b,rfl⟩)

def fourierKernel (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  ⟨Classical.choose (S.exists_fourierKernel_lift t b),
    (Classical.choose_spec (S.exists_fourierKernel_lift t b)).1⟩

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def normalizedFourier (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  (kernelFourier t)⁻¹ • S.fourierKernel t b

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous finite approximations of modular moments. -/

universe u uE uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {ι : Type uι} [Fintype ι]

def modularAverage (S : StandardModularData H) (p t : ι → ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, p i • S.sigma (t i) a

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar truncation and Fourier localization with a width-independent L1 bound. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace BoundedRecovery

def bandMultiplier (s rho : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => (bump0 ((u-s)/rho) : ℂ))
    (Complex.continuous_ofReal.comp (bump0.continuous.comp (by fun_prop))) 1 (by
      intro u
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump0.nonneg]
        using (bump0.le_one (x := (u-s)/rho)))

@[simp] lemma bandMultiplier_apply (s rho u : ℝ) :
    bandMultiplier s rho u = (bump0 ((u-s)/rho) : ℂ) := rfl

end BoundedRecovery

noncomputable section
open Set MeasureTheory
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def filterL1 : ℝ := ∫ t, ‖baseKernel t‖
end BoundedRecovery

end
end
end
end

end OAI
end


