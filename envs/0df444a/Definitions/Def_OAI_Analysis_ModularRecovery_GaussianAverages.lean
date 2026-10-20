-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_GaussianAverages
-- name    : OAI_Analysis_ModularRecovery_GaussianAverages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:32:57.64772+00:00
-- url     : https://prove2.me/theorems/5aec55ff-a765-42dc-b8fa-3651e7d747b9
-- title:
--   Gaussian averages of modular kernels
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   With the Gaussian cutoffs $g_n$, the kernel scalar $\kappa(r)=1/(2\cosh(r/2))$ and the modular kernels $K_r(b)\in M$ for $b\in M'$:
--
--   1. **Gaussian Fourier weight.** $w_{n,t}(r)=g_n(r)e^{itr}$.
--   2. **Kernel multiplier.** The bounded function $u\mapsto\int w_{n,t}(r)\,\kappa(r-u)\,dr$.
--   3. **Kernel average.** The element of $M$
--   $$
--   A_{n,t}(b)=\int g_n(r)e^{itr}K_r(b)\,dr ,
--   $$
--   a strong integral, with $A_{n,t}(b)\xi$ given by the kernel multiplier applied to $Jb^*\xi$.
--   4. **Gram pairing.** $\sum_{i,j}\langle h_i,K_r(b_j^*b_i)h_j\rangle$, a positive definite function of $r$. It makes the Gram matrices of kernel averages positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/GaussianAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/GaussianAverages.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
import Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
import Definitions.Def_OAI_Analysis_ModularRecovery_Commutant
import Definitions.Def_OAI_Analysis_ModularRecovery_PositiveKernels
import Definitions.Def_OAI_Analysis_ModularRecovery_KernelContinuity
import Definitions.Def_OAI_Analysis_ModularRecovery_StrongIntegrals

namespace OAI

/-! Gaussian operator averages and their positivity and adjoint identities. -/

universe u uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

lemma spectralCharacter_arg_add (t r s : ℝ) :
    spectralCharacter t (r+s) = spectralCharacter t r*spectralCharacter t s := by
  simp [mul_add,add_mul,Complex.exp_add]

lemma spectralCharacter_arg_neg (t r : ℝ) :
    spectralCharacter t (-r) = star (spectralCharacter t r) := by
  simp [← Complex.exp_conj]

lemma spectralCharacter_arg_sub (t r s : ℝ) :
    spectralCharacter t (r-s) = spectralCharacter t r*star (spectralCharacter t s) := by
  rw [sub_eq_add_neg,spectralCharacter_arg_add,spectralCharacter_arg_neg]

def gaussianFourierWeight (n : ℕ) (t r : ℝ) : ℂ :=
  (gaussianCutoff n r:ℂ)*spectralCharacter t r

lemma integrable_gaussianFourierWeight (n : ℕ) (t : ℝ) :
    Integrable (gaussianFourierWeight n t) := by
  exact integrable_smul_bounded_orbit (integrable_gaussianCutoff n).ofReal
    (spectralCharacter t).continuous (C := 1) (by intro r; exact (spectralCharacter_norm t r).le)

lemma integrable_weight_translatedKernel (n : ℕ) (t : ℝ) :
    Integrable (fun r => gaussianFourierWeight n t r • translatedKernel r) :=
  integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
    continuous_translatedKernel norm_translatedKernel_le

def kernelMultiplier (n : ℕ) (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  ∫ r, gaussianFourierWeight n t r • translatedKernel r

lemma kernelMultiplier_apply (n : ℕ) (t u : ℝ) :
    kernelMultiplier n t u = ∫ r, gaussianFourierWeight n t r*(kernelScalar (r-u):ℂ) := by
  exact ((BoundedContinuousFunction.evalCLM ℂ u).integral_comp_comm
    (integrable_weight_translatedKernel n t)).symm

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


