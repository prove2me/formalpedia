-- Prove2me | Definitions.Def_OAIQ250T011
-- name    : OAIQ250T011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:10:13.874411+00:00
-- url     : https://prove2.me/theorems/c9fa0f24-75ef-4bf6-be3f-6232cce97eb0
-- title:
--   Definitions bundle OAIQ250T011 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 81 declarations of OpenAI's Lean: 37 definitions and 44 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.cellFactor`, `OAI.AtomicTriangular.Construction.cellSeparation`, `OAI.AtomicTriangular.Construction.localPhase`, `OAI.AtomicTriangular.Construction.localShift`, `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_2`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_4`, `OAI.AtomicTriangular.FiniteCertificate.curvatureConstant3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_0`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_2`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_4`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_4`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable00`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTail1`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTail2`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTail3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTail4`, `OAI.AtomicTriangular.FiniteCertificate.nearRadiusBox`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_0`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_1`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst1_0`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst1_1`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst2_0`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst2_1`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst3_0`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst3_1`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst4_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_ParamActual`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualInput`, `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_DirectWaveJets`, `Triangular_Construction_FiniteJets`, `Triangular_Construction_FiniteProjection`, `Triangular_Construction_Schur`, `Triangular_Schwartz_Regularity`, `Triangular_Signs_FarSigns`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_RemainderBoxes`, `Triangular_Signs_RemainderSums0`, `Triangular_Signs_RemainderSums1`, `Triangular_Signs_RemainderSums2`, `Triangular_Signs_RemainderSums3`, `Triangular_Signs_RemainderSums4`, `Triangular_Signs_SineBarrierBase`, `Triangular_Signs_SineGlobal`, `Triangular_Signs_SineGrid1`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridCover`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData01`, `Triangular_Taylor_CurvatureData11`, `Triangular_Taylor_TaylorRowsBase`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T000`, `OAIQ250T001` and `OAIQ250T002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T050`, `OAIQ250T051`, `OAIQ250T052`, `OAIQ250T053`, `OAIQ250T054`, `OAIQ250T055`, `OAIQ250T056`, `OAIQ250T057`, `OAIQ250T058`, `OAIQ250T059`, `OAIQ250T060`, `OAIQ250T061`, `OAIQ250T062`, `OAIQ250T063`, `OAIQ250T064`, `OAIQ250T065`, `OAIQ250T066`, `OAIQ250T067`, `OAIQ250T068`, `OAIQ250T069`, `OAIQ250T070`, `OAIQ250T071`, `OAIQ250T072`, `OAIQ250T073`, `OAIQ250T074`, `OAIQ250T075`, `OAIQ250T076`, `OAIQ250T077`, `OAIQ250T078`, `OAIQ250T079`, `OAIQ250T080`, `OAIQ250T081`, `OAIQ250T082` and `OAIQ250T083`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T000
import Definitions.Def_OAIQ250T001
import Definitions.Def_OAIQ250T002

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
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

end AtomicTriangular.Construction

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

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma spectralParameter_inv {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (spectralParameter k t)⁻¹ = lambda k t := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  apply inv_eq_of_mul_eq_one_right
  unfold lambda spectralParameter
  push_cast
  field_simp
  simp only [waveDen]
  push_cast
  ring_nf
  simp [I_sq]

lemma spectral_exponent {k : ℝ} (hk : 0 < k) (v t : ℝ) (x : Plane) :
    -(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter k t =
      -(Real.pi:ℂ)*v*(radial x:ℂ)+I*Real.pi*zeta k v t*(radial x:ℂ) := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  have hbs := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hbs
  rw [div_eq_mul_inv,spectralParameter_inv hk]
  unfold lambda zeta Xwave radial
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  rw [hbs]
  ring

lemma transformed_spectral_wave {k : ℝ} (hk : 0 < k) (v t : ℝ) (w : Plane) :
    𝓕 (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedWave k v t (radial w) := by
  have hfun : (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) =
      (fun x : Plane => exp (-(Real.pi:ℂ)*spectralParameter k t*‖x‖^2)) := by
    funext x
    rw [← exp_add]
    congr 1
    unfold spectralParameter radial
    push_cast
    ring
  rw [hfun,complex_gaussian_transform _ (spectralParameter_pos hk t),
    spectralParameter_inv hk,spectral_exponent hk,exp_add]
  unfold transformedWave
  ring

end AtomicTriangular.Construction

end
end
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma gaussianZ_bounds {α : ℝ} (hα : 1≤α) : 0 < gaussianZ α ∧ gaussianZ α < Z := by
  have hb : b ≤ (8661/10000:ℝ) := by nlinarith [b_sq,b_pos]
  have hquot : (10000/8661:ℝ) ≤ α/b := (le_div_iff₀ b_pos).mpr (by nlinarith)
  have hd : 0 ≤ α/b-h := by norm_num [h] at * <;> linarith
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_d2.le hd
  have he : 1/Z < Real.pi*(α/b-h) := by norm_num [h,Z] at * <;> linarith
  have hepos : 0 < Real.pi*(α/b-h) := lt_trans (by norm_num [Z]) he
  constructor
  · exact one_div_pos.mpr hepos
  · exact (div_lt_iff₀ hepos).mpr (by
      have hh := mul_lt_mul_of_pos_left he (by norm_num [Z] : 0<Z)
      norm_num [Z] at *
      nlinarith)
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

lemma neumann_equation (T : F →L[ℝ] F) (hT : ‖T‖<1) (y : F) :
    neumann T y - T (neumann T y) = y := by
  have hh := congrArg (fun A : F →L[ℝ] F => A y) (mul_neg_geom_series T hT)
  simpa only [neumann,sub_apply,mul_apply_eq_comp,
    one_apply_eq_self] using hh
omit [CompleteSpace E] in
lemma solution_equations (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) (h : ‖tailOperator L B K D‖<1) :
    tailSolution L B K D r s = D (tailSolution L B K D r s)+
      K (finiteSolution L B K D r s)+s := by
  have hh := neumann_equation (tailOperator L B K D) h (s+K (L r))
  change tailSolution L B K D r s - _ = _ at hh
  simp only [tailOperator,add_apply,ContinuousLinearMap.comp_apply] at hh
  simp only [finiteSolution,map_add]
  rw [sub_eq_iff_eq_add] at hh
  calc
    _ = s+K (L r)+(D (tailSolution L B K D r s)+K (L (B (tailSolution L B K D r s)))) := hh
    _ = _ := by abel
end AtomicTriangular.Schur
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

lemma tail_pairs_norm (w : TailCoefficients) :
    (∑' n, (|w (n,0)| + |w (n,1)|))=‖w‖ := by
  rw [l1_norm]
  symm
  calc
    (∑' p, |w p|) = ∑' n : TailNode, ∑' d : Fin 2, |w (n,d)| := (l1_summable w).tsum_prod
    _ = _ := by simp only [tsum_fintype,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
                rfl

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction
open Complex

lemma finiteC_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (finiteC a n).re=Q n ∧ 6*(deriv (finiteC a) n).re=(waveDerivative 3 n).re := by
  let g : ℂ → ℂ := fun s => ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hg : Differentiable ℂ g := by unfold g sineFactor; fun_prop
  have h0 := sineFactor_at_residue a n hn
  have h2 : iteratedDeriv 2 (sineFactor a) n=0 := by simp only [sineFactor_second,h0,mul_zero]
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by
      simpa [sineFactor] using h0
    simpa [hsin] using (sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ))))
  have hd : (deriv (sineFactor a) n)^2=4*(kappa:ℂ)^2 := by
    rw [sineFactor_deriv]
    calc
      _ = 4*(kappa:ℂ)^2*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2 := by ring
      _ = _ := by rw [hc,mul_one]
  obtain ⟨hp2,hp3⟩ := square_zero_product_jets (sineFactor a) g hf hg n h0 h2
  have hp : (fun s => sineFactor a s^2*g s)=P := (funext (P_factor a)).symm
  rw [hp,←waveDerivative_eq_iterated,hd] at hp2 hp3
  have hfc : deriv (finiteC a) n=4*(kappa:ℂ)^2*deriv g n :=
    ((hg n).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  constructor
  · have hr := congrArg Complex.re hp2
    change (4*(kappa:ℂ)^2*g n).re= Q n
    unfold Q
    rw [hp2]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring
  · rw [hfc,hp3]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring

lemma finiteD_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteD a n=0 ∧ deriv (finiteD a) n=finiteC a n := by
  obtain ⟨h0,h1⟩ := finiteRatio_matching a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,zero_mul]
  · have hh := (((differentiable_finiteRatio a (n:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,zero_mul,one_mul,add_zero] at hh
    exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma finiteC_deriv_re (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (deriv (finiteC a) n).re=Q n*D n := by
  have hmem : n%36∈residues := by rw [hn]; exact residue_mem a
  have hQ : Q n≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n hmem).1).ne'
  have hh := (finiteC_matching_jets a n hn).2
  unfold D
  field_simp
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma rowNode_mem (i : Fin 20) : (rowNode i).val∈FiniteNodes := by
  have hh : ∀ n : Fin 10,finiteNode n∈FiniteNodes := by decide +kernel
  exact hh _
lemma finite_column_matching (i : Fin 20) (c : Fin 22) :
    ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by
  have hh : ∀ i : Fin 20, ∀ c : Fin 22,
      ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by decide +kernel
  exact hh i c
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma gaussianG_deriv {z : ℝ} (hz : 0<z) (s : ℝ) :
    HasDerivAt (gaussianG z) (-Q 1*Real.exp ((1-s)/z)) s := by
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (Q 1*z))
  convert hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; field_simp; ring)
lemma negativeJet_gaussian {z : ℝ} (hz : 0<z) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (gaussianG z n:ℂ) ((deriv (gaussianG z) (n:ℝ):ℝ):ℂ)).re = -gaussianTarget v z n d := by
  rw [negativeJet_re,(gaussianG_deriv hz n).deriv]
  simp only [ofReal_re,gaussianG,gaussianTarget,Real.exp_add]
  split_ifs <;> ring
lemma rowNode_cover (n : Node) (hn : n.val∈FiniteNodes) (d : Fin 2) :
    ∃ i : Fin 20,rowNode i=n ∧ rowDerivative i=d := by
  obtain ⟨j,hj⟩ := finiteNode_surj hn
  refine ⟨⟨2*j.val+d.val,by omega⟩,?_,?_⟩
  · apply Subtype.ext
    change finiteNode ⟨(2*j.val+d.val)/2,by omega⟩=n.val
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Fin.ext
    dsimp
    omega
  · apply Fin.ext
    change (2*j.val+d.val)%2=d.val
    omega
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvatureData00_0 : Fin 31 → RI := ![⟨6853891945200943485301729861025104955078957921694968091335063,6853891945200943485301729861025104955078957921695011725457718⟩,⟨5970501427819488547196173567826313649757670011787616648451868,5970501427819488547196173567826313649757670011787654658620941⟩,⟨5148034394395375328959965984503301055148195061184220477491670,5148034394395375328959965984503301055148195061184253251566020⟩,⟨4386490844928603830593107111056067171250533069884779578454432,4386490844928603830593107111056067171250533069884807504292938⟩,⟨3685870779419174052095596947484611998064684037889293951340190,3685870779419174052095596947484611998064684037889317416801713⟩,⟨3046174197867085993467435493788935535590647965197763596148910,3046174197867085993467435493788935535590647965197782989092322⟩,⟨2467401100272339654708622749969037783828424851810188512880611,2467401100272339654708622749969037783828424851810204221164776⟩,⟨1949551486634935035819158716024918742778014697726568701535301,1949551486634935035819158716024918742778014697726581113019088⟩,⟨1492625356954872136799043391956578412439417502946904162112959,1492625356954872136799043391956578412439417502946913664655238⟩,⟨1096622711232150957648276777764016792812633267471194894613605,1096622711232150957648276777764016792812633267471201876073241⟩,⟨761543549466771498366858873447233883897661991299440899037221,761543549466771498366858873447233883897661991299445747273083⟩,⟨487387871658733758954789679006229685694503674431642175383823,487387871658733758954789679006229685694503674431645278254776⟩,⟨274155677808037739412069194441004198203158316867798723653397,274155677808037739412069194441004198203158316867800469018313⟩,⟨121846967914683439738697419751557421423625918607910543845954,121846967914683439738697419751557421423625918607911319563697⟩,⟨30461741978670859934674354937889355355906479651977635961487,30461741978670859934674354937889355355906479651977829890927⟩,⟨-2,4⟩,⟨30461741978670859934674354937889355355906479651977635961487,30461741978670859934674354937889355355906479651977829890927⟩,⟨121846967914683439738697419751557421423625918607910543845955,121846967914683439738697419751557421423625918607911319563698⟩,⟨274155677808037739412069194441004198203158316867798723653398,274155677808037739412069194441004198203158316867800469018314⟩,⟨487387871658733758954789679006229685694503674431642175383825,487387871658733758954789679006229685694503674431645278254778⟩,⟨761543549466771498366858873447233883897661991299440899037223,761543549466771498366858873447233883897661991299445747273085⟩,⟨1096622711232150957648276777764016792812633267471194894613607,1096622711232150957648276777764016792812633267471201876073243⟩,⟨1492625356954872136799043391956578412439417502946904162112962,1492625356954872136799043391956578412439417502946913664655240⟩,⟨1949551486634935035819158716024918742778014697726568701535304,1949551486634935035819158716024918742778014697726581113019091⟩,⟨2467401100272339654708622749969037783828424851810188512880627,2467401100272339654708622749969037783828424851810204221164791⟩,⟨3046174197867085993467435493788935535590647965197763596148914,3046174197867085993467435493788935535590647965197782989092326⟩,⟨3685870779419174052095596947484611998064684037889293951340194,3685870779419174052095596947484611998064684037889317416801717⟩,⟨4386490844928603830593107111056067171250533069884779578454436,4386490844928603830593107111056067171250533069884807504292942⟩,⟨5148034394395375328959965984503301055148195061184220477491675,5148034394395375328959965984503301055148195061184253251566025⟩,⟨5970501427819488547196173567826313649757670011787616648451873,5970501427819488547196173567826313649757670011787654658620946⟩,⟨6853891945200943485301729861025104955078957921694968091335069,6853891945200943485301729861025104955078957921695011725457723⟩]
def curvatureData00_1 : Fin 31 → RI := ![⟨6853891945200943485301729861025104955078957921694968091328045,6853891945200943485301729861025104955078957921695011725457718⟩,⟨5970501427819488547196173567826313649757670011787616648445754,5970501427819488547196173567826313649757670011787654658620941⟩,⟨5148034394395375328959965984503301055148195061184220477486399,5148034394395375328959965984503301055148195061184253251566020⟩,⟨4386490844928603830593107111056067171250533069884779578449941,4386490844928603830593107111056067171250533069884807504292938⟩,⟨3685870779419174052095596947484611998064684037889293951336415,3685870779419174052095596947484611998064684037889317416801713⟩,⟨3046174197867085993467435493788935535590647965197763596145791,3046174197867085993467435493788935535590647965197782989092322⟩,⟨2467401100272339654708622749969037783828424851810188512878084,2467401100272339654708622749969037783828424851810204221164776⟩,⟨1949551486634935035819158716024918742778014697726568701533305,1949551486634935035819158716024918742778014697726581113019088⟩,⟨1492625356954872136799043391956578412439417502946904162111431,1492625356954872136799043391956578412439417502946913664655238⟩,⟨1096622711232150957648276777764016792812633267471194894612482,1096622711232150957648276777764016792812633267471201876073241⟩,⟨761543549466771498366858873447233883897661991299440899036442,761543549466771498366858873447233883897661991299445747273083⟩,⟨487387871658733758954789679006229685694503674431642175383324,487387871658733758954789679006229685694503674431645278254776⟩,⟨274155677808037739412069194441004198203158316867798723653116,274155677808037739412069194441004198203158316867800469018313⟩,⟨121846967914683439738697419751557421423625918607910543845829,121846967914683439738697419751557421423625918607911319563697⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨-2,4⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨121846967914683439738697419751557421423625918607910543845830,121846967914683439738697419751557421423625918607911319563698⟩,⟨274155677808037739412069194441004198203158316867798723653117,274155677808037739412069194441004198203158316867800469018314⟩,⟨487387871658733758954789679006229685694503674431642175383326,487387871658733758954789679006229685694503674431645278254778⟩,⟨761543549466771498366858873447233883897661991299440899036444,761543549466771498366858873447233883897661991299445747273085⟩,⟨1096622711232150957648276777764016792812633267471194894612484,1096622711232150957648276777764016792812633267471201876073243⟩,⟨1492625356954872136799043391956578412439417502946904162111434,1492625356954872136799043391956578412439417502946913664655240⟩,⟨1949551486634935035819158716024918742778014697726568701533308,1949551486634935035819158716024918742778014697726581113019091⟩,⟨2467401100272339654708622749969037783828424851810188512878100,2467401100272339654708622749969037783828424851810204221164791⟩,⟨3046174197867085993467435493788935535590647965197763596145795,3046174197867085993467435493788935535590647965197782989092326⟩,⟨3685870779419174052095596947484611998064684037889293951336419,3685870779419174052095596947484611998064684037889317416801717⟩,⟨4386490844928603830593107111056067171250533069884779578449945,4386490844928603830593107111056067171250533069884807504292942⟩,⟨5148034394395375328959965984503301055148195061184220477486404,5148034394395375328959965984503301055148195061184253251566025⟩,⟨5970501427819488547196173567826313649757670011787616648445759,5970501427819488547196173567826313649757670011787654658620946⟩,⟨6853891945200943485301729861025104955078957921694968091328051,6853891945200943485301729861025104955078957921695011725457723⟩]
def curvatureData00_2 : Fin 31 → RI := ![⟨6853891945200943485301729861025104955078957921694968091328045,6853891945200943485301729861025104955078957921695011725457718⟩,⟨5970501427819488547196173567826313649757670011787616648445754,5970501427819488547196173567826313649757670011787654658620941⟩,⟨5148034394395375328959965984503301055148195061184220477486399,5148034394395375328959965984503301055148195061184253251566020⟩,⟨4386490844928603830593107111056067171250533069884779578449941,4386490844928603830593107111056067171250533069884807504292938⟩,⟨3685870779419174052095596947484611998064684037889293951336415,3685870779419174052095596947484611998064684037889317416801713⟩,⟨3046174197867085993467435493788935535590647965197763596145791,3046174197867085993467435493788935535590647965197782989092322⟩,⟨2467401100272339654708622749969037783828424851810188512878084,2467401100272339654708622749969037783828424851810204221164776⟩,⟨1949551486634935035819158716024918742778014697726568701533305,1949551486634935035819158716024918742778014697726581113019088⟩,⟨1492625356954872136799043391956578412439417502946904162111431,1492625356954872136799043391956578412439417502946913664655238⟩,⟨1096622711232150957648276777764016792812633267471194894612482,1096622711232150957648276777764016792812633267471201876073241⟩,⟨761543549466771498366858873447233883897661991299440899036442,761543549466771498366858873447233883897661991299445747273083⟩,⟨487387871658733758954789679006229685694503674431642175383324,487387871658733758954789679006229685694503674431645278254776⟩,⟨274155677808037739412069194441004198203158316867798723653116,274155677808037739412069194441004198203158316867800469018313⟩,⟨121846967914683439738697419751557421423625918607910543845829,121846967914683439738697419751557421423625918607911319563697⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨-2,4⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨121846967914683439738697419751557421423625918607910543845830,121846967914683439738697419751557421423625918607911319563698⟩,⟨274155677808037739412069194441004198203158316867798723653117,274155677808037739412069194441004198203158316867800469018314⟩,⟨487387871658733758954789679006229685694503674431642175383326,487387871658733758954789679006229685694503674431645278254778⟩,⟨761543549466771498366858873447233883897661991299440899036444,761543549466771498366858873447233883897661991299445747273085⟩,⟨1096622711232150957648276777764016792812633267471194894612484,1096622711232150957648276777764016792812633267471201876073243⟩,⟨1492625356954872136799043391956578412439417502946904162111434,1492625356954872136799043391956578412439417502946913664655240⟩,⟨1949551486634935035819158716024918742778014697726568701533308,1949551486634935035819158716024918742778014697726581113019091⟩,⟨2467401100272339654708622749969037783828424851810188512878100,2467401100272339654708622749969037783828424851810204221164791⟩,⟨3046174197867085993467435493788935535590647965197763596145795,3046174197867085993467435493788935535590647965197782989092326⟩,⟨3685870779419174052095596947484611998064684037889293951336419,3685870779419174052095596947484611998064684037889317416801717⟩,⟨4386490844928603830593107111056067171250533069884779578449945,4386490844928603830593107111056067171250533069884807504292942⟩,⟨5148034394395375328959965984503301055148195061184220477486404,5148034394395375328959965984503301055148195061184253251566025⟩,⟨5970501427819488547196173567826313649757670011787616648445759,5970501427819488547196173567826313649757670011787654658620946⟩,⟨6853891945200943485301729861025104955078957921694968091328051,6853891945200943485301729861025104955078957921695011725457723⟩]
def curvatureData00_3 : Fin 31 → RI := ![⟨6853891945200943485301729861025104955078957921694968091328045,6853891945200943485301729861025104955078957921695011725457718⟩,⟨5970501427819488547196173567826313649757670011787616648445754,5970501427819488547196173567826313649757670011787654658620941⟩,⟨5148034394395375328959965984503301055148195061184220477486399,5148034394395375328959965984503301055148195061184253251566020⟩,⟨4386490844928603830593107111056067171250533069884779578449941,4386490844928603830593107111056067171250533069884807504292938⟩,⟨3685870779419174052095596947484611998064684037889293951336415,3685870779419174052095596947484611998064684037889317416801713⟩,⟨3046174197867085993467435493788935535590647965197763596145791,3046174197867085993467435493788935535590647965197782989092322⟩,⟨2467401100272339654708622749969037783828424851810188512878084,2467401100272339654708622749969037783828424851810204221164776⟩,⟨1949551486634935035819158716024918742778014697726568701533305,1949551486634935035819158716024918742778014697726581113019088⟩,⟨1492625356954872136799043391956578412439417502946904162111431,1492625356954872136799043391956578412439417502946913664655238⟩,⟨1096622711232150957648276777764016792812633267471194894612482,1096622711232150957648276777764016792812633267471201876073241⟩,⟨761543549466771498366858873447233883897661991299440899036442,761543549466771498366858873447233883897661991299445747273083⟩,⟨487387871658733758954789679006229685694503674431642175383324,487387871658733758954789679006229685694503674431645278254776⟩,⟨274155677808037739412069194441004198203158316867798723653116,274155677808037739412069194441004198203158316867800469018313⟩,⟨121846967914683439738697419751557421423625918607910543845829,121846967914683439738697419751557421423625918607911319563697⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨-2,4⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨121846967914683439738697419751557421423625918607910543845830,121846967914683439738697419751557421423625918607911319563698⟩,⟨274155677808037739412069194441004198203158316867798723653117,274155677808037739412069194441004198203158316867800469018314⟩,⟨487387871658733758954789679006229685694503674431642175383326,487387871658733758954789679006229685694503674431645278254778⟩,⟨761543549466771498366858873447233883897661991299440899036444,761543549466771498366858873447233883897661991299445747273085⟩,⟨1096622711232150957648276777764016792812633267471194894612484,1096622711232150957648276777764016792812633267471201876073243⟩,⟨1492625356954872136799043391956578412439417502946904162111434,1492625356954872136799043391956578412439417502946913664655240⟩,⟨1949551486634935035819158716024918742778014697726568701533308,1949551486634935035819158716024918742778014697726581113019091⟩,⟨2467401100272339654708622749969037783828424851810188512878100,2467401100272339654708622749969037783828424851810204221164791⟩,⟨3046174197867085993467435493788935535590647965197763596145795,3046174197867085993467435493788935535590647965197782989092326⟩,⟨3685870779419174052095596947484611998064684037889293951336419,3685870779419174052095596947484611998064684037889317416801717⟩,⟨4386490844928603830593107111056067171250533069884779578449945,4386490844928603830593107111056067171250533069884807504292942⟩,⟨5148034394395375328959965984503301055148195061184220477486404,5148034394395375328959965984503301055148195061184253251566025⟩,⟨5970501427819488547196173567826313649757670011787616648445759,5970501427819488547196173567826313649757670011787654658620946⟩,⟨6853891945200943485301729861025104955078957921694968091328051,6853891945200943485301729861025104955078957921695011725457723⟩]
def curvatureData00_4 : Fin 31 → RI := ![⟨6853891945200943485301729861025104955078957921694968091328045,6853891945200943485301729861025104955078957921695011725457718⟩,⟨5970501427819488547196173567826313649757670011787616648445754,5970501427819488547196173567826313649757670011787654658620941⟩,⟨5148034394395375328959965984503301055148195061184220477486399,5148034394395375328959965984503301055148195061184253251566020⟩,⟨4386490844928603830593107111056067171250533069884779578449941,4386490844928603830593107111056067171250533069884807504292938⟩,⟨3685870779419174052095596947484611998064684037889293951336415,3685870779419174052095596947484611998064684037889317416801713⟩,⟨3046174197867085993467435493788935535590647965197763596145791,3046174197867085993467435493788935535590647965197782989092322⟩,⟨2467401100272339654708622749969037783828424851810188512878084,2467401100272339654708622749969037783828424851810204221164776⟩,⟨1949551486634935035819158716024918742778014697726568701533305,1949551486634935035819158716024918742778014697726581113019088⟩,⟨1492625356954872136799043391956578412439417502946904162111431,1492625356954872136799043391956578412439417502946913664655238⟩,⟨1096622711232150957648276777764016792812633267471194894612482,1096622711232150957648276777764016792812633267471201876073241⟩,⟨761543549466771498366858873447233883897661991299440899036442,761543549466771498366858873447233883897661991299445747273083⟩,⟨487387871658733758954789679006229685694503674431642175383324,487387871658733758954789679006229685694503674431645278254776⟩,⟨274155677808037739412069194441004198203158316867798723653116,274155677808037739412069194441004198203158316867800469018313⟩,⟨121846967914683439738697419751557421423625918607910543845829,121846967914683439738697419751557421423625918607911319563697⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨-2,4⟩,⟨30461741978670859934674354937889355355906479651977635961455,30461741978670859934674354937889355355906479651977829890927⟩,⟨121846967914683439738697419751557421423625918607910543845830,121846967914683439738697419751557421423625918607911319563698⟩,⟨274155677808037739412069194441004198203158316867798723653117,274155677808037739412069194441004198203158316867800469018314⟩,⟨487387871658733758954789679006229685694503674431642175383326,487387871658733758954789679006229685694503674431645278254778⟩,⟨761543549466771498366858873447233883897661991299440899036444,761543549466771498366858873447233883897661991299445747273085⟩,⟨1096622711232150957648276777764016792812633267471194894612484,1096622711232150957648276777764016792812633267471201876073243⟩,⟨1492625356954872136799043391956578412439417502946904162111434,1492625356954872136799043391956578412439417502946913664655240⟩,⟨1949551486634935035819158716024918742778014697726568701533308,1949551486634935035819158716024918742778014697726581113019091⟩,⟨2467401100272339654708622749969037783828424851810188512878100,2467401100272339654708622749969037783828424851810204221164791⟩,⟨3046174197867085993467435493788935535590647965197763596145795,3046174197867085993467435493788935535590647965197782989092326⟩,⟨3685870779419174052095596947484611998064684037889293951336419,3685870779419174052095596947484611998064684037889317416801717⟩,⟨4386490844928603830593107111056067171250533069884779578449945,4386490844928603830593107111056067171250533069884807504292942⟩,⟨5148034394395375328959965984503301055148195061184220477486404,5148034394395375328959965984503301055148195061184253251566025⟩,⟨5970501427819488547196173567826313649757670011787616648445759,5970501427819488547196173567826313649757670011787654658620946⟩,⟨6853891945200943485301729861025104955078957921694968091328051,6853891945200943485301729861025104955078957921695011725457723⟩]
def curvatureTable00 : Fin 5 → Fin 31 → RI := ![curvatureData00_0,curvatureData00_1,curvatureData00_2,curvatureData00_3,curvatureData00_4]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvatureData01_0 : Fin 31 → RI := ![⟨24434706212943770910671192985539581471000472160262931606423330,24434706212943770910671192985539581471000472160263087165773107⟩,⟨28933471749921817559947782476563968170281578176186045104140302,28933471749921817559947782476563968170281578176186229304106312⟩,⟨34575203872566002581882653525004687093957180968000673194651162,34575203872566002581882653525004687093957180968000893311733582⟩,⟨41718832100522755805876473385178615210106493814880312869730858,41718832100522755805876473385178615210106493814880578465492459⟩,⟨50850803608378037790677595798057107522266026102733455776249252,50850803608378037790677595798057107522266026102733779509135004⟩,⟨62629472193697144201300870408955720895827884691984424237840042,62629472193697144201300870408955720895827884691984822957592104⟩,⟨77937566317170450108750302754669124546537830880894060187284351,77937566317170450108750302754669124546537830880894556363382699⟩,⟨97931263180800673897290503482411552022107158482347820854330090,97931263180800673897290503482411552022107158482348444316857286⟩,⟨124051105916993446529972251451940564147475582495848581558319580,124051105916993446529972251451940564147475582495849371308329986⟩,⟨157910093810840362176147317576583957648232093888063649897333876,157910093810840362176147317576583957648232093888064655204762441⟩,⟨200886609846766333891890032837946195638759693236495882813453911,200886609846766333891890032837946195638759693236497161723477221⟩,⟨253153845100863801611637024243429742038496060650697906078250779,253153845100863801611637024243429742038496060650699517738633947⟩,⟨311953718656290415546697309862431449250792094229518369713807951,311953718656290415546697309862431449250792094229520355713462531⟩,⟨369617770731914730723732256459036100170597252288154310995018306,369617770731914730723732256459036100170597252288156664102938426⟩,⟨413405680673738651581049488689514170998406929305087575129524222,413405680673738651581049488689514170998406929305090207005638203⟩,⟨429968610151373277648670923375886333653255280947267963596360384,429968610151373277648670923375886333653255280947270700917514455⟩,⟨413405680673738651581049488689514170998406929305087575129524592,413405680673738651581049488689514170998406929305090207005638573⟩,⟨369617770731914730723732256459036100170597252288154310995018993,369617770731914730723732256459036100170597252288156664102938998⟩,⟨311953718656290415546697309862431449250792094229518369713804000,311953718656290415546697309862431449250792094229520355713463349⟩,⟨253153845100863801611637024243429742038496060650697906078251492,253153845100863801611637024243429742038496060650699517738634660⟩,⟨200886609846766333891890032837946195638759693236495882813454599,200886609846766333891890032837946195638759693236497161723474327⟩,⟨157910093810840362176147317576583957648232093888063649897334332,157910093810840362176147317576583957648232093888064655204762962⟩,⟨124051105916993446529972251451940564147475582495848581558319023,124051105916993446529972251451940564147475582495849371308330319⟩,⟨97931263180800673897290503482411552022107158482347820854330374,97931263180800673897290503482411552022107158482348444316857618⟩,⟨77937566317170450108750302754669124546537830880894060187284308,77937566317170450108750302754669124546537830880894556363381926⟩,⟨62629472193697144201300870408955720895827884691984424237839716,62629472193697144201300870408955720895827884691984822957591766⟩,⟨50850803608378037790677595798057107522266026102733455776249040,50850803608378037790677595798057107522266026102733779509135189⟩,⟨41718832100522755805876473385178615210106493814880312869730826,41718832100522755805876473385178615210106493814880578465492292⟩,⟨34575203872566002581882653525004687093957180968000673194651233,34575203872566002581882653525004687093957180968000893311733492⟩,⟨28933471749921817559947782476563968170281578176186045104140239,28933471749921817559947782476563968170281578176186229304106251⟩,⟨24434706212943770910671192985539581471000472160262931606423277,24434706212943770910671192985539581471000472160263087165773164⟩]
def curvatureData01_1 : Fin 31 → RI := ![⟨12255623128756475251945024771555026538949445419036753895973473,12255623128756475251945024771555026538949445419036858873780908⟩,⟨11664831693501205286361448527182910923844477801977653423753088,11664831693501205286361448527182910923844477801977761475636615⟩,⟨10764162788205715469084123943941070557921967008592769545256486,10764162788205715469084123943941070557921967008592878147021228⟩,⟨9545806136990350353471232351746536661232585165386506988195028,9545806136990350353471232351746536661232585165386612702826445⟩,⟨8043983010713230470218579933501914214043677274027998892889725,8043983010713230470218579933501914214043677274028097488314265⟩,⟨6349383801820873272272960888924591053115713199596408313236353,6349383801820873272272960888924591053115713199596495202542926⟩,⟨4611560691642447779934264869912324461625125573291386457223396,4611560691642447779934264869912324461625125573291457548405932⟩,⟨3016765977213692365342868223884005784289099307593200730495747,3016765977213692365342868223884005784289099307593253582147292⟩,⟨1735834309932371476825160347987977861918850558891119490409057,1735834309932371476825160347987977861918850558891154327575220⟩,⟨859171947941473418976057841955741419607248362952628133403293,859171947941473418976057841955741419607248362952648007994397⟩,⟨361496648763264338934409798923104443251540169487896225119136,361496648763264338934409798923104443251540169487905889427576⟩,⟨131307701678736870678795322435967826548836621632530408864171,131307701678736870678795322435967826548836621632534453444525⟩,⟨44063493900140271764306051301948125293168357918640454909148,44063493900140271764306051301948125293168357918642000536593⟩,⟨15755166312881650925093750415837423408511882518860282603162,15755166312881650925093750415837423408511882518860897588653⟩,⟨7394479382503485209934319694098947309461032642930135991429,7394479382503485209934319694098947309461032642930445918162⟩,⟨5582506097753102943736245827407590701657690987526335390200,5582506097753102943736245827407590701657690987526575315548⟩,⟨7394479382503485209934319694098947309461032642930135991429,7394479382503485209934319694098947309461032642930445918162⟩,⟨15755166312881650925093750415837423408511882518860282603162,15755166312881650925093750415837423408511882518860897588653⟩,⟨44063493900140271764306051301948125293168357918640454909147,44063493900140271764306051301948125293168357918642000536593⟩,⟨131307701678736870678795322435967826548836621632530408864171,131307701678736870678795322435967826548836621632534453444526⟩,⟨361496648763264338934409798923104443251540169487896225119138,361496648763264338934409798923104443251540169487905889427571⟩,⟨859171947941473418976057841955741419607248362952628133403295,859171947941473418976057841955741419607248362952648007994399⟩,⟨1735834309932371476825160347987977861918850558891119490409049,1735834309932371476825160347987977861918850558891154327575225⟩,⟨3016765977213692365342868223884005784289099307593200730495756,3016765977213692365342868223884005784289099307593253582147302⟩,⟨4611560691642447779934264869912324461625125573291386457223394,4611560691642447779934264869912324461625125573291457548405886⟩,⟨6349383801820873272272960888924591053115713199596408313236320,6349383801820873272272960888924591053115713199596495202542891⟩,⟨8043983010713230470218579933501914214043677274027998892889691,8043983010713230470218579933501914214043677274028097488314294⟩,⟨9545806136990350353471232351746536661232585165386506988195020,9545806136990350353471232351746536661232585165386612702826407⟩,⟨10764162788205715469084123943941070557921967008592769545256509,10764162788205715469084123943941070557921967008592878147021200⟩,⟨11664831693501205286361448527182910923844477801977653423753063,11664831693501205286361448527182910923844477801977761475636590⟩,⟨12255623128756475251945024771555026538949445419036753895973446,12255623128756475251945024771555026538949445419036858873780937⟩]
def curvatureData01_2 : Fin 31 → RI := ![⟨6147006514633075942601367336762103108747750444012795085681784,6147006514633075942601367336762103108747750444012861294947630⟩,⟨4702798876463135577865254024543197717583837347121245152716050,4702798876463135577865254024543197717583837347121302386060368⟩,⟨3351164636889631894104931596462230250645498821333925505911753,3351164636889631894104931596462230250645498821333971849399466⟩,⟨2184203397291671318184920439872816158039481842993978787070257,2184203397291671318184920439872816158039481842994013318802838⟩,⟨1272460965906591132225220081417338643201331253767475514399477,1272460965906591132225220081417338643201331253767498660804111⟩,⟨643701331828921962221321529012873294445965467556253909341149,643701331828921962221321529012873294445965467556267471251336⟩,⟨272865743923242618558924831903771304669872739981416445610350,272865743923242618558924831903771304669872739981423148730352⟩,⟨92931273075402360995812201471353917377635718018865295889142,92931273075402360995812201471353917377635718018867974580406⟩,⟨24289350177616050618299644347417625918715121394143212204464,24289350177616050618299644347417625918715121394144038090569⟩,⟨4674662767370675029625849737801580554168244568250558505592,4674662767370675029625849737801580554168244568250746620979⟩,⟨650515368678637961536206844778320319703937389608684069342,650515368678637961536206844778320319703937389608715039662⟩,⟨68107646215219687815249680579429109096824849136511190703,68107646215219687815249680579429109096824849136515003136⟩,⟨6223972911914340989999205569149569736635127740880853352,6223972911914340989999205569149569736635127740881257338⟩,⟨671572865814938286133897082721789632136409952537598044,671572865814938286133897082721789632136409952537648153⟩,⟨132263120451461497832798125613404419467331323840840912,132263120451461497832798125613404419467331323840852504⟩,⟨72480580199747497774329401467262755209941397270828684,72480580199747497774329401467262755209941397270836026⟩,⟨132263120451461497832798125613404419467331323840840912,132263120451461497832798125613404419467331323840852504⟩,⟨671572865814938286133897082721789632136409952537598044,671572865814938286133897082721789632136409952537648153⟩,⟨6223972911914340989999205569149569736635127740880853352,6223972911914340989999205569149569736635127740881257338⟩,⟨68107646215219687815249680579429109096824849136511190703,68107646215219687815249680579429109096824849136515003136⟩,⟨650515368678637961536206844778320319703937389608684069342,650515368678637961536206844778320319703937389608715039662⟩,⟨4674662767370675029625849737801580554168244568250558505592,4674662767370675029625849737801580554168244568250746620979⟩,⟨24289350177616050618299644347417625918715121394143212204464,24289350177616050618299644347417625918715121394144038090569⟩,⟨92931273075402360995812201471353917377635718018865295889142,92931273075402360995812201471353917377635718018867974580407⟩,⟨272865743923242618558924831903771304669872739981416445610350,272865743923242618558924831903771304669872739981423148730349⟩,⟨643701331828921962221321529012873294445965467556253909341146,643701331828921962221321529012873294445965467556267471251332⟩,⟨1272460965906591132225220081417338643201331253767475514399471,1272460965906591132225220081417338643201331253767498660804116⟩,⟨2184203397291671318184920439872816158039481842993978787070255,2184203397291671318184920439872816158039481842994013318802829⟩,⟨3351164636889631894104931596462230250645498821333925505911759,3351164636889631894104931596462230250645498821333971849399457⟩,⟨4702798876463135577865254024543197717583837347121245152716040,4702798876463135577865254024543197717583837347121302386060359⟩,⟨6147006514633075942601367336762103108747750444012795085681770,6147006514633075942601367336762103108747750444012861294947644⟩]
def curvatureData01_3 : Fin 31 → RI := ![⟨1103486746271424008928391885435094288530092953548397551396,1103486746271424008928391885435094288530092953548440413769⟩,⟨55059278508684906964327495688573652038217598180756215536,55059278508684906964327495688573652038217598180758934839⟩,⟨1550206692706909044879122016900960697740625390787270345,1550206692706909044879122016900960697740625390787366619⟩,⟨21517852669565976886737258381172789265415984864159136,21517852669565976886737258381172789265415984864160901⟩,⟨124254183521428679732772667205007888744273764059515,124254183521428679732772667205007888744273764059670⟩,⟨241598791454639983393999323854382775450175248051,241598791454639983393999323854382775450175248240⟩,⟨122239797166112275565640399214611343728007299,122239797166112275565640399214611343728007533⟩,⟨11910094322486298905198663285561826361203,11910094322486298905198663285561826361498⟩,⟨161905366668708053942760279151018576,161905366668708053942760279151018949⟩,⟨232074675639099651132300605775,232074675639099651132300606250⟩,⟨31818055462944312056606,31818055462944312057210⟩,⟨588188821747781,588188821748541⟩,⟨4665267,4666204⟩,⟨-370,740⟩,⟨-414,827⟩,⟨-430,860⟩,⟨-414,827⟩,⟨-370,740⟩,⟨4665267,4666204⟩,⟨588188821747781,588188821748541⟩,⟨31818055462944312056606,31818055462944312057210⟩,⟨232074675639099651132300605775,232074675639099651132300606250⟩,⟨161905366668708053942760279151018576,161905366668708053942760279151018949⟩,⟨11910094322486298905198663285561826361203,11910094322486298905198663285561826361498⟩,⟨122239797166112275565640399214611343728007299,122239797166112275565640399214611343728007533⟩,⟨241598791454639983393999323854382775450175248051,241598791454639983393999323854382775450175248240⟩,⟨124254183521428679732772667205007888744273764059515,124254183521428679732772667205007888744273764059670⟩,⟨21517852669565976886737258381172789265415984864159136,21517852669565976886737258381172789265415984864160901⟩,⟨1550206692706909044879122016900960697740625390787270345,1550206692706909044879122016900960697740625390787366619⟩,⟨55059278508684906964327495688573652038217598180756215536,55059278508684906964327495688573652038217598180758934839⟩,⟨1103486746271424008928391885435094288530092953548397551396,1103486746271424008928391885435094288530092953548440413769⟩]
def curvatureData01_4 : Fin 31 → RI := ![⟨3130094618727568550931508859192676937094371810571124724,3130094618727568550931508859192676937094371810571307827⟩,⟨24400173317437620466607050079258256772876553786721386,24400173317437620466607050079258256772876553786723307⟩,⟨76334597646994146219481442650331529815142998989117,76334597646994146219481442650331529815142998989223⟩,⟨77336214213867363837240026783136651316480538249,77336214213867363837240026783136651316480538375⟩,⟨19376898963332861247168739909265640270903272,19376898963332861247168739909265640270903425⟩,⟨858408076959142623974166739250542693848,858408076959142623974166739250542694037⟩,⟨4467575196197407428229575959365047,4467575196197407428229575959365282⟩,⟨1695069285668308034587081602,1695069285668308034587081896⟩,⟨28149849769923765778,28149849769923766151⟩,⟨13146932135,13146932610⟩,⟨-201,402⟩,⟨-254,507⟩,⟨-312,624⟩,⟨-370,740⟩,⟨-414,827⟩,⟨-430,860⟩,⟨-414,827⟩,⟨-370,740⟩,⟨-312,624⟩,⟨-254,507⟩,⟨-201,402⟩,⟨13146932135,13146932610⟩,⟨28149849769923765778,28149849769923766151⟩,⟨1695069285668308034587081602,1695069285668308034587081896⟩,⟨4467575196197407428229575959365047,4467575196197407428229575959365282⟩,⟨858408076959142623974166739250542693848,858408076959142623974166739250542694037⟩,⟨19376898963332861247168739909265640270903272,19376898963332861247168739909265640270903425⟩,⟨77336214213867363837240026783136651316480538249,77336214213867363837240026783136651316480538375⟩,⟨76334597646994146219481442650331529815142998989117,76334597646994146219481442650331529815142998989223⟩,⟨24400173317437620466607050079258256772876553786721386,24400173317437620466607050079258256772876553786723307⟩,⟨3130094618727568550931508859192676937094371810571124724,3130094618727568550931508859192676937094371810571307827⟩]
def curvatureTable01 : Fin 5 → Fin 31 → RI := ![curvatureData01_0,curvatureData01_1,curvatureData01_2,curvatureData01_3,curvatureData01_4]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvatureData11_3 : Fin 31 → RI := ![⟨311467012276899448323139231917091766199391223710496922,311467012276899448323139231917091766199391223710517200⟩,⟨12882416568673153993447378907705244175880317362127966,12882416568673153993447378907705244175880317362129002⟩,⟨348675156843208364088016711832801915028215021634336,348675156843208364088016711832801915028215021634425⟩,⟨5865827861477831774565132741854226312431100180085,5865827861477831774565132741854226312431100180160⟩,⟨58365176326034570070869738088021702798719766842,58365176326034570070869738088021702798719766929⟩,⟨329486531580404022218130256622928058963301022,329486531580404022218130256622928058963301123⟩,⟨1030852379143930764154752227119231192329844,1030852379143930764154752227119231192329961⟩,⟨1804745185814079676450878416279368549391,1804745185814079676450878416279368549526⟩,⟨1883522219149661822326371306056274800,1883522219149661822326371306056274956⟩,⟨1350698473084867200532817884940762,1350698473084867200532817884940941⟩,⟨851537495825317095981264299566,851537495825317095981264299770⟩,⟨681509623292578586107002019,681509623292578586107002247⟩,⟨1120561382019317769846059,1120561382019317769846311⟩,⟨6556666474771068291847,6556666474771068292118⟩,⟨231199583428524638167,231199583428524638451⟩,⟨72296155941742355381,72296155941742355669⟩,⟨231199583428524638167,231199583428524638451⟩,⟨6556666474771068291847,6556666474771068292118⟩,⟨1120561382019317769846059,1120561382019317769846311⟩,⟨681509623292578586107002019,681509623292578586107002247⟩,⟨851537495825317095981264299566,851537495825317095981264299770⟩,⟨1350698473084867200532817884940762,1350698473084867200532817884940941⟩,⟨1883522219149661822326371306056274800,1883522219149661822326371306056274956⟩,⟨1804745185814079676450878416279368549391,1804745185814079676450878416279368549526⟩,⟨1030852379143930764154752227119231192329844,1030852379143930764154752227119231192329961⟩,⟨329486531580404022218130256622928058963301022,329486531580404022218130256622928058963301123⟩,⟨58365176326034570070869738088021702798719766842,58365176326034570070869738088021702798719766929⟩,⟨5865827861477831774565132741854226312431100180085,5865827861477831774565132741854226312431100180160⟩,⟨348675156843208364088016711832801915028215021634336,348675156843208364088016711832801915028215021634425⟩,⟨12882416568673153993447378907705244175880317362127966,12882416568673153993447378907705244175880317362129002⟩,⟨311467012276899448323139231917091766199391223710496922,311467012276899448323139231917091766199391223710517200⟩]
def curvatureData11_4 : Fin 31 → RI := ![⟨9296051911237295477869632416860708942584590420101,9296051911237295477869632416860708942584590420151⟩,⟨54886098130291998057643879023624251717867079582,54886098130291998057643879023624251717867079639⟩,⟨164996541655775408040335684222004891576008442,164996541655775408040335684222004891576008508⟩,⟨232796281652949854900593861390408058017569,232796281652949854900593861390408058017644⟩,⟨142530506071582726747612384204017285877,142530506071582726747612384204017285964⟩,⟨35469635794612308790294752399514470,35469635794612308790294752399514571⟩,⟨3459337020011874947742449616790,3459337020011874947742449616907⟩,⟨134400722161580528488124310,134400722161580528488124445⟩,⟨2302800193514175822326,2302800193514175822482⟩,⟨21836407082203305,21836407082203485⟩,⟨169774848202,169774848406⟩,⟨1943126,1943355⟩,⟨-84,168⟩,⟨-90,180⟩,⟨-95,189⟩,⟨-96,192⟩,⟨-95,189⟩,⟨-90,180⟩,⟨-84,168⟩,⟨1943126,1943355⟩,⟨169774848202,169774848406⟩,⟨21836407082203305,21836407082203485⟩,⟨2302800193514175822326,2302800193514175822482⟩,⟨134400722161580528488124310,134400722161580528488124445⟩,⟨3459337020011874947742449616790,3459337020011874947742449616907⟩,⟨35469635794612308790294752399514470,35469635794612308790294752399514571⟩,⟨142530506071582726747612384204017285877,142530506071582726747612384204017285964⟩,⟨232796281652949854900593861390408058017569,232796281652949854900593861390408058017644⟩,⟨164996541655775408040335684222004891576008442,164996541655775408040335684222004891576008508⟩,⟨54886098130291998057643879023624251717867079582,54886098130291998057643879023624251717867079639⟩,⟨9296051911237295477869632416860708942584590420101,9296051911237295477869632416860708942584590420151⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvatureColumn1_2 : Fin 22 → RI := ![⟨492737994145033258700847028046463667588492418873980399900044,492737994145033258700847028050440491097563524774734674439459⟩,⟨2088225632928948965862684975488287924817843951890290961125088,2088225632928948965862684975488288068920447118821604914009135⟩,⟨373259149351668988056358864045218250189980081629738817969576,373259149351668988056358864049195200175335144260500511298646⟩,⟨1730740367376542488918229535524054157407011376294068374878621,1730740367376542488918229535524058969784406138827643301889767⟩,⟨219272662534707682167763991420799780154700399892488090903117,219272662534707682167763991424782227867682253103174660269307⟩,⟨1204796664817511404320493407604269445398193685512890150121326,1204796664817511404320493407604567767730513142964726992135074⟩,⟨178686680211071685234108861684963464727159670710887448489495,178686680211071685234108861688951745768145011599439292576608⟩,⟨1021065582736533232735111218482377889096478055674461397327563,1021065582736533232735111218483035447415013645602860319770280⟩,⟨150101691034635769719078825107773978472035350010418773478875,150101691034635769719078825111752112037074136280076271457321⟩,⟨768863569952289287926862957712573757772030933970583739067370,768863569952289287926862957712632760930932724388281382835873⟩,⟨198469835165894648430327472150392663053309590747421413645226,198469835165894648430327472154369486381987855089091999344079⟩,⟨834494366484370953353125088747187130385162605937530597745682,834494366484370953353125088747950906379540149131122186007742⟩,⟨294188263747599027157576910856834958495359851064983130884618,294188263747599027157576910860817524454698224763826032828141⟩,⟨1135548606651355606860482908266551594232553299527499636403108,1135548606651355606860482908268017408079263282959352781623739⟩,⟨371385030865852095875809226481846514902983741735185942181989,371385030865852095875809226485835314301186787736098384090502⟩,⟨1411179907701577172759281232326094485496625845649448157584513,1411179907701577172759281232326713078263324436152987205493851⟩,⟨689198484301338120805034581534468972446045660363658863837789,689198484301338120805034581538447019802160348578856082547394⟩,⟨2432278457694674313559771427280971762529699907023985993746813,2432278457694674313559771427281030285293109522087730778178041⟩,⟨977312728288406147189024143737030731493125833943428704124525,977312728288406147189024143741007681040864560130667115369395⟩,⟨3334579168264614880614730288335750974819194761209570545796425,3334579168264614880614730288335755853863555589647297285521655⟩,⟨1126968346473033480137737149160140766837091109860588827712525,1126968346473033480137737149164123253683200381973453232401409⟩,⟨3892280461323035124905217620209048740852949672501748608844940,3892280461323035124905217620209345115188615995110685068087506⟩]
def curvatureColumn1_3 : Fin 22 → RI := ![⟨828291193688351065221289482776556229364831097352885,828291193688351065221289483657518019560837852255545⟩,⟨59023234651583563077564286501807644410579526107038576,59023234651583563077564286501807665488871694472325990⟩,⟨821514986992793647703932763469964337554816767102428,821514986992793647703932764350927302192507881171724⟩,⟨58300047068333113679285032194627224059617204093666593,58300047068333113679285032194627975218168093954641754⟩,⟨807245979127971556650196989563876474730587402626466,807245979127971556650196990444896750215062510251413⟩,⟨56781954717707114801063844314479127287888655370811338,56781954717707114801063844314527773178852725300839792⟩,⟨799861065510841784000286263802705631310823796875988,799861065510841784000286264683790173817278747241084⟩,⟨55999929334559295782400124046843776375377214548104542,55999929334559295782400124046951904918051598273509148⟩,⟨792381090351517351169531645997916081537869248844767,792381090351517351169531646878890698658342313713051⟩,⟨55211609170930812194673482619002051087927615099543873,55211609170930812194673482619011555412401876707758614⟩,⟨807244573466176795237307810854725234698106138372522,807244573466176795237307811735687024824275615472456⟩,⟨56781046956026617019652650653619876835845309135386360,56781046956026617019652650653619898030134226043802547⟩,⟨828279377991535332502114094166439089828785638184964,828279377991535332502114095047459417961883713062077⟩,⟨59021115987766726911233527608358573531825890873866951,59021115987766726911233527608406973829222237240058202⟩,⟨834747110639239283341368853634373515552796919651387,834747110639239283341368854515458352251344366484857⟩,⟨59712676867531556757295528327508957891604456608782133,59712676867531556757295528327616671392308448075366674⟩,⟨851782656720845330124515675910226934324330289719864,851782656720845330124515676791201516279189139624652⟩,⟨61538913962159813190420892026634397545673897368232435,61538913962159813190420892026643896711483493235059028⟩,⟨864304828848271133703899648529360152712070406524289,864304828848271133703899649410323117460706971138485⟩,⟨62884815823075131562678055504605269022076259280912375,62884815823075131562678055504606020288339035320627235⟩,⟨869652553692509682954881910877302387656899972160165,869652553692509682954881911758322677636330280389834⟩,⟨63460083219929588203904981288693286943491044026426131,63460083219929588203904981288741943466566456123485412⟩]
def curvatureColumn1_4 : Fin 22 → RI := ![⟨3363994217262576426026759788738909011532115958,3363994217262576426026759815032114576133903227⟩,⟨1641702348658942796387296095868126236366780573291,1641702348658942796387296095868126853003078038708⟩,⟨3360874979691564559664658327453458167727166099,3360874979691564559664658353746668684385148024⟩,⟨1638724646252702774593086094723728011882128575789,1638724646252702774593086094723750040045954225543⟩,⟨3354275192893685854228300473131200167139716013,3354275192893685854228300499424653286477127664⟩,⟨1632427446509710339480629826955186881717697983701,1632427446509710339480629826956616894846367448539⟩,⟨3350844778800741105768102958990001255712974844,3350844778800741105768102985283727182575505922⟩,⟨1629156424562103617443300916909936099642520059103,1629156424562103617443300916913116308433823852781⟩,⟨3347361753625311826816310743325360026955249978,3347361753625311826816310769618619775086224861⟩,⟨1625837344319338801695032959870056516559762570220,1625837344319338801695032959870335895248514068416⟩,⟨3354275189524729012367889053063324012034852024,3354275189524729012367889079356529576602238880⟩,⟨1632427411850071157167235552141188504637379464678,1632427411850071157167235552141189121056405117038⟩,⟨3363994188668989003144924388286232301292948893,3363994188668989003144924414579685457019503825⟩,⟨1641702267225306201235397266577579811427347654033,1641702267225306201235397266579008841985455793190⟩,⟨3366960955963685075437729729998795678679450118,3366960955963685075437729756292521778924211533⟩,⟨1644535214707477572708230739910382443526742864052,1644535214707477572708230739913561092095918525234⟩,⟨3374726216469945217393809000283666505918872620,3374726216469945217393809026576926241310360899⟩,⟨1651953715875160642804910734195658411112439473246,1651953715875160642804910734195937786880845754239⟩,⟨3380389537948522881303619586036679798009370040,3380389537948522881303619612329890315157378183⟩,⟨1657367270612848520494907948264097688418356103821,1657367270612848520494907948264119718701097622593⟩,⟨3382797814785111546996181070700560350180601040,3382797814785111546996181096994013528823613237⟩,⟨1659670116207951544873702557793619978360077817422,1659670116207951544873702557795050333224277373680⟩]
def curvatureTail1 : RI := ⟨1146570904437445124234805277954807889641704200443903319238089820,1146570904437445124234805277954807889641704200443912235954319601⟩
lemma curvatureTail1_calc : ((curvatureTable00 1 30).add (curvatureTable01 1 30)).mul (RI.point 60)=curvatureTail1 := by decide +kernel
def curvatureTail2 : RI := ⟨780053907590041165674185831867232483829602501942465790620589260,780053907590041165674185831867232483829602501942472381224322021⟩
lemma curvatureTail2_calc : ((curvatureTable00 2 30).add (curvatureTable01 2 30)).mul (RI.point 60)=curvatureTail2 := by decide +kernel
def curvatureConstant3 : RI := ⟨1215198976953092218551294390379033113285331535323125796493,1215198976953092218551294390379033113285331535325211480446⟩
def curvatureTail3 : RI := ⟨411299725916832894558639495174632402962049280878910989332766820,411299725916832894558639495174632402962049280878913609952289521⟩
lemma curvatureTail3_calc : ((curvatureTable00 3 30).add (curvatureTable01 3 30)).mul (RI.point 60)=curvatureTail3 := by decide +kernel
def curvatureTail4 : RI := ⟨411233704517733732772216847552037848865353700964006719747166500,411233704517733732772216847552037848865353700964009337805933001⟩
lemma curvatureTail4_calc : ((curvatureTable00 4 30).add (curvatureTable01 4 30)).mul (RI.point 60)=curvatureTail4 := by decide +kernel
end AtomicTriangular.FiniteCertificate
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

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

lemma sine_pi_bounds : (piLow:ℝ)≤Real.pi ∧ Real.pi≤(piHigh:ℝ) := by
  rcases AtomicTriangular.Constants.pStar_bracket with ⟨h1,h2⟩
  constructor
  · have hh : (piLow:ℝ)≤AtomicTriangular.Constants.pStar := by norm_num [piLow,AtomicTriangular.Constants.pStar]
    exact hh.trans h1.le
  · have hh : AtomicTriangular.Constants.pStar+AtomicTriangular.Constants.eps≤(piHigh:ℝ) := by norm_num [piHigh,AtomicTriangular.Constants.pStar,AtomicTriangular.Constants.eps]
    exact h2.le.trans hh

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def localPhase (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)%36
def localShift (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)/36
def cellSeparation (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  min ((localPhase u j:ℚ)+cellLo u k) (36-((localPhase u j:ℚ)+cellHi u k))
def cellFactor (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  if j=localPivot u then vanishingLower (cellMagnitude u k) else sineLower (cellSeparation u k j)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma realP_nonneg (s : ℝ) : 0 ≤ realP s := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
lemma realP_periodic : Function.Periodic realP 36 := by
  intro s
  unfold realP
  apply Finset.prod_congr rfl
  intro a _
  rw [show Real.pi*(s+36-residue a)/36=Real.pi*(s-residue a)/36+Real.pi by ring,Real.sin_add_pi]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def nearDisplacement (n : Fin 7) (y : Fin 2) : ℝ := nearDisplacementNum n y / 2
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def nearRadiusBox (n : Fin 7) : RI := if n.val<2 then RI.point 1 else (RI.point 3).divNat 2
lemma nearRadiusBox_mem (n : Fin 7) : (nearRadiusBox n).Mem (nearRadius n) := by
  fin_cases n <;> (first | (simp [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; all_goals first | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | rfl | decide) | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale])
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst0_0 : RI := ⟨519303659837231508609753465144172443307032014319,519303659837231508609753465144172443307032014635⟩
def remainderConst0_1 : RI := ⟨253857234449456888984536148167494600049643340549163441513275,253857234449456888984536148167494600049643583879658232965768⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst1_0 : RI := ⟨519303659837231508609753465144172443307032014319,519303659837231508609753465144172443307032014635⟩
def remainderConst1_1 : RI := ⟨2220946914991851539663952795577454335007644206646516624,2220946914991851539663952795577454335007644352721486683⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst2_0 : RI := ⟨2754363752882702151881500878729181939270482946869770,2754363752882702151881500878729181939270482946915417⟩
def remainderConst2_1 : RI := ⟨1040413389771822233684589810260266695275990073926812837302,1040413389771822233684589810260266695275990089961190387322⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst3_0 : RI := ⟨2754363752882702151881500878729181939270482946869770,2754363752882702151881500878729181939270482946915417⟩
def remainderConst3_1 : RI := ⟨12287957044502690722447256922551839140954374467733388519,12287957044502690722447256922551839140954374473604059139⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst4_0 : RI := ⟨2754363752882702151881500878729181939270482946869770,2754363752882702151881500878729181939270482946915417⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussianG_contDiff (z : ℝ) : ContDiff ℝ ⊤ (gaussianG z) := by unfold gaussianG; fun_prop
lemma gaussianG_second {z : ℝ} (hz : 0<z) (s : ℝ) :
    iteratedDeriv 2 (gaussianG z) s=Q 1/z*Real.exp ((1-s)/z) := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (gaussianG z)=fun t => -Q 1*Real.exp ((1-t)/z) := funext fun t => (gaussianG_deriv hz t).deriv
  rw [he]
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (-Q 1))
  convert hh.deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)
lemma deletedSecond_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (m s L : ℝ)
    (hb : ∀ t∈uIcc m s,L ≤ iteratedDeriv 2 f t/2) : L ≤ deletedSecond f m s := by
  by_cases hms : m=s
  · subst s
    simpa [deletedSecond] using hb m (left_mem_uIcc)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf hms
    rw [he]
    exact hb c (Ioo_subset_Icc_self hc)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors10 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma cell_displacement (u : Fin 30) (k : Fin 100) {x : ℝ}
    (hx : (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100) :
    (localHalf u:ℝ)*x∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ) := by
  have hlo : (cellLo u k:ℝ)=min ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellLo; push_cast; rfl
  have hhi : (cellHi u k:ℝ)=max ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellHi; push_cast; rfl
  rw [hlo,hhi]
  by_cases h : 0≤(localHalf u:ℝ)
  · have hab : (localHalf u:ℝ)*k.val/100≤(localHalf u:ℝ)*(k.val+1)/100 := by nlinarith
    rw [min_eq_left hab,max_eq_right hab]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 h,mul_le_mul_of_nonneg_left hx.2 h]
  · have h := le_of_not_ge h
    have hab : (localHalf u:ℝ)*(k.val+1)/100≤(localHalf u:ℝ)*k.val/100 := by nlinarith
    rw [min_eq_right hab,max_eq_left hab]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 h,mul_le_mul_of_nonpos_left hx.2 h]
lemma local_boundary_geometry (u : Fin 30) :
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) := by
  exact (show ∀ u : Fin 30,
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) by decide +kernel) u
lemma local_halfGap_cover {t : ℝ} (ht : t∈Ico (-(5/2)) (67/2)) :
    ∃ u : Fin 30,∃ x∈Icc (0:ℝ) 1,t=(localCenter u:ℝ)+(localHalf u:ℝ)*x ∧
      t∈Ico (localBoundary u.val:ℝ) (localBoundary (u.val+1):ℝ) := by
  have hex : ∃ n : ℕ,1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) := by
    refine ⟨30,by omega,le_rfl,?_⟩
    simpa only [local_boundary_end.2,Rat.cast_div,Rat.cast_ofNat] using ht.2
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  change 1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) at hn
  have hl : (localBoundary (n-1):ℝ)≤t := by
    by_cases h : n=1
    · simp only [h,Nat.sub_self,local_boundary_end.1,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat]
      linarith [ht.1]
    · have hmin := Nat.find_min hex (show n-1<n by omega)
      by_contra! hh
      exact hmin ⟨by omega,by omega,hh⟩
  let u : Fin 30 := ⟨n-1,by omega⟩
  have hg := local_boundary_geometry u
  have hg₁ : min (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary u.val:ℝ) := by
    simpa only [Rat.cast_min,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.1
  have hg₂ : max (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary (u.val+1):ℝ) := by
    simpa only [Rat.cast_max,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.2.1
  have hu : t<(localBoundary (u.val+1):ℝ) := by simpa only [u,show n-1+1=n by omega] using hn.2.2
  have hb : t∈uIcc (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ)) := by
    rw [uIcc,mem_Icc,hg₁,hg₂]
    exact ⟨hl,hu.le⟩
  have hne : (localHalf u:ℝ)≠0 := by exact_mod_cast hg.2.2.1
  refine ⟨u,(t-localCenter u)/(localHalf u:ℝ),?_,?_,hl,hu⟩
  · by_cases hp : 0<(localHalf u:ℝ)
    · rw [uIcc_of_le (by linarith)] at hb
      exact ⟨div_nonneg (sub_nonneg.mpr hb.1) hp.le,(div_le_one hp).mpr (by linarith [hb.2])⟩
    · have hp : (localHalf u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      rw [uIcc_of_ge (by linarith)] at hb
      exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hb.2) hp.le,(div_le_one_of_neg hp).mpr (by linarith [hb.1])⟩
  · field_simp
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma strong_local_geometry (u : Fin 30) (hu : 16 ≤ u.val ∧ u.val ≤ 21) :
    localCenter u∈({16,19,21}:Finset ℤ) ∧ cellBarrier u=3 := by
  have hh : ∀ u : Fin 30,16 ≤ u.val ∧ u.val ≤ 21 → localCenter u∈({16,19,21}:Finset ℤ) := by decide +kernel
  exact ⟨hh u hu,by simp [cellBarrier,hu]⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_identity (f : ℝ → ℝ) (m s : ℝ) :
    f s=f m+deriv f m*(s-m)+(s-m)^2*deletedSecond f m s := by
  by_cases hsm : s=m
  · simp [hsm]
  · rw [deletedSecond,ite_eq_right hsm]
    field_simp [sub_ne_zero.mpr hsm]
    ring
end AtomicTriangular.Construction
end

end OAI
end


