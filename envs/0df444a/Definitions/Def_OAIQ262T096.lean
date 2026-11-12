-- Prove2me | Definitions.Def_OAIQ262T096
-- name    : OAIQ262T096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:03.461183+00:00
-- url     : https://prove2.me/theorems/126a8738-2c78-4d9d-8305-e6a5b58b2545
-- title:
--   Definitions bundle OAIQ262T096 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 9 definitions and 61 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.atomFunction`, `OAI.AtomicTriangular.Construction.finiteJ`, `OAI.AtomicTriangular.Construction.finiteJJet`, `OAI.AtomicTriangular.Construction.outputComplex`, `OAI.AtomicTriangular.Construction.pairComplex`, `OAI.AtomicTriangular.Construction.rawConstantCurvature`, `OAI.AtomicTriangular.Construction.rawTailCurvature`, `OAI.AtomicTriangular.Construction.transformedFunction`, `OAI.AtomicTriangular.Construction.transformedInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_CurvatureAnalytic`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_DirectWaveJets`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteJets`, `Triangular_Construction_FinitePairBridge`, `Triangular_Construction_NodeJets`, `Triangular_Schwartz_FourierCLM`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_InputCLM`, `Triangular_Schwartz_Regularity`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData01`, `Triangular_Taylor_CurvatureData11`, `Triangular_Taylor_FiniteTaylorIdentity`, `Triangular_Taylor_TaylorExp01`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T009`, `OAIQ262T012`, `OAIQ262T013`, `OAIQ262T014`, `OAIQ262T015` and `OAIQ262T044` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T143`, `OAIQ262T144`, `OAIQ262T145` and `OAIQ262T146`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T009
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T014
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T044

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

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

end AtomicTriangular.FiniteCertificate

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

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
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def rawConstantCurvature (s : ℝ) : ℝ :=
  (∑ j : Fin 31, curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖)/2
def rawTailCurvature (i : Fin 5) : ℝ :=
  60*(curvatureWave 0 0 (curvaturePoint i) (frequency 30)+
    curvatureWave 0 1 (curvaturePoint i) (frequency (if i.val=0 then 15 else 30)))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma taylorPhase_re_nonpos (q br : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    (taylorPhase q br t).re≤0 := by
  fin_cases br
  · simp only [taylorPhase,↓reduceIte,sub_re,mul_re,mul_im,I_re,I_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_sub]
    have hh : h≤damping q := by fin_cases q <;> (first | (simp [damping,h,H]; all_goals first | (norm_num [damping,h,H]; done) | rfl | decide) | (norm_num [damping,h,H]; done) | norm_num [damping,h,H])
    exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh))
  · change (I*Real.pi*zeta (damping q) h t).re≤0
    rw [wavePhase_re]
    have hh := (frequencyDecay_pos q 0 ht).le
    change 0≤Real.pi*(damping q*Xwave (damping q) t-h) at hh
    nlinarith

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0 ≤ curvatureWave q br s t := by
  unfold curvatureWave; positivity
lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t ≤ curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
lemma curvatureWave_direct (q : Fin 2) (s t : ℝ) :
    curvatureWave q 0 s t = Real.pi^2*(t^2+(damping q-h)^2)*Real.exp (-Real.pi*(damping q-h)*s) := by
  unfold curvatureWave
  rw [←Complex.normSq_eq_norm_sq]
  simp only [taylorPhase,taylorAmplitude,Fin.val_zero,↓reduceIte,norm_one,mul_one,
    Complex.normSq_apply,sub_re,sub_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,
    zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
  ring_nf
lemma curvatureWave_transformed (q : Fin 2) (s t : ℝ) :
    curvatureWave q 1 s t = Real.pi^2*(h^2+(4/3-2*damping q*h)*Xwave (damping q) t)*
      Real.sqrt (Xwave (damping q) t)*Real.exp (-Real.pi*(damping q*Xwave (damping q) t-h)*s) := by
  simp only [curvatureWave,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [norm_wavePhase (damping_pos q),norm_lambda (damping_pos q),wavePhase_re,mul_pow,
    Real.sq_sqrt]
  rw [←normSq_zeta (damping_pos q)]
  exact normSq_nonneg _
lemma curvatureWave_even (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s (-t)=curvatureWave q br s t := by
  fin_cases br
  · simp [curvatureWave_direct]
  · simp [curvatureWave_transformed,Xwave,waveDen]
lemma curvatureWave_abs (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s |t|=curvatureWave q br s t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,curvatureWave_even]
lemma curvature_tail_direct {s t : ℝ} (ht : |t|≤5/6) :
    curvatureWave 0 0 s t ≤ curvatureWave 0 0 s (5/6) := by
  rw [curvatureWave_direct,curvatureWave_direct]
  norm_num [damping]
  have hh : t^2≤(5/6:ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hh)]
lemma curvature_tail_zero {t : ℝ} (_ht : |t|≤5/6) :
    curvatureWave 0 1 0 t ≤ curvatureWave 0 1 0 0 := by
  rw [curvatureWave_transformed,curvatureWave_transformed]
  simp only [mul_zero,Real.exp_zero,mul_one]
  have hx : Xwave (damping 0) t≤Xwave (damping 0) 0 := by
    rw [←show Xwave (damping 0) |t|=Xwave (damping 0) t by simp [Xwave,waveDen]]
    exact Xwave_antitone (damping_pos 0) le_rfl (abs_nonneg t)
  have h1 : 0≤4/3-2*damping 0*h := by norm_num [damping,h]
  apply mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx h1) _) (sq_nonneg _)) (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg _)
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg h1 (Xwave_pos (damping_pos 0) 0).le))
lemma curvature_tail_positive {s t : ℝ} (hs : 1 ≤ s) (ht : |t| ≤ 5/6) :
    curvatureWave 0 1 s t ≤ curvatureWave 0 1 s (5/6) := by
  rw [←curvatureWave_abs 0 1 s t]
  rw [curvatureWave_transformed,curvatureWave_transformed]
  have hx := Xwave_pos (damping_pos 0) (5/6)
  have hxy := Xwave_antitone (damping_pos 0) (abs_nonneg t) ht
  have hbase : (3/2:ℝ)≤Real.pi*h*Xwave h (5/6) := by
    have hp := Real.pi_gt_three
    norm_num [Xwave,waveDen,h] at *
    linarith
  have hb : (3/2:ℝ)≤(Real.pi*damping 0*s)*Xwave (damping 0) (5/6) := by
    change (3/2:ℝ)≤(Real.pi*h*s)*Xwave h (5/6)
    have hh : 0 ≤ h := by norm_num [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg Real.pi_pos.le (mul_nonneg hh hx.le))]
  have hh := Envelope.linear_sqrt_exp_antitone hx hxy (sq_nonneg h)
    (show 0≤4/3-2*damping 0*h by norm_num [damping,h]) hb
  have he (x : ℝ) : Real.exp (-Real.pi*(damping 0*x-h)*s) =
      Real.exp (Real.pi*h*s)*Real.exp (-(Real.pi*damping 0*s)*x) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he,he]
  convert mul_le_mul_of_nonneg_left hh (show 0≤Real.pi^2*Real.exp (Real.pi*h*s) by positivity) using 1 <;> first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_0_pre (j : Fin 31) : (curvatureExpInput 0 0 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_1_pre (j : Fin 31) : (curvatureExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_2_pre (j : Fin 31) : (curvatureExpInput 0 0 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_3_pre (j : Fin 31) : (curvatureExpInput 0 0 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_4_pre (j : Fin 31) : (curvatureExpInput 0 0 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_0_pre (j : Fin 31) : (curvatureExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_1_pre (j : Fin 31) : (curvatureExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_2_pre (j : Fin 31) : (curvatureExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_3_pre (j : Fin 31) : (curvatureExpInput 0 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_4_pre (j : Fin 31) : (curvatureExpInput 0 1 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_1_pre (j : Fin 31) : (curvatureExpInput 1 1 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_2_pre (j : Fin 31) : (curvatureExpInput 1 1 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_3_pre (j : Fin 31) : (curvatureExpInput 1 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_4_pre (j : Fin 31) : (curvatureExpInput 1 1 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureTail0_calc : ((curvatureTable00 0 30).add (curvatureTable01 0 15)).mul (RI.point 60)=curvatureTail0 := by decide +kernel
lemma curvatureTail1_calc : ((curvatureTable00 1 30).add (curvatureTable01 1 30)).mul (RI.point 60)=curvatureTail1 := by decide +kernel
lemma curvatureTail2_calc : ((curvatureTable00 2 30).add (curvatureTable01 2 30)).mul (RI.point 60)=curvatureTail2 := by decide +kernel
lemma curvatureConstant3_calc : (RI.sum (fun j : Fin 31 => (curvatureTable01 3 j).mul (columnNorm22 j))).divNat 2=curvatureConstant3 := by decide +kernel
lemma curvatureTail3_calc : ((curvatureTable00 3 30).add (curvatureTable01 3 30)).mul (RI.point 60)=curvatureTail3 := by decide +kernel
lemma curvatureTail4_calc : ((curvatureTable00 4 30).add (curvatureTable01 4 30)).mul (RI.point 60)=curvatureTail4 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction
open Complex

lemma finiteC_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteC a n.val=0 ∧ deriv (finiteC a) n.val=0 := by
  have hne : (sineFactor a n.val)^2≠0 := pow_ne_zero 2 (sineFactor_ne_zero hn)
  have hh := congrFun (finiteC_P a) (n.val:ℂ)
  have hc : finiteC a n.val=0 := by
    apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*finiteC a n.val=0 by
      simpa [P_node] using hh)).resolve_left hne
  refine ⟨hc,?_⟩
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hd := (((hf (n.val:ℂ)).hasDerivAt.pow 2).mul
    ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
  change deriv (fun s => (sineFactor a s)^2*finiteC a s) n.val = _ at hd
  rw [finiteC_P] at hd
  have hr := ((differentiable_P (n.val:ℂ)).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  rw [deriv_P_node,mul_zero] at hr
  rw [hr,hc,mul_zero,zero_add] at hd
  apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*deriv (finiteC a) n.val=0 by simpa using hd.symm)).resolve_left hne

lemma finiteD_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteD a n.val=0 ∧ deriv (finiteD a) n.val=0 := by
  obtain ⟨h0,h1⟩ := finiteC_other_jets a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,mul_zero]
  · have hh := (((differentiable_finiteRatio a (n.val:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,mul_zero,mul_zero,add_zero] at hh
    exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_NodeJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : dBasis n m.val = 0 := by
  rw [dBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

def transformedFunction (k v : ℝ) (hk : 0 < k) (s : ℂ) : C(Spectrum,ℂ) :=
  lambdaFunction k hk * NormedSpace.exp (s • zetaFunction k v hk)
lemma transformedFunction_apply (k v : ℝ) (hk : 0 < k) (s : ℂ) (t : Spectrum) :
    transformedFunction k v hk s t = transformedWave k v t.val s := by
  simp only [transformedFunction,ContinuousMap.mul_apply,exponential_apply]
  change lambda k t.val * exp (s*(I*Real.pi*zeta k v t.val)) = _
  unfold transformedWave
  congr 2
  ring

def atomFunction (k : ℝ) (x : Plane) : C(Spectrum,ℂ) :=
  exp (-(Real.pi:ℂ)*k*(radial x:ℂ)) • phaseFunction (radial x:ℂ)
lemma atomFunction_apply (k : ℝ) (x : Plane) (t : Spectrum) :
    atomFunction k x t = exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ)) := rfl
lemma continuous_atomFunction (k : ℝ) : Continuous (atomFunction k) := by
  have hs : Continuous (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))) := by
    unfold radial; fun_prop
  have ht : Continuous (fun x : Plane => phaseFunction (radial x:ℂ)) := by
    apply differentiable_phaseFunction.continuous.comp
    unfold radial; fun_prop
  simpa only [atomFunction] using! hs.smul ht
lemma atomFunction_bound (k : ℝ) (x : Plane) : ‖atomFunction k x‖ ≤ gaussian k x := by
  apply (ContinuousMap.norm_le _ (by unfold gaussian; positivity)).mpr
  intro t
  rw [atomFunction_apply,norm_mul]
  have hp : ‖exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp,mul_one,Complex.norm_exp]
  simp [gaussian]
lemma integrable_atomFunction {k : ℝ} (hk : 0 < k) : Integrable (atomFunction k) :=
  (integrable_gaussian hk).mono' (continuous_atomFunction k).aestronglyMeasurable
    (ae_of_all _ (atomFunction_bound k))
lemma fourier_atomFunction {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (atomFunction k) w = exp (-(Real.pi:ℂ)*v*(radial w:ℂ)) •
      transformedFunction k v hk (radial w:ℂ) := by
  ext t
  have hh := clm_fourier (ContinuousMap.evalCLM ℂ t) (atomFunction k) (integrable_atomFunction hk) w
  have ha := transformed_spectral_wave hk v t.val w
  change 𝓕 (fun x => atomFunction k x t) w = (𝓕 (atomFunction k) w) t at hh
  rw [← hh]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
    exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))) w =
    exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedFunction k v hk (radial w:ℂ) t
  rw [transformedFunction_apply]
  exact ha
lemma fourier_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*S (transformedFunction k v hk (radial w:ℂ)) := by
  have hh := clm_fourier S (atomFunction k) (integrable_atomFunction hk) w
  have he : (fun x => S (atomFunction k x)) =
      (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
    ext x
    simp only [atomFunction,map_smul,smul_eq_mul]
  rw [he,fourier_atomFunction hk v,map_smul] at hh
  exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_term_bound (a : InputCoefficients) (n : TailNode) :
    ‖(a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val‖ ≤
      (|a.tailC n|+|a.tailD n|)*tailVariation := by
  have hc : cVariation ≤ tailVariation := by
    exact le_add_of_nonneg_right (by unfold dVariation coeffAbs; positivity)
  have hd : dVariation ≤ tailVariation := by
    exact le_add_of_nonneg_left (by unfold cVariation coeffAbs; positivity)
  calc
    _ ≤ ‖(a.tailC n:ℂ) • spectralCCLM n.val‖ + ‖(a.tailD n:ℂ) • spectralDCLM n.val‖ := by
      convert! norm_add_le ((a.tailC n:ℂ) • spectralCCLM n.val) ((a.tailD n:ℂ) • spectralDCLM n.val) using 1
      all_goals try with_reducible_and_instances rfl
    _ ≤ |a.tailC n| * ‖spectralCCLM n.val‖ + |a.tailD n| * ‖spectralDCLM n.val‖ := by
      have hn (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
        intro f
        change ‖(r:ℂ) * T f‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
      exact add_le_add (hn _ _) (hn _ _)
    _ ≤ |a.tailC n| *tailVariation+|a.tailD n| *tailVariation :=
      add_le_add (mul_le_mul_of_nonneg_left ((spectralCCLM_norm n.val).trans hc) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((spectralDCLM_norm n.val).trans hd) (abs_nonneg _))
    _ = _ := by ring

lemma summable_tailSpectral (a : InputCoefficients) :
    Summable (fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val) :=
  Summable.of_norm_bounded (E := C(Spectrum,ℂ) →L[ℂ] ℂ)
    (f := fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)
    (a.summable.mul_right tailVariation) (tailSpectral_term_bound a)

lemma tailSpectral_apply (a : InputCoefficients) (f : C(Spectrum,ℂ)) :
    tailSpectral a f = (a.C:ℂ)*spectralP f +
      ∑' n : TailNode, ((a.tailC n:ℂ)*spectralC n.val f + (a.tailD n:ℂ)*spectralD n.val f) := by
  have ht := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tailSpectral a)
  simpa only [tailSpectral,add_apply, smul_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul,spectralPCLM_apply,
    spectralCCLM_apply,spectralDCLM_apply] using congrArg (fun x => (a.C:ℂ)*spectralP f+x) ht

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

lemma finiteSpectral_phase (a : InputCoefficients) (s : ℂ) :
    finiteSpectral a (phaseFunction s) = finiteInput a s := by
  simp only [finiteSpectral,sum_apply,add_apply,
    smul_apply,smul_eq_mul,atomSpectral_finiteC_phase,atomSpectral_finiteD_phase,finiteInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ r : Fin 8, (e r:ℂ) * (∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r * finiteWaveJet q 0 (frequency j) k s +
    finiteSpectrum (otherSide side) q j r * finiteWaveJet q 1 (frequency j) k s))
def finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (s : ℝ) : ℝ := (finiteJJet side e 0 s).re
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_DirectWaveJets
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
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma tailSpectral_zero_coeff (C : ℝ) (a : TrigonometricCoefficients) :
    tailSpectral (coefficientInput C a 0)=(C:ℂ) • spectralPCLM := by
  ext f
  simp [tailSpectral_apply,coefficientInput,spectralPCLM_apply]
lemma tailSpectral_zero_constant (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput 0 a w)=
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := by
  have hz : (0:ℂ) • spectralPCLM=(0:C(Spectrum,ℂ) →L[ℂ] ℂ) := by
    ext f
    change (0:ℂ)*_=0
    exact zero_mul _
  change (0:ℂ) • spectralPCLM+_= _
  rw [hz,zero_add]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma rawConstantCurvature_antitone {u s : ℝ} (hus : u ≤ s) :
    rawConstantCurvature s ≤ rawConstantCurvature u := by
  unfold rawConstantCurvature
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 0 1 (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FinitePairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma finiteSpectrum_dot (side q : Fin 2) (j : Fin 31) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8,(e r:ℂ)*finiteSpectrum side q j r)=
      if q.val=0 then ((gamma side *ᵥ e) 2:ℂ)*fourierCoeff j
      else ∑ c : Fin 22,(finiteApprox side e c:ℂ)*finiteColumn ⟨c.val,by omega⟩ j := by
  by_cases hq : q.val=0
  · simp only [finiteSpectrum,hq,↓reduceIte,Acoefficient_constant,Matrix.mulVec,dotProduct,
      ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  · simp only [finiteSpectrum,hq,↓reduceIte,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    change (∑ r : Fin 8,(e r:ℂ)*(finiteColumn ⟨c.val,by omega⟩ j*(Acoefficient side ⟨c.val,by omega⟩ r:ℂ)))=
      ((∑ r : Fin 8,Acoefficient side ⟨c.val,by omega⟩ r*e r:ℝ):ℂ)*finiteColumn ⟨c.val,by omega⟩ j
    simp only [ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Regularity
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
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

def transformedInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  tailSpectral a (transformedFunction h h h_pos s) +
    finiteSpectral a (transformedFunction H h H_pos s)
def outputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedInput a (radial x)
lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
lemma outputComplex_radial (a : InputCoefficients) (x y : Plane) (hxy : ‖x‖=‖y‖) : outputComplex a x = outputComplex a y := by
  simp only [outputComplex,radial,hxy]

def pairComplex (a₁ a₂ : InputCoefficients) : Plane → ℂ := inputComplex a₁ + outputComplex a₂
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_4_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 4)).exp = taylorExp0_1_4 j := by
  revert j
  decide +kernel
lemma taylorExp0_1_7_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 7)).exp = taylorExp0_1_7 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


