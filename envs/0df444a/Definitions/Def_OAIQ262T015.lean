-- Prove2me | Definitions.Def_OAIQ262T015
-- name    : OAIQ262T015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:42:35.844674+00:00
-- url     : https://prove2.me/theorems/2bfbb0e0-535c-4ebf-862c-6c0d0aa11f8e
-- title:
--   Definitions bundle OAIQ262T015 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 14 definitions and 34 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.cellFactor`, `OAI.AtomicTriangular.Construction.cellSeparation`, `OAI.AtomicTriangular.Construction.localPhase`, `OAI.AtomicTriangular.Construction.localShift`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_3`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_4`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01`, `OAI.AtomicTriangular.FiniteCertificate.nearRadiusBox`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_1`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst1_0`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst1_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_ParamActual`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualInput`, `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_FiniteJets`, `Triangular_Construction_FiniteProjection`, `Triangular_Construction_Schur`, `Triangular_Schwartz_FourierCLM`, `Triangular_Schwartz_Realness`, `Triangular_Signs_FarSigns`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_RemainderBoxes`, `Triangular_Signs_RemainderSums0`, `Triangular_Signs_RemainderSums1`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridCover`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_CurvatureData01`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T000`, `OAIQ262T001`, `OAIQ262T002` and `OAIQ262T003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T096`, `OAIQ262T097`, `OAIQ262T098`, `OAIQ262T099`, `OAIQ262T100`, `OAIQ262T101`, `OAIQ262T102`, `OAIQ262T103`, `OAIQ262T104`, `OAIQ262T105`, `OAIQ262T106`, `OAIQ262T107`, `OAIQ262T108`, `OAIQ262T109`, `OAIQ262T110`, `OAIQ262T111`, `OAIQ262T112`, `OAIQ262T113`, `OAIQ262T114`, `OAIQ262T115`, `OAIQ262T116`, `OAIQ262T117`, `OAIQ262T118`, `OAIQ262T119`, `OAIQ262T120`, `OAIQ262T121`, `OAIQ262T122`, `OAIQ262T123`, `OAIQ262T124`, `OAIQ262T125`, `OAIQ262T126`, `OAIQ262T127`, `OAIQ262T128`, `OAIQ262T129`, `OAIQ262T130`, `OAIQ262T131`, `OAIQ262T132`, `OAIQ262T133`, `OAIQ262T134`, `OAIQ262T135` and `OAIQ262T136`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T000
import Definitions.Def_OAIQ262T001
import Definitions.Def_OAIQ262T002
import Definitions.Def_OAIQ262T003

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
namespace AtomicTriangular.Construction

open Polynomial

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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamActual
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_Schur
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInput
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

lemma finiteC_P (a : Fin 15) :
    (fun s => (sineFactor a s)^2*finiteC a s) = fun s => 4*(kappa:ℂ)^2*P s := by
  funext s
  rw [P_factor a]
  unfold finiteC
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

lemma integrable_gaussian {k : ℝ} (hk : 0 < k) : Integrable (gaussian k) := by
  have hc : 0 < ((Real.pi*k*b:ℝ):ℂ).re := by
    simpa only [Complex.ofReal_re] using mul_pos (mul_pos Real.pi_pos hk) b_pos
  have hi := (integrable_cexp_neg_mul_sq_norm_add hc 0 (0:Plane)).norm
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [gaussian,radial,Complex.norm_exp,mul_assoc,pow_two]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteProjection
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInterpolation
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
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma dBasis_conj (n : Node) (s : ℂ) : conj (dBasis n s) = dBasis n (conj s) := by
  simpa only [dBasis,Complex.ofReal_intCast] using dslope_conj_real P_conj (n.val:ℝ) s
lemma cBasis_conj (n : Node) (s : ℂ) : conj (cBasis n s) = cBasis n (conj s) := by
  simpa only [cBasis,Complex.ofReal_intCast] using dslope_conj_real (dBasis_conj n) (n.val:ℝ) s
lemma tailInput_conj (a : InputCoefficients) (s : ℂ) : conj (tailInput a s) = tailInput a (conj s) := by
  simp only [tailInput,map_add,map_mul,Complex.conj_ofReal,P_conj,Complex.conj_tsum,cBasis_conj,dBasis_conj]

lemma inputComplex_real (a : InputCoefficients) (x : Plane) : conj (inputComplex a x) = inputComplex a x := by
  simp only [inputComplex,map_add,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal,tailInput_conj,finiteInput_conj]

end AtomicTriangular.Construction
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridDefs
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridAnalytic
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderBoxes
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
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderConst0_1 : RI := ⟨253857234449456888984536148167494600049643340549163441513275,253857234449456888984536148167494600049643583879658232965768⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums1
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_GaussianDeleted
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_FarSigns
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


