-- Prove2me | Definitions.Def_OAIQ240Bp025
-- name    : OAIQ240Bp025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:22:58.942791+00:00
-- url     : https://prove2.me/theorems/391e385e-58fa-4412-a32e-e36961e597b4
-- title:
--   Definitions bundle OAIQ240Bp025 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 32 definitions and 54 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectionDeriv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeCR`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeCoordinates`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeEquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeNormalize`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCompInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderLocInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lipHolderSet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCR`, `OAI.HigherDimensionalBallPacking.Rigidity.projectedCauchyForm`, `OAI.SymplecticBallPacking.Hamiltonian.pullbackForm`, `OAI.SymplecticBallPacking.Hamiltonian.roundDisk`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Cauchy_GreenFormula`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Cauchy/GreenFormula.lean), [`BallPacking_Compactness_AffineCorrectionInfinity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/AffineCorrectionInfinity.lean), [`BallPacking_Compactness_GradientBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/GradientBounds.lean), [`BallPacking_Fredholm_FiniteExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean), [`BallPacking_Holder_MarkedFrame`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedFrame.lean), [`BallPacking_Holder_MarkedJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedJets.lean).
--
--   **Imports.** It imports the bundles `OAIQ240Bp008` and `OAIQ240Bp009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp012`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp008
import Definitions.Def_OAIQ240Bp009

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem plane_deriv_first {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun x => F (x,p.2)) p.1 = fderiv ℝ F p (1,0) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem plane_deriv_second {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun t => F (p.1,t)) p.2 = fderiv ℝ F p (0,1) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

def pullbackForm (phi : Plane → Plane) (alpha : Plane → Plane →L[ℝ] ℝ)
    (p : Plane) : Plane →L[ℝ] ℝ := (alpha (phi p)).comp (fderiv ℝ phi p)

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

theorem pullbackForm_smooth {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) :
    ContDiff ℝ ∞ (pullbackForm phi alpha) :=
  (ha.comp hp).clm_comp (hp.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem pullbackForm_curl {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) (p : Plane) :
    planarCurl (pullbackForm phi alpha) p = planarCurl alpha (phi p) *
      planarArea (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1)) := by
  have hd := (((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (phi p)).hasFDerivAt.comp p
    (((hp.differentiable (by simp)) p).hasFDerivAt)).clm_comp
      (((hp.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt)
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  dsimp only [Function.comp_def] at hd
  unfold planarCurl pullbackForm
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  rw [hs.eq (1,0) (0,1)]
  have hb := bilinear_skew_plane (fderiv ℝ alpha (phi p))
    (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1))
  linear_combination hb

theorem integral_curl_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (a b : Plane) (hab : a ≤ b) :
    (∫ p in Icc a b, planarCurl alpha p) =
      ((∫ t in a.2..b.2, alpha (b.1,t) (0,1)) - ∫ t in a.2..b.2, alpha (a.1,t) (0,1)) -
      ((∫ r in a.1..b.1, alpha (r,b.2) (1,0)) - ∫ r in a.1..b.1, alpha (r,a.2) (1,0)) := by
  let F : Plane → ℝ := fun p => alpha p (0,1)
  let G : Plane → ℝ := fun p => -alpha p (1,0)
  have hF : ContDiff ℝ ∞ F := ha.clm_apply contDiff_const
  have hG : ContDiff ℝ ∞ G := (ha.clm_apply contDiff_const).neg
  have hFd (p : Plane) : fderiv ℝ F p =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)).comp (fderiv ℝ alpha p) :=
    ((ContinuousLinearMap.apply ℝ ℝ (0,1) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  have hGd (p : Plane) : fderiv ℝ G p =
      -((ContinuousLinearMap.apply ℝ ℝ (1,0)).comp (fderiv ℝ alpha p)) :=
    (((ContinuousLinearMap.apply ℝ ℝ (1,0) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).neg).fderiv
  have he (p : Plane) : fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1) = planarCurl alpha p := by
    rw [hFd,hGd]
    rfl
  have hi : IntegrableOn (fun p => fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1)) (Icc a b) :=
    (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hG.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hg := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G
    (fderiv ℝ F) (fderiv ℝ G) a b hab hF.continuous.continuousOn hG.continuous.continuousOn
    (fun p _ => ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt)
    (fun p _ => ((hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt) hi
  simp_rw [he] at hg
  simp only [F,G,intervalIntegral.integral_neg] at hg
  linear_combination hg

theorem polar_deriv_first (p : Plane) :
    fderiv ℝ polarCoord.symm p (1,0) = (Real.cos p.2,Real.sin p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_deriv_second (p : Plane) :
    fderiv ℝ polarCoord.symm p (0,1) = (-p.1*Real.sin p.2,p.1*Real.cos p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_area (p : Plane) :
    planarArea (fderiv ℝ polarCoord.symm p (1,0)) (fderiv ℝ polarCoord.symm p (0,1)) = p.1 := by
  rw [polar_deriv_first,polar_deriv_second,planarArea_apply]
  have ht := Real.cos_sq_add_sin_sq p.2
  dsimp
  linear_combination p.1 * ht

theorem integral_curl_polar_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 ≤ R) :
    (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*planarCurl alpha (polarCoord.symm p)) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  let eta := pullbackForm polarCoord.symm alpha
  have he (p : Plane) : planarCurl eta p = p.1*planarCurl alpha (polarCoord.symm p) := by
    rw [pullbackForm_curl polar_smooth ha,polar_area,mul_comm]
  have h := integral_curl_rectangle (pullbackForm_smooth polar_smooth ha)
    ((0:ℝ),-Real.pi) (R,Real.pi) ⟨hR,by linarith [Real.pi_pos]⟩
  change (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), planarCurl eta p) = _ at h
  simp_rw [he] at h
  have hside (r : ℝ) : eta (r,Real.pi) (1,0) = eta (r,-Real.pi) (1,0) := by
    simp [eta,pullbackForm,polar_deriv_first,polarCoord_symm_apply]
  have hin (t : ℝ) : eta (0,t) (0,1) = 0 := by
    simp [eta,pullbackForm,polar_deriv_second,Prod.mk_zero_zero]
  have hout (t : ℝ) : eta (R,t) (0,1) =
      alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
    simp [eta,pullbackForm,polar_deriv_second]
  change _ = ((∫ t in -Real.pi..Real.pi, eta (R,t) (0,1)) -
    ∫ t in -Real.pi..Real.pi, eta (0,t) (0,1)) -
    ((∫ r in (0:ℝ)..R, eta (r,Real.pi) (1,0)) - ∫ r in (0:ℝ)..R, eta (r,-Real.pi) (1,0)) at h
  simp_rw [hside,hin,hout] at h
  simpa using h

def roundDisk (R : ℝ) : Set Plane := {p | p.1^2+p.2^2 < R^2}

theorem polar_mem_roundDisk {R : ℝ} (hR : 0 < R) {p : Plane} (hp : 0 < p.1) :
    polarCoord.symm p ∈ roundDisk R ↔ p.1 < R := by
  have hn : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 = p.1^2 := by
    simp only [polarCoord_symm_apply]
    linear_combination p.1^2 * Real.cos_sq_add_sin_sq p.2
  change (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 < R^2 ↔ _
  rw [hn]
  constructor <;> intro h <;> nlinarith

theorem integral_roundDisk_polar (f : Plane → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, f p) =
      ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
  have hm : MeasurableSet (roundDisk R) :=
    (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  let S : Set Plane := {p | p.1 < R}
  have hS : MeasurableSet S := (isOpen_lt continuous_fst continuous_const).measurableSet
  have he (p : Plane) (hp : p ∈ polarCoord.target) :
      p.1 * (roundDisk R).indicator f (polarCoord.symm p) =
        S.indicator (fun p => p.1*f (polarCoord.symm p)) p := by
    have hi := polar_mem_roundDisk hR hp.1
    by_cases ht : p.1 < R
    · simp only [indicator_of_mem (hi.mpr ht),indicator_of_mem (show p ∈ S from ht)]
    · simp only [indicator_of_notMem (mt hi.mp ht),indicator_of_notMem (show p ∉ S from ht),mul_zero]
  have hinter : polarCoord.target ∩ S = Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target,mem_inter_iff,mem_prod,mem_Ioi,mem_Ioo,S,mem_ofPred_eq]
    tauto
  calc
    (∫ p in roundDisk R, f p) = ∫ p in polarCoord.target,
        p.1 * (roundDisk R).indicator f (polarCoord.symm p) := by
      rw [← integral_indicator hm]
      exact (integral_comp_polarCoord_symm ((roundDisk R).indicator f)).symm
    _ = ∫ p in polarCoord.target, S.indicator (fun p => p.1*f (polarCoord.symm p)) p :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet he
    _ = ∫ p in Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, p.1*f (polarCoord.symm p) := by
      rw [setIntegral_indicator hS,hinter]
    _ = ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
      apply setIntegral_congr_set
      rw [Icc_prod_eq]
      exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem integral_curl_roundDisk {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, planarCurl alpha p) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  rw [integral_roundDisk_polar _ hR]
  exact integral_curl_polar_rectangle ha hR.le

theorem coordinateForm_smooth {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (coordinateForm U V) :=
  (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem coordinateForm_compact {U V : Plane → ℝ} (hU : HasCompactSupport U)
    (hV : HasCompactSupport V) : HasCompactSupport (coordinateForm U V) := by
  apply HasCompactSupport.intro (hU.union hV)
  intro p hp
  have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
  have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
  simp only [coordinateForm,hu,hv,zero_smul,zero_add]

theorem form_eval_fderiv {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (p v w : Plane) : fderiv ℝ (fun q => alpha q w) p v = fderiv ℝ alpha p v w := by
  have he := ((ContinuousLinearMap.apply ℝ ℝ w : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt).fderiv
  exact congrArg (fun D : Plane →L[ℝ] ℝ => D v) he

theorem coordinateForm_curl {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (p : Plane) :
    planarCurl (coordinateForm U V) p =
      deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 := by
  rw [plane_deriv_first (hV.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    plane_deriv_second (hU.differentiable (by simp))]
  unfold planarCurl
  rw [← form_eval_fderiv (coordinateForm_smooth hU hV),
    ← form_eval_fderiv (coordinateForm_smooth hU hV)]
  simp only [coordinateForm_apply,mul_zero,mul_one,zero_add,add_zero]

end SymplecticBallPacking.Hamiltonian

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

 theorem polar_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (polarCoord.symm (R,t)) = circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,polarCoord_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem angular_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (-R*Real.sin t,R*Real.cos t) =
      Complex.I*circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem roundDisk_measurable (R : ℝ) : MeasurableSet (roundDisk R) :=
  (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet

 theorem cauchyCurl_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cauchyCurl f) :=
  (contDiff_const.mul ((hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)).sub
    ((hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

 theorem cauchyCurl_compact {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cauchyCurl f) :=
  ((hf.fderiv_apply (𝕜 := ℝ) 1).comp_left (g := fun z : ℂ => Complex.I*z) (by simp)).sub
    (hf.fderiv_apply (𝕜 := ℝ) Complex.I)

 def projectedCauchyForm (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) : Plane → Plane →L[ℝ] ℝ :=
  coordinateForm (fun p => L (f (Complex.equivRealProdCLM.symm p)))
    (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p)))

 theorem projectedCauchyForm_smooth (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (projectedCauchyForm L f) := by
  exact coordinateForm_smooth
    (L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff))
    (L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff)))

 theorem projectedCauchyForm_compact (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (projectedCauchyForm L f) := by
  have hc := hf.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  exact coordinateForm_compact (hc.comp_left L.map_zero)
    (hc.comp_left (g := fun z : ℂ => L (Complex.I*z)) (by simp))

 theorem projectedCauchyForm_apply (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) (p v : Plane) :
    projectedCauchyForm L f p v =
      L (f (Complex.equivRealProdCLM.symm p)*Complex.equivRealProdCLM.symm v) := by
  have h (z : ℂ) : z*Complex.equivRealProdCLM.symm v =
      v.1 • z + v.2 • (Complex.I*z) := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply] <;> ring
  rw [h,map_add,map_smul,map_smul]
  simp only [projectedCauchyForm,coordinateForm_apply,smul_eq_mul]
  ring

 theorem projectedCauchyForm_curl (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (p : Plane) :
    planarCurl (projectedCauchyForm L f) p =
      L (cauchyCurl f (Complex.equivRealProdCLM.symm p)) := by
  have hb := (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Complex.equivRealProdCLM.symm p)).hasFDerivAt.comp
    p Complex.equivRealProdCLM.symm.hasFDerivAt
  have hu := L.hasFDerivAt.comp p hb
  have hv := L.hasFDerivAt.comp p (hb.const_mul Complex.I)
  have hU : ContDiff ℝ ∞ (fun p => L (f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff)
  have hV : ContDiff ℝ ∞ (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff))
  rw [projectedCauchyForm,coordinateForm_curl hU hV,
    plane_deriv_first (hV.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    plane_deriv_second (hU.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  simp only [Function.comp_def] at hu hv
  rw [hu.fderiv,hv.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    smul_apply,smul_eq_mul,Complex.equivRealProdCLM_symm_apply,
    Complex.ofReal_one,Complex.ofReal_zero,zero_mul,one_mul,zero_add,add_zero]
  exact (map_sub L _ _).symm

 theorem complex_compact_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ p : Plane, cauchyCurl f (Complex.equivRealProdCLM.symm p)) = 0 := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hh (L : ℂ →L[ℝ] ℝ) : L (∫ p : Plane,
      cauchyCurl f (Complex.equivRealProdCLM.symm p))=0 := by
    rw [←L.integral_comp_comm hi]
    simp_rw [←projectedCauchyForm_curl L hf]
    exact compact_planar_stokes (projectedCauchyForm_smooth L hf)
      (projectedCauchyForm_compact L hc)
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 theorem complex_disk_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t) := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hb : IntervalIntegrable (fun t => f (circleMap 0 R t)*(Complex.I*circleMap 0 R t))
      volume (-Real.pi) Real.pi :=
    ((hf.continuous.comp (continuous_circleMap 0 R)).mul
      (continuous_const.mul (continuous_circleMap 0 R))).intervalIntegrable _ _
  have hh (L : ℂ →L[ℝ] ℝ) :
      L (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      L (∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) := by
    rw [←L.integral_comp_comm hi.integrableOn,←L.intervalIntegral_comp_comm hb]
    simp_rw [←projectedCauchyForm_curl L hf]
    rw [integral_curl_roundDisk (projectedCauchyForm_smooth L hf) hR]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [projectedCauchyForm_apply,polar_complex_eq_circleMap,angular_complex_eq_circleMap]
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 theorem cauchyPuncture_curl (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyCurl (cauchyPuncture b f) z = cauchyCurl f z/z := by
  have he := (cauchyPuncture_eventuallyEq b f hz).fderiv_eq (𝕜 := ℝ)
  unfold cauchyCurl
  rw [he]
  exact cauchyCurl_div (hf.differentiable (by simp) z)
    (fun h => by simp only [h,norm_zero,not_lt_of_ge b.rOut_pos.le] at hz)

 theorem complexCartesian_norm_sq (p : Plane) :
    ‖Complex.equivRealProdCLM.symm p‖^2 = p.1^2+p.2^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.equivRealProdCLM_symm_apply,pow_two]

 theorem complexCartesian_norm_ge_of_notMem {R : ℝ} (hR : 0<R) {p : Plane}
    (hp : p ∉ roundDisk R) : R≤‖Complex.equivRealProdCLM.symm p‖ := by
  have hn := norm_nonneg (Complex.equivRealProdCLM.symm p)
  have he := complexCartesian_norm_sq p
  change ¬p.1^2+p.2^2<R^2 at hp
  push Not at hp
  nlinarith

 theorem cauchy_exterior_integral {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) =
      -(Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)) := by
  let b := cauchyInnerBump R hR
  let g := cauchyPuncture b f
  have hg : ContDiff ℝ ∞ g := cauchyPuncture_smooth b hf
  have hgc : HasCompactSupport g := cauchyPuncture_compact b hc
  have hi : Integrable (fun p : Plane => cauchyCurl g (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hg).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hgc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hs := integral_add_compl (roundDisk_measurable R) hi
  rw [complex_compact_stokes hg hgc,complex_disk_stokes hg hgc hR] at hs
  have he : (∫ p in (roundDisk R)ᶜ, cauchyCurl g (Complex.equivRealProdCLM.symm p)) =
      ∫ p in (roundDisk R)ᶜ,
        cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p := by
    apply setIntegral_congr_fun (roundDisk_measurable R).compl
    intro p hp
    apply cauchyPuncture_curl b hf
    have hh := complexCartesian_norm_ge_of_notMem hR hp
    change R/2 < _
    linarith
  have hb : (∫ t in -Real.pi..Real.pi, g (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) =
      Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hn : b.rOut<‖circleMap 0 R t‖ := by
      rw [norm_circleMap_zero,abs_of_pos hR]
      change R/2<R
      linarith
    rw [show g (circleMap 0 R t)=f (circleMap 0 R t)/circleMap 0 R t from
      (cauchyPuncture_eventuallyEq b f hn).eq_of_nhds]
    field_simp [circleMap_ne_center hR.ne' (θ := t)]
  rw [he,hb] at hs
  exact eq_neg_of_add_eq_zero_right hs

 theorem cauchyCurl_div_integrable {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable (fun z => cauchyCurl f z/z) := by
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
    locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
      (cauchyCurl_smooth hf).continuous (cauchyCurl_compact hc)

 theorem shrinking_exterior_aecover :
    AECover (volume : Measure Plane) (𝓝[>] (0:ℝ)) (fun R => (roundDisk R)ᶜ) := by
  refine ⟨?_,fun R => (roundDisk_measurable R).compl⟩
  filter_upwards [volume.ae_ne (0:Plane)] with p hp
  have hpos : 0<p.1^2+p.2^2 := by
    by_contra! hh
    have hx : p.1=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    have hy : p.2=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    exact hp (Prod.ext hx hy)
  have hsq : ContinuousAt (fun R : ℝ => R^2) 0 := by fun_prop
  have ht : Tendsto (fun R : ℝ => R^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [zero_pow (by decide : (2:ℕ)≠0)] using
      hsq.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  filter_upwards [ht.eventually (Iio_mem_nhds hpos)] with R hR
  change ¬p.1^2+p.2^2<R^2
  exact not_lt_of_ge (le_of_lt hR)

 theorem cauchy_green_fundamental {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ z : ℂ, cauchyCurl f z/z) = -(2*Real.pi*Complex.I)*f 0 := by
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hi : Integrable (fun p : Plane =>
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) :=
    hp.integrable_comp_of_integrable (cauchyCurl_div_integrable hf hc)
  have hl := ((circle_mean_integral_limit hf.continuous).const_mul Complex.I).neg
  have hl' : Tendsto (fun R : ℝ => ∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p)
      (𝓝[>] (0:ℝ)) (𝓝 (-(2*Real.pi*Complex.I)*f 0)) := by
    have hh := hl.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    have heval : -(Complex.I * ((2*Real.pi:ℝ) • f 0)) =
        -(2*Real.pi*Complex.I)*f 0 := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [heval] at hh
    apply hh.congr'
    have hR : ∀ᶠ R in 𝓝[>] (0:ℝ), 0<R := self_mem_nhdsWithin
    filter_upwards [hR] with R hR
    exact (cauchy_exterior_integral hf hc hR).symm
  have he := shrinking_exterior_aecover.integral_eq_of_tendsto _ hi hl'
  rw [← hp.integral_comp' (fun z : ℂ => cauchyCurl f z/z)]
  exact he

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma curlJet_smul (c : ℂ) (A : ℂ →L[ℝ] E) : curlJet (c • A) = c • curlJet A := by
  simp only [curlJet_apply, smul_apply, smul_sub]
  rw [smul_comm c Complex.I]

lemma regularizedCauchyJet_curl_zero {z : ℂ} (hz : z ≠ 0) :
    curlJet (regularizedCauchyJet 0 z) = (0:ℂ) := by
  rw [regularizedCauchyJet_zero_fderiv hz, curlJet_apply]
  have hd := (hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ
  rw [hd.fderiv]
  change Complex.I * ((1:ℂ) * (-(z^2)⁻¹)) - Complex.I * (-(z^2)⁻¹) = 0
  ring

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealContinuousLinearMapIdComplex_solutions_4
omit [CompleteSpace E] in
lemma cancellationJetIntegrand_integrable (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Integrable (cancellationJetIntegrand b 0 g x) := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let δ : ℕ → ℝ := fun n => 1/(n+1)
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ] <;> positivity
  have hδt : Tendsto δ atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hδ⟩
  have hm : AEStronglyMeasurable (cancellationJetIntegrand b 0 g x) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (cancellationJetIntegrand_continuous b (hδ n) hgC x).aestronglyMeasurable)
      (Eventually.of_forall fun w => (cancellationJetIntegrand_tendsto b g x w).comp hδt)
  apply ((cauchySchauderWeight_integrable b.rOut).const_mul ((C+3)*H)).mono' hm
  apply Eventually.of_forall
  intro w
  apply le_of_tendsto (cancellationJetIntegrand_tendsto b g x w).norm
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact cancellationJetIntegrand_bound b hC hCb hH hg hd x w

lemma bump_complex_compact (b : ContDiffBump (0:ℂ)) :
    HasCompactSupport (fun z : ℂ => (b z : ℂ)) := b.hasCompactSupport.comp_left (g := (Complex.ofReal : ℝ → ℂ)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma bumpCurlKernel_apply (b : ContDiffBump (0:ℂ)) (z : ℂ) :
    bumpCurlKernel b z =
      (Complex.I * (fderiv ℝ b z 1 : ℂ) - (fderiv ℝ b z Complex.I : ℂ)) * z⁻¹ := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (((b.contDiff : ContDiff ℝ ∞ b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) z).hasFDerivAt
  change HasFDerivAt (fun w : ℂ => (b w : ℂ)) _ z at hd
  rw [bumpCurlKernel,cauchyCurl,hd.fderiv,div_eq_mul_inv]
  rfl

lemma bumpCurlKernel_integrable (b : ContDiffBump (0:ℂ)) : Integrable (bumpCurlKernel b) :=
  cauchyCurl_div_integrable (bump_complex_smooth b) (bump_complex_compact b)

lemma bumpCurlKernel_integral (b : ContDiffBump (0:ℂ)) :
    (∫ w : ℂ, bumpCurlKernel b w) = -(2*Real.pi*Complex.I) := by
  have h := cauchy_green_fundamental (bump_complex_smooth b) (bump_complex_compact b)
  simpa only [bumpCurlKernel, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one, mul_one] using h

lemma cutoffCauchyJet_curl (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : z ≠ 0) :
    curlJet (cutoffCauchyJet b 0 z) = bumpCurlKernel b z := by
  rw [cutoffCauchyJet, map_add, map_smul,regularizedCauchyJet_curl_zero hz,smul_zero,zero_add]
  rw [curlJet_apply, smoothCauchyKernel_zero,bumpCurlKernel_apply]
  simp only [ContinuousLinearMap.smulRight_apply, Complex.real_smul,smul_eq_mul]
  ring

lemma tailCauchyJet_curl {z : ℂ} (hz : z ≠ 0) :
    curlJet (tailCauchyJet 0 z) = -bumpCurlKernel schauderBump z := by
  have he : scaledSchauderBump 1 = schauderBump := by funext w; simp [scaledSchauderBump]
  rw [tailCauchyJet,he,map_sub,map_smul,regularizedCauchyJet_curl_zero hz,smul_zero,zero_sub]
  rw [curlJet_apply,smoothCauchyKernel_zero,bumpCurlKernel_apply]
  simp only [ContinuousLinearMap.smulRight_apply, Complex.real_smul,smul_eq_mul]
  ring

omit [CompleteSpace E] in
lemma curlJet_smulComp (A : ℂ →L[ℝ] ℂ) (v : E) :
    curlJet (((ContinuousLinearMap.lsmul ℝ ℂ).flip v).comp A) = curlJet A • v := by
  simp only [curlJet_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_smul,sub_smul,smul_eq_mul]

lemma cutoffCauchyDerivative_curl (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    curlJet (cutoffCauchyDerivative b g x) =
      ∫ w : ℂ, bumpCurlKernel b w • (g (x-w)-g x) := by
  rw [cutoffCauchyDerivative, ← (curlJet (E := E)).integral_comp_comm
    (cancellationJetIntegrand_integrable b hgC hH hg x)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℂ)] with w hw
  rw [cancellationJetIntegrand,curlJet_smulComp,cutoffCauchyJet_curl b hw]

lemma tailCauchyDerivative_curl {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g) (x : ℂ) :
    curlJet (tailCauchyDerivative g x) = -(∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) := by
  rw [tailCauchyDerivative, ← (curlJet (E := E)).integral_comp_comm (tailIntegralJet_integrable hgC hi x)]
  rw [← integral_sub_left_eq_self _ volume x]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℂ)] with w hw
  rw [tailIntegralJet,curlJet_smulComp,sub_sub_cancel,tailCauchyJet_curl hw,neg_smul]

omit [CompleteSpace E] in
lemma bumpCurlKernel_smul_integrable (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) (x : ℂ) : Integrable (fun w : ℂ => bumpCurlKernel b w • g (x-w)) := by
  have hc := cauchyCurl_compact (bump_complex_compact b)
  have hs := cauchyCurl_smooth (bump_complex_smooth b)
  have hi := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
    (hs.continuous.smul (hgC.comp (continuous_const.sub continuous_id)))
    (hc.smul_right (f' := fun w => g (x-w)))
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  funext w
  change (cauchyCurl (fun z : ℂ => (b z : ℂ)) w / w) • g (x-w) =
    w⁻¹ • (cauchyCurl (fun z : ℂ => (b z : ℂ)) w • g (x-w))
  rw [div_eq_mul_inv,smul_smul,mul_comm]

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst3
local instance markedJetInst4_r3eb091_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst5
local instance markedJetInst6_r3eb091_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst7
local instance markedJetInst8_r3eb091_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
omit [CompleteSpace E] in
lemma standardJetCR_zeroNormalize (u : COne ℂ E) :
    standardJetCR (zeroNormalize u) = standardJetCR u := by
  apply value_ext
  intro z
  simp only [standardJetCR_value,zeroNormalize_deriv]

omit [CompleteSpace E] in
lemma complex_differentiable_of_curl_zero {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableAt ℝ f z) (hc : curlJet (fderiv ℝ f z) = 0) :
    DifferentiableAt ℂ f z := by
  let A := fderiv ℝ f z
  let L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ (A 1)
  have hI : A Complex.I = Complex.I • A 1 := by
    exact (sub_eq_zero.mp hc).symm
  have hL : L.restrictScalars ℝ = A := by
    ext w
    have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul,Complex.ofReal_one,mul_one] using (Complex.re_add_im w).symm
    have hAw : A w = w.re • A 1 + w.im • (Complex.I • A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add,map_smul,hI]
    rw [hAw]
    change w • A 1 = _
    conv_lhs => rw [hw]
    rw [add_smul,smul_assoc,one_smul,smul_assoc]
  exact (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt hL).differentiableAt


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst2
local instance crSectInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance crSectInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance crSectInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance crSectInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance crSectInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance crSectInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J)

def crSection (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : HMap ℂ E :=
  const _ (a Complex.I) + jetDirection Complex.I u -
    bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip (structureAlong hJ p a u)
      (const _ (a 1) + jetDirection 1 u)

def crSectionDeriv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    COne ℂ E →L[ℝ] HMap ℂ E :=
  jetDirection Complex.I -
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip (structureAlong hJ p a u)).comp
      (jetDirection 1) -
    ((bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip).flip
      (const _ (a 1)+jetDirection 1 u)).comp (structureAlongDeriv hJ p a u)


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance markedAffineInst1_r3eb091_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r3eb091_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r3eb091_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r3eb091_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma mem_markedModel (K : Set ℂ) (u : COne ℂ E) :
    u ∈ markedModel K ↔ cValue u 0 = 0 ∧ standardJetCR u ∈ supportedHolder K := Iff.rfl

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst5_r3eb091_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r3eb091_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r3eb091_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r3eb091_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedCR : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  standardJetCR.restrict (fun _u hu => hu.2)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance holderCompInst1 : NormedAddCommGroup (HMap X E) := inferInstance

local instance holderCompInst2_r3eb091_1 : NormedSpace ℝ (HMap X E) := inferInstance
def lipHolderSet (K : Set X) (M L : ℝ) : Set (HMap X E) :=
  {u | (∀ x, ‖valueCLM _ u x‖ ≤ M) ∧
    (∀ x y, ‖valueCLM _ u x-valueCLM _ u y‖ ≤ L*dist x y) ∧
    (∀ x ∉ K, valueCLM _ u x = 0)}

variable (b : ContDiffBump (0:ℂ))
local instance holderLocInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1
local instance transInst2_r3eb091_1 : NormedSpace ℝ (HMap D E) := inferInstance
local instance transInst3_r3eb091_1 : NormedAddCommGroup (COne D E) := inferInstance
local instance transInst4_r3eb091_1 : NormedSpace ℝ (COne D E) := inferInstance
def holderTranslate (t : D) (u : HMap D E) : HMap D E :=
  ofBound (fun z => valueCLM _ u (z+t))
    ((valueCLM _ u).continuous.comp (continuous_id.add continuous_const))
    ‖u‖ ‖u‖ (fun z => norm_value_le u _) (norm_nonneg u) (by
      intro x y
      simpa only [dist_add_right] using norm_sub_value_le u (x+t) (y+t))

omit [NormedSpace ℝ D] in
@[simp] lemma holderTranslate_value [NormedSpace ℝ D] (t : D) (u : HMap D E) (z : D) :
    valueCLM _ (holderTranslate t u) z = valueCLM _ u (z+t) := rfl

def jetTranslate (t : D) (u : COne D E) : COne D E :=
  ⟨(holderTranslate t (jetValueCLM _ u),holderTranslate t (jetDerivCLM _ u)),by
    intro z
    have h := (c_hasFDerivAt u (z+t)).comp z ((hasFDerivAt_id z).add_const t)
    change HasFDerivAt (fun x => cValue u (x+t)) (cDeriv u (z+t)) z
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using h⟩

@[simp] lemma jetTranslate_value (t : D) (u : COne D E) (z : D) :
    cValue (jetTranslate t u) z = cValue u (z+t) := rfl

@[simp] lemma jetTranslate_deriv (t : D) (u : COne D E) (z : D) :
    cDeriv (jetTranslate t u) z = cDeriv u (z+t) := rfl

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst10
local instance csInst11 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
local instance csInst12 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
local instance csInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance csInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance csInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance csInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance csInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance csInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst2
local instance ccInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ccInst4_r3eb091_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ccInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ccInst6_r3eb091_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance ccInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeInst1
local instance freeInst2_r3eb091_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeInst3_r3eb091_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeInst4_r3eb091_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance freeInst5_r3eb091_1 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
local instance freeInst6_r3eb091_1 : NormedSpace ℝ (freeModel (E := E) K) := inferInstance
local instance freeInst7_r3eb091_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeInst8_r3eb091_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeInst9_r3eb091_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance freeInst10_r3eb091_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def freeCR : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  standardJetCR.restrict (fun _ hu => hu)

def freeNormalize : freeModel (E := E) K →L[ℝ] markedModel (E := E) K :=
  (zeroNormalize.comp (freeModel (E := E) K).subtypeL).codRestrict _ (fun u => by
    apply (mem_markedModel K _).mpr
    refine ⟨?_,?_⟩
    · change cValue u.val 0-cValue u.val 0=0
      exact sub_self _
    · change standardJetCR (zeroNormalize u.val) ∈ supportedHolder K
      rw [standardJetCR_zeroNormalize]
      exact u.property)

def freeCoordinates : freeModel (E := E) K →L[ℝ] E × markedModel (E := E) K :=
  ((jetEval 0).comp (freeModel (E := E) K).subtypeL).prod freeNormalize

def freeEquiv : freeModel (E := E) K ≃L[ℝ] E × markedModel (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse freeCoordinates freeSum
    (by
      intro v
      apply Subtype.ext
      apply cValue_ext
      intro z
      change cValue v.val 0+(cValue v.val z-cValue v.val 0)=cValue v.val z
      abel)
    (by
      intro v
      apply Prod.ext
      · change v.1+cValue v.2.val 0=v.1
        have hz : cValue v.2.val 0=0 := v.2.property.1
        rw [hz,add_zero]
      · apply Subtype.ext
        apply cValue_ext
        intro z
        change (v.1+cValue v.2.val z)-(v.1+cValue v.2.val 0)=cValue v.2.val z
        have hz : cValue v.2.val 0=0 := v.2.property.1
        rw [hz,add_zero]
        abel)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


