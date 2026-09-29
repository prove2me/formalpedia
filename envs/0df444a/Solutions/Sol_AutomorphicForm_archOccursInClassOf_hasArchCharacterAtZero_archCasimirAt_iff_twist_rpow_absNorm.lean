-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c74accae-0a7a-5c5b-8298-f466a847a261

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
p2m_attr_erase "instance" "LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace Ws23
namespace T1

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal NumberField.AdelicVolume Matrix
open LanglandsTunnell LanglandsTunnell.RealArchParam
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem agrees_twist {Θ' Θ : HeckeEigensystem F ℂ} (h : Θ'.AgreesAwayFromFinite Θ) (χ : HeightOneSpectrum (𝓞 F) → ℂ) :
    (Θ'.twist χ).AgreesAwayFromFinite (Θ.twist χ) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨by rw [HeckeEigensystem.twist_a, HeckeEigensystem.twist_a, (hS v hv).1],
    by rw [HeckeEigensystem.twist_b, HeckeEigensystem.twist_b, (hS v hv).2]⟩⟩

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
  Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot))

theorem rpow_neg_neg_mul_rpow_neg (v : HeightOneSpectrum (𝓞 F)) (t : ℝ) :
    ((((Ideal.absNorm v.asIdeal : ℝ) ^ (-(-t)) : ℝ) : ℂ)) * (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add (absNorm_pos v), neg_neg, add_neg_cancel, Real.rpow_zero, Complex.ofReal_one]

theorem twist_twist_agrees (Θ : HeckeEigensystem F ℂ) (t : ℝ) :
    ((Θ.twist fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)).twist
        fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(-t)) : ℝ) : ℂ)).AgreesAwayFromFinite Θ := by
  refine ⟨∅, fun v _ => ⟨?_, ?_⟩⟩
  · rw [HeckeEigensystem.twist_a, HeckeEigensystem.twist_a, ← mul_assoc, rpow_neg_neg_mul_rpow_neg, one_mul]
  · rw [HeckeEigensystem.twist_b, HeckeEigensystem.twist_b, ← mul_assoc, ← mul_pow, rpow_neg_neg_mul_rpow_neg, one_pow,
      one_mul]

def nu (g : AdelicGL2 (𝓞 F) F) : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g)

theorem nu_pos (g : AdelicGL2 (𝓞 F) F) : 0 < nu g := ideleNorm_pos _

theorem nu_mul (g h : AdelicGL2 (𝓞 F) F) : nu (g * h) = nu g * nu h := by
  simp only [nu, map_mul, ideleNorm_mul]

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F v (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne F hvw]

omit [NumberField F] in
theorem norm_det_glEquivOfRingEquiv_symm {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ‖((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  have e : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) =
      ((ringEquivRealOfIsReal hw).symm.toRingHom).mapMatrix ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [e, ← RingHom.map_det]
  have h := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
  rw [RingEquiv.apply_symm_apply] at h
  rw [show ((ringEquivRealOfIsReal hw).symm.toRingHom) ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
    (ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det from rfl, ← h, Real.norm_eq_abs]

theorem archDetNorm_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) (v : InfinitePlace F) :
    archDetNorm v (archRealGLAt hw m) = if v = w then |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| else 1 := by
  unfold archDetNorm
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl, archComponent_glArch_archRealGLAt_self, norm_det_glEquivOfRingEquiv_symm]
  · rw [if_neg hvw, archComponent_glArch_archRealGLAt_of_ne hvw, Units.val_one, Matrix.det_one, norm_one]

theorem nu_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    nu (archRealGLAt hw m : AdelicGL2 (𝓞 F) F) = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  unfold nu
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (archRealGLAt hw m)
    (by rw [show glFin (𝓞 F) F (archRealGLAt hw m) = 1 from glFin_adelicArchGLIncl F _]; exact Subgroup.one_mem _)]
  simp_rw [archDetNorm_archRealGLAt hw m]
  rw [Finset.prod_eq_single w]
  · rw [if_pos rfl, NumberField.InfinitePlace.mult, if_pos hw, pow_one]
  · intro v _ hvw
    rw [if_neg hvw, one_pow]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem nu_mul_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) (m : GL (Fin 2) ℝ) :
    nu (g * archRealGLAt hw m) = nu g * |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  rw [nu_mul, nu_archRealGLAt]

theorem det_archFlowMatrix (d : ArchDir) (t : ℝ) :
    ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  cases d
  · show ((splitTorusGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [splitTorusGL2, Matrix.det_fin_two_of, ← Real.exp_add]
  · show ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [unipotentGL2, Matrix.det_fin_two_of]
  · show ((lowerUnipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [lowerUnipotentGL2, Matrix.det_fin_two_of]

theorem nu_mul_archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    nu (g * archFlowAt hw d t) = nu g := by
  unfold archFlowAt
  rw [nu_mul_archRealGLAt, det_archFlowMatrix, abs_one, mul_one]

theorem nu_mul_adelicArchGLInclAt {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    nu (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = nu g := by
  rw [← archRealGLAt_glEquivOfRingEquiv hw, nu_mul_archRealGLAt]
  have hdet : (((k : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff _).1 k.2).1
  have e : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
        (((k : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
  rw [e, ← RingHom.map_det, hdet, map_one, abs_one, mul_one]

def twistFn (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((nu g ^ t : ℝ) : ℂ) * φ g

theorem hasArchCharacterAt₀_twistFn {w : InfinitePlace F} (hw : w.IsReal) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : HasArchCharacterAt₀ F w χ φ) (t : ℝ) : HasArchCharacterAt₀ F w χ (twistFn t φ) := by
  intro k g
  simp only [twistFn, nu_mul_adelicArchGLInclAt hw, h k g]
  ring

theorem archDerivAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (twistFn t φ) = twistFn t (archDerivAt hw d φ) := by
  funext g
  show deriv (fun s : ℝ => ((nu (g * archFlowAt hw d s) ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s)) 0 =
    ((nu g ^ t : ℝ) : ℂ) * deriv (fun s : ℝ => φ (g * archFlowAt hw d s)) 0
  have e : (fun s : ℝ => ((nu (g * archFlowAt hw d s) ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s)) =
      fun s => ((nu g ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s) := by
    funext s; rw [nu_mul_archFlowAt]
  rw [e, deriv_const_mul_field]

theorem archCasimirAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (twistFn t φ) = twistFn t (archCasimirAt hw φ) := by
  funext g
  simp only [archCasimirAt, archDerivAt_twistFn, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [twistFn, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem archCasimirAt_twistFn_of_eq {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} {lam : ℂ}
    (h : archCasimirAt hw φ = lam • φ) : archCasimirAt hw (twistFn t φ) = lam • twistFn t φ := by
  rw [archCasimirAt_twistFn, h]
  funext g
  simp only [twistFn, Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) := by
  have h : (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) = fun e => e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    funext e; simp [Matrix.det_fin_two]
  rw [h]
  have hp : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => e i j) := fun i j =>
    (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)
  exact ((hp 0 0).mul (hp 1 1)).sub ((hp 0 1).mul (hp 1 0))

theorem isArchSmoothAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (twistFn t φ) := by
  intro g
  have hform : ∀ e ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0},
      ((nu (g * archRealLiftAt hw e) ^ t : ℝ) : ℂ) = (((nu g * ‖(Matrix.of e).det‖) ^ t : ℝ) : ℂ) := by
    intro e he
    rw [archRealLiftAt_of_det_ne_zero hw he, nu_mul_archRealGLAt, Real.norm_eq_abs]
    rfl
  have hreal : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (nu g * ‖(Matrix.of e).det‖) ^ t)
      {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    have hne : (Matrix.of e).det ≠ 0 := he
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ‖(Matrix.of e).det‖) e :=
      (contDiffAt_norm ℝ hne).comp e contDiff_det_of.contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => nu g * ‖(Matrix.of e).det‖) e := contDiffAt_const.mul h1
    have hne' : nu g * ‖(Matrix.of e).det‖ ≠ 0 := mul_ne_zero (nu_pos g).ne' (norm_ne_zero_iff.mpr hne)
    exact (h2.rpow_const_of_ne hne').contDiffWithinAt
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ((nu (g * archRealLiftAt hw e) ^ t : ℝ) : ℂ))
      {e | (Matrix.of e).det ≠ 0} := by
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hreal).congr fun e he => ?_
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact hform e he
  exact hdet.mul (h g)

theorem occ_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (t : ℝ)
    (h : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (Θ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) := by
  obtain ⟨Θ', hΘ', R, hR, htyp, hsm, hΩ⟩ := h
  obtain ⟨R', hR', -, hfun⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul F c u d₁ d₂ T
      hd₁ Θ' R hR t
  have hfun' : R'.toFun = twistFn t R.toFun := funext hfun
  refine ⟨_, agrees_twist hΘ' _, R', hR', ?_, ?_, ?_⟩
  · rw [hfun']; exact hasArchCharacterAt₀_twistFn hw _ htyp t
  · rw [hfun']; exact isArchSmoothAt_twistFn hw t hsm
  · rw [hfun']; exact archCasimirAt_twistFn_of_eq hw t hΩ

theorem mainO (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (t : ℝ) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (Θ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) :=
  ⟨occ_twist c u d₁ d₂ T hd₁ Θ w hw n lam t, fun h => (occ_twist c u d₁ d₂ T hd₁ _ w hw n lam (-t) h).of_agrees (twist_twist_agrees Θ t)⟩

end Ws23.T1

end

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (t : ℝ) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (Θ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) :=
  Ws23.T1.mainO c u d₁ d₂ T hd₁ Θ w hw n lam t

end S_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm (solution)
