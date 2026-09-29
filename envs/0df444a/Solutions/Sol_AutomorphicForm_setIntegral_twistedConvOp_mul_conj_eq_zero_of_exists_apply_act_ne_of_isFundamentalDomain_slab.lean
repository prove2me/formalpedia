-- Prove2me | solution 1 for AutomorphicForm.setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/608ea176-e88e-5bde-843b-5b7f80d01a9d

import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate Pointwise NNReal ENNReal

noncomputable section

namespace R4VanSigma

section Norm

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem distribHaarChar_ringEquiv (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L)
    (hθ : Continuous θ) (hθ' : Continuous θ.symm) (z : (AdeleRing (𝓞 L) L)ˣ) :
    distribHaarChar (AdeleRing (𝓞 L) L)
        (Units.map (θ.toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) =
      distribHaarChar (AdeleRing (𝓞 L) L) z := by
  set ν : Measure (AdeleRing (𝓞 L) L) := adelicAddHaar (𝓞 L) L with hν
  haveI : ν.IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 L) L
  haveI : ν.Regular := by
    rw [hν]
    dsimp only [adelicAddHaar, Measure.addHaar]
    infer_instance

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs_int : (interior s).Nonempty := ⟨0, mem_interior_iff_mem_nhds.mpr hs_mem⟩
  have hs0 : ν s ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν hs_int).ne'
  have hstop : ν s ≠ ∞ := hs_compact.measure_lt_top.ne
  have hs_meas : MeasurableSet s := hs_compact.isClosed.measurableSet
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) hs0 hstop ?_

  let e : AdeleRing (𝓞 L) L ≃+ AdeleRing (𝓞 L) L := θ.symm.toAddEquiv
  have he : Continuous e := hθ'
  have he' : Continuous e.symm := hθ
  let ν' : Measure (AdeleRing (𝓞 L) L) := Measure.map e ν
  haveI : ν'.IsAddHaarMeasure := e.isAddHaarMeasure_map ν he he'
  haveI : ν'.Regular := Measure.Regular.map (Homeomorph.mk e.toEquiv he he')
  have hθs : MeasurableSet (θ ⁻¹' s) := hs_meas.preimage hθ.measurable
  have hzθs : MeasurableSet (z • (θ ⁻¹' s)) := by
    have : z • (θ ⁻¹' s) = (fun a => z⁻¹ • a) ⁻¹' (θ ⁻¹' s) := by
      ext a
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    rw [this]
    exact hθs.preimage (measurable_const_smul _)
  have hset : (Units.map (θ.toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) • s =
      e ⁻¹' (z • (θ ⁻¹' s)) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_smul_set, Units.smul_def, smul_eq_mul, Units.coe_map,
      MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨θ.symm b, by simpa using hb, ?_⟩
      show (z : AdeleRing (𝓞 L) L) * θ.symm b = θ.symm (θ z * b)
      rw [map_mul, RingEquiv.symm_apply_apply]
    · rintro ⟨c, hc, hca⟩
      refine ⟨θ c, hc, ?_⟩
      have : θ (↑z * c) = θ (e a) := congrArg θ hca
      simpa [map_mul, e] using this
  rw [hset, ← Measure.map_apply he.measurable hzθs]
  show ν' (z • (θ ⁻¹' s)) = _
  rw [← distribHaarChar_mul ν' z (θ ⁻¹' s)]
  congr 1
  show Measure.map e ν (θ ⁻¹' s) = ν s
  rw [Measure.map_apply he.measurable hθs]
  congr 1
  ext a
  simp [e]

theorem ideleNorm_ringEquiv (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L)
    (hθ : Continuous θ) (hθ' : Continuous θ.symm) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L
        (Units.map (θ.toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) =
      NumberField.TateGlobal.ideleNorm L z := by
  simp only [NumberField.TateGlobal.ideleNorm, distribHaarChar_ringEquiv θ hθ hθ' z]

end Norm

section Slab

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

def slab (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z * z := by
  refine Units.ext ?_
  simp [AutomorphicForm.centralScalar, pow_two]

theorem centralScalar_mul_mem_slab_iff {α β : ℝ} {z : (AdeleRing (𝓞 L) L)ˣ}
    (hz : NumberField.TateGlobal.ideleNorm L z = 1) (x : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar,
    hz, one_mul]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r => mul_comm _ r) _).eq

scoped instance smulInvariantMeasure_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ slab L α β =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem setIntegral_eq_of_isFundamentalDomain {α β : ℝ} {Φ₀ Φ₁ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (hΦ₁s : Φ₁ ⊆ slab L α β)
    (hΦ₁ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₁
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hF : ∀ (γ : GL (Fin 2) L) (x), F (globalPoints (𝓞 L) L γ * x) = F x) :
    ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = ∫ x in Φ₁, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have h := hΦ₀.setIntegral_eq hΦ₁ (f := F) (fun γ x => by
    obtain ⟨g, γ₀, rfl⟩ := γ
    exact hF γ₀ x)
  rwa [Measure.restrict_restrict_of_subset hΦ₀s, Measure.restrict_restrict_of_subset hΦ₁s] at h

theorem measurePreserving_centralScalar_mul {α β : ℝ} {z : (AdeleRing (𝓞 L) L)ˣ}
    (hz : NumberField.TateGlobal.ideleNorm L z = 1) :
    MeasurePreserving (fun x => centralScalar (𝓞 L) L z * x)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  have h := (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 L) L)
    (centralScalar (𝓞 L) L z)).restrict_preimage (measurableSet_slab (L := L) α β)
  have hpre : (fun x => centralScalar (𝓞 L) L z * x) ⁻¹' slab L α β = slab L α β := by
    ext x
    exact centralScalar_mul_mem_slab_iff hz x
  rwa [hpre] at h

theorem isFundamentalDomain_image_centralScalar {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    {z : (AdeleRing (𝓞 L) L)ˣ} (hz : NumberField.TateGlobal.ideleNorm L z = 1) :
    IsFundamentalDomain (globalPoints (𝓞 L) L).range
      ((fun x => centralScalar (𝓞 L) L z * x) '' Φ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  have hz' : NumberField.TateGlobal.ideleNorm L z⁻¹ = 1 := by
    have h1 := NumberField.TateGlobal.ideleNorm_mul z z⁻¹
    rw [mul_inv_cancel, hz, one_mul] at h1
    rw [← h1]
    exact NumberField.TateGlobal.ideleNorm_one L
  have hq : Measure.QuasiMeasurePreserving (Equiv.mulLeft (centralScalar (𝓞 L) L z)).symm
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
    have h := measurePreserving_centralScalar_mul (α := α) (β := β) hz'
    rw [map_inv] at h
    exact h.quasiMeasurePreserving
  refine hΦ₀.image_of_equiv (Equiv.mulLeft (centralScalar (𝓞 L) L z)) hq (Equiv.refl _) ?_
  intro γ x
  obtain ⟨g, γ₀, rfl⟩ := γ
  show centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L γ₀ * x) =
    globalPoints (𝓞 L) L γ₀ * (centralScalar (𝓞 L) L z * x)
  rw [← mul_assoc, centralScalar_mul_comm, mul_assoc]

theorem setIntegral_eq_mul_setIntegral {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    {z : (AdeleRing (𝓞 L) L)ˣ} (hz : NumberField.TateGlobal.ideleNorm L z = 1)
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hF : ∀ (γ : GL (Fin 2) L) (x), F (globalPoints (𝓞 L) L γ * x) = F x)
    (c : ℂ) (hFz : ∀ x, F (centralScalar (𝓞 L) L z * x) = c * F x) :
    ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = c * ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have h1s : (fun x => centralScalar (𝓞 L) L z * x) '' Φ₀ ⊆ slab L α β := by
    rintro _ ⟨x, hx, rfl⟩
    exact (centralScalar_mul_mem_slab_iff hz x).2 (hΦ₀s hx)
  calc ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
        = ∫ x in (fun x => centralScalar (𝓞 L) L z * x) '' Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
          setIntegral_eq_of_isFundamentalDomain hΦ₀s hΦ₀ h1s
            (isFundamentalDomain_image_centralScalar hΦ₀ hz) F hF
    _ = ∫ x in Φ₀, F (centralScalar (𝓞 L) L z * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
          (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 L) L)
            (centralScalar (𝓞 L) L z)).setIntegral_image_emb
            (MeasurableEquiv.mulLeft (centralScalar (𝓞 L) L z)).measurableEmbedding F Φ₀
    _ = ∫ x in Φ₀, c * F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by simp_rw [hFz]
    _ = c * ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := integral_const_mul c _

theorem integrableOn_of_isFundamentalDomain {α β : ℝ} {Φ₀ Φ₁ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (hΦ₁ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₁
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (G : AdelicGL2 (𝓞 L) L → ℝ) (hG : ∀ (γ : GL (Fin 2) L) (x), G (globalPoints (𝓞 L) L γ * x) = G x)
    (hint : IntegrableOn G Φ₁ (adelicGLHaar (Fin 2) (𝓞 L) L)) :
    IntegrableOn G Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have h1 : IntegrableOn G Φ₁ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
    refine hint.mono_measure ?_
    exact Measure.restrict_le_self
  have h0 := (hΦ₁.integrableOn_iff hΦ₀ (f := G) (fun γ x => by
    obtain ⟨g, γ₀, rfl⟩ := γ
    exact hG γ₀ x)).1 h1
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hΦ₀s] at h0

end Slab

section Extend

variable {L : Type} [Field L] [NumberField L]

theorem ideleNorm_pow (z : (AdeleRing (𝓞 L) L)ˣ) (n : ℕ) :
    NumberField.TateGlobal.ideleNorm L (z ^ n) = NumberField.TateGlobal.ideleNorm L z ^ n := by
  induction n with
  | zero => simp [NumberField.TateGlobal.ideleNorm_one L]
  | succ n ih => rw [pow_succ, NumberField.TateGlobal.ideleNorm_mul, ih, pow_succ]

theorem eq_one_of_normOne_of_pow {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ}
    (h1 : ∀ z, NumberField.TateGlobal.ideleNorm L z = 1 → χ z = 1)
    {n : ℕ} (hn : 0 < n) (hpow : ∀ z, χ z ^ n = 1) (z : (AdeleRing (𝓞 L) L)ˣ) : χ z = 1 := by

  have hr : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos z
  obtain ⟨w, -, hw⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one L
    (NumberField.TateGlobal.ideleNorm L z ^ ((n : ℝ)⁻¹)) (Real.rpow_pos_of_pos hr _)
  have hwn : NumberField.TateGlobal.ideleNorm L (w ^ n) = NumberField.TateGlobal.ideleNorm L z := by
    rw [ideleNorm_pow, hw, Real.rpow_inv_natCast_pow hr.le hn.ne']

  have hu : NumberField.TateGlobal.ideleNorm L ((w ^ n)⁻¹ * z) = 1 := by
    have h := NumberField.TateGlobal.ideleNorm_mul (w ^ n) ((w ^ n)⁻¹ * z)
    rw [mul_inv_cancel_left, hwn] at h
    exact (mul_eq_left₀ hr.ne').mp h.symm
  have hz : z = w ^ n * ((w ^ n)⁻¹ * z) := by rw [mul_inv_cancel_left]
  rw [hz, map_mul, h1 _ hu, mul_one, map_pow, hpow]

end Extend

section Twist

variable {L : Type} [Field L] [NumberField L]
variable {K : Type} [Field K] [Algebra K L] {D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L}

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem sigmaAdelicAct_centralScalar (τ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D τ (centralScalar (𝓞 L) L w) =
      centralScalar (𝓞 L) L
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) w) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom w

theorem twistedConvOp_centralScalar_mul (σ : L ≃ₐ[K] L)
    {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} (φ u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ u (centralScalar (𝓞 L) L z * x) =
      ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
        twistedConvOp K L D σ φ u x := by
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  simp only [sigmaSectionActOn, Function.comp_apply, map_mul, sigmaAdelicAct_centralScalar σ z,
    mul_assoc]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [hu.central_transform ⟨_, Subgroup.mem_top _⟩, mul_assoc]

theorem twistedConvOp_globalPoints_mul (σ : L ≃ₐ[K] L)
    {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} (φ u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ u (globalPoints (𝓞 L) L γ * x) = twistedConvOp K L D σ φ u x := by
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  simp only [sigmaSectionActOn, Function.comp_apply, map_mul, mul_assoc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) from
    sigmaAdelicAct_globalPoints K L D σ γ, hu.left_invariant]

theorem iterate_unitsMap_act (σ : L ≃ₐ[K] L) (k : ℕ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
        AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L))^[k] z =
      Units.map ((D.act (σ ^ k) : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
        AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z := by
  induction k with
  | zero =>
    refine Units.ext ?_
    simp [RingAut.one_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Units.ext ?_
    simp [pow_succ', map_mul, RingAut.mul_apply]

end Twist

end R4VanSigma
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab.R4VanSigma"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab.R4VanSigma"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open R4VanSigma in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ ≠
        ξL ⟨z, Subgroup.mem_top z⟩)
    (u v : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (hv : IsLsXiFunction (𝓞 L) L ⊤ ξL v)
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) :
    ∫ x in Φ₀, twistedConvOp K L D σ φ u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  classical
  haveI := isHaar (L := L)

  set θu : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
      AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) with hθu
  set ξf : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξf
  set A := twistedConvOp K L D σ φ u with hA
  set F : AdelicGL2 (𝓞 L) L → ℂ := fun x => A x * conj (v x) with hF
  set G : AdelicGL2 (𝓞 L) L → ℂ := fun x => v x * conj (v x) with hG

  have hFγ : ∀ (γ : GL (Fin 2) L) (x), F (globalPoints (𝓞 L) L γ * x) = F x := by
    intro γ x
    simp only [hF, hA, twistedConvOp_globalPoints_mul σ φ u hu, hv.left_invariant]
  have hFz : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x),
      F (centralScalar (𝓞 L) L z * x) = (ξf (θu z) * conj (ξf z)) * F x := by
    intro z x
    simp only [hF, hA, hξf, hθu, twistedConvOp_centralScalar_mul σ φ u hu,
      hv.central_transform ⟨z, Subgroup.mem_top z⟩, map_mul]
    ring
  have hGγ : ∀ (γ : GL (Fin 2) L) (x), G (globalPoints (𝓞 L) L γ * x) = G x := by
    intro γ x
    simp only [hG, hv.left_invariant]
  have hGz : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x),
      G (centralScalar (𝓞 L) L z * x) = (ξf z * conj (ξf z)) * G x := by
    intro z x
    simp only [hG, hξf, hv.central_transform ⟨z, Subgroup.mem_top z⟩, map_mul]
    ring

  by_cases hI : ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0
  · exact hI
  exfalso

  have hvint : IntegrableOn (fun x => ‖v x‖ ^ 2) Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) :=
    integrableOn_of_isFundamentalDomain (α := α) (β := β) hΦ₀s hΦ₀ hΦ (fun x => ‖v x‖ ^ 2)
      (fun γ x => by simp only [hv.left_invariant])
      ((memLp_two_iff_integrable_sq_norm hv₂.1).1 hv₂)
  have hGpos : ∫ x in Φ₀, (‖v x‖ ^ 2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ 0 := by
    intro h0
    apply hI
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖v x‖) hvint).1 h0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    have hx0 : v x = 0 := by simpa [sq_eq_zero_iff, norm_eq_zero] using hx
    simp [hF, hx0]
  have hGc : ∫ x in Φ₀, G x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ((∫ x in Φ₀, (‖v x‖ ^ 2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hG, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hGne : ∫ x in Φ₀, G x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ 0 := by
    rw [hGc]
    exact_mod_cast hGpos

  have hunit : ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z = 1 →
      ξf z * conj (ξf z) = 1 := by
    intro z hz
    have h := setIntegral_eq_mul_setIntegral (α := α) (β := β) hΦ₀s hΦ₀ hz G hGγ _ (hGz z)
    exact (mul_eq_right₀ hGne).1 h.symm

  have hone : ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z = 1 →
      ξf (θu z) = ξf z := by
    intro z hz
    have h := setIntegral_eq_mul_setIntegral (α := α) (β := β) hΦ₀s hΦ₀ hz F hFγ _ (hFz z)
    have hc : ξf (θu z) * conj (ξf z) = 1 := (mul_eq_right₀ hI).1 h.symm
    have hu1 := hunit z hz
    calc ξf (θu z) = ξf (θu z) * (ξf z * conj (ξf z)) := by rw [hu1, mul_one]
      _ = (ξf (θu z) * conj (ξf z)) * ξf z := by ring
      _ = ξf z := by rw [hc, one_mul]

  let ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ :=
    ξL.comp (Subgroup.topEquiv (G := (AdeleRing (𝓞 L) L)ˣ)).symm.toMonoidHom
  have hξ' : ∀ z, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  let χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := (ξ'.comp θu) / ξ'
  have hχ : ∀ z, χ z = ξ' (θu z) / ξ' z := fun z => rfl
  have hχ1 : ∀ z, NumberField.TateGlobal.ideleNorm L z = 1 → χ z = 1 := by
    intro z hz
    rw [hχ, div_eq_one]
    exact Units.val_injective (hone z hz)

  have hθc : Continuous ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) :=
    D.continuous_act σ
  have hθc' : Continuous ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).symm :
      AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) := by
    have h := D.continuous_act σ⁻¹
    rw [map_inv] at h
    exact h
  have hθn : ∀ z, NumberField.TateGlobal.ideleNorm L (θu z) = NumberField.TateGlobal.ideleNorm L z :=
    fun z => ideleNorm_ringEquiv (D.act σ : RingAut (AdeleRing (𝓞 L) L)) hθc hθc' z
  have hχnorm : ∀ z w : (AdeleRing (𝓞 L) L)ˣ,
      NumberField.TateGlobal.ideleNorm L z = NumberField.TateGlobal.ideleNorm L w → χ z = χ w := by
    intro z w hzw
    have h1 : NumberField.TateGlobal.ideleNorm L (w⁻¹ * z) = 1 := by
      have h := NumberField.TateGlobal.ideleNorm_mul w (w⁻¹ * z)
      rw [mul_inv_cancel_left, hzw] at h
      exact ((mul_eq_left₀ (NumberField.TateGlobal.ideleNorm_pos w).ne').mp h.symm)
    calc χ z = χ (w * (w⁻¹ * z)) := by rw [mul_inv_cancel_left]
      _ = χ w * χ (w⁻¹ * z) := map_mul χ _ _
      _ = χ w := by rw [hχ1 _ h1, mul_one]
  have hθn_iter : ∀ (k : ℕ) (z), NumberField.TateGlobal.ideleNorm L (θu^[k] z) =
      NumberField.TateGlobal.ideleNorm L z := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih => intro z; rw [Function.iterate_succ_apply', hθn, ih]

  have hiter : ∀ (k : ℕ) (z), ξ' (θu^[k] z) = χ z ^ k * ξ' z := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply']
      have h1 : ξ' (θu (θu^[k] z)) = χ (θu^[k] z) * ξ' (θu^[k] z) := by
        rw [hχ, div_mul_cancel]
      rw [h1, hχnorm _ z (hθn_iter k z), ih, pow_succ]
      group

  have hn : 0 < orderOf σ := orderOf_pos σ
  have hθpow : ∀ z, θu^[orderOf σ] z = z := by
    intro z
    rw [hθu, iterate_unitsMap_act σ (orderOf σ) z, pow_orderOf_eq_one, map_one]
    refine Units.ext ?_
    simp [RingAut.one_apply]
  have hpow : ∀ z, χ z ^ orderOf σ = 1 := by
    intro z
    have h := hiter (orderOf σ) z
    rw [hθpow] at h
    exact (right_eq_mul.mp h).symm ▸ rfl

  have hχall := eq_one_of_normOne_of_pow hχ1 hn hpow
  obtain ⟨z₀, hz₀⟩ := hne
  apply hz₀
  have h := hχall z₀
  rw [hχ, div_eq_one] at h
  exact h

end S_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab (solution)
