-- Prove2me | solution 1 for AutomorphicForm.ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e8a8b785-d610-5cc5-ad23-7ddd0cf16761

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

import Theorems.Thm_AutomorphicForm_coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace L3D1

open AutomorphicForm

section Centralizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem t2Space_GL : T2Space (GL (Fin 2) (v.adicCompletion K)) := inferInstance

attribute [local instance] AutomorphicForm.locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  AutomorphicForm.localCentralizerBorel

theorem isClosed_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) :=
  Set.isClosed_centralizer _

theorem isClosedEmbedding_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    Topology.IsClosedEmbedding ((↑) : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) :=
  (isClosed_localCentralizer K v γ).isClosedEmbedding_subtypeVal

theorem locallyCompactSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    LocallyCompactSpace (localCentralizer K v γ) :=
  (isClosedEmbedding_localCentralizer K v γ).locallyCompactSpace

theorem borelSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (localCentralizer K v γ) _ (localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (localCentralizerBorel K v γ) rfl

attribute [local instance] locallyCompactSpace_localCentralizer borelSpace_localCentralizer

def centralizerUnits (γ : GL (Fin 2) (v.adicCompletion K)) : Set (localCentralizer K v γ) :=
  {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v}

theorem isCompact_centralizerUnits (γ : GL (Fin 2) (v.adicCompletion K)) : IsCompact (centralizerUnits K v γ) :=
  (isClosedEmbedding_localCentralizer K v γ).isCompact_preimage (isCompact_localIntegralSet K v)

theorem isOpen_centralizerUnits (γ : GL (Fin 2) (v.adicCompletion K)) : IsOpen (centralizerUnits K v γ) :=
  (isOpen_localIntegralSet K v).preimage continuous_subtype_val

theorem one_mem_centralizerUnits (γ : GL (Fin 2) (v.adicCompletion K)) : (1 : localCentralizer K v γ) ∈
    centralizerUnits K v γ :=
  one_mem_localIntegralSet K v

def unitsPC (γ : GL (Fin 2) (v.adicCompletion K)) : TopologicalSpace.PositiveCompacts (localCentralizer K v γ) :=
  ⟨⟨centralizerUnits K v γ, isCompact_centralizerUnits K v γ⟩, by
    rw [(isOpen_centralizerUnits K v γ).interior_eq]
    exact ⟨1, one_mem_centralizerUnits K v γ⟩⟩

theorem exists_haar_mass_one (γ : GL (Fin 2) (v.adicCompletion K)) :
    ∃ τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ ∧
      τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} = 1 := by
  refine ⟨Measure.haarMeasure (unitsPC K v γ), Measure.isHaarMeasure_haarMeasure _, ?_⟩
  exact Measure.haarMeasure_self

end Centralizer

theorem isRegularSemisimple_diagUnits2 {F : Type*} [Field F] {a b : Fˣ} (hab : a ≠ b) :
    IsRegularSemisimple (diagUnits2 a b) := by
  rw [isRegularSemisimple_iff_ne_zero, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of,
    Matrix.det_fin_two_of]
  have hab' : (a : F) - b ≠ 0 := sub_ne_zero.2 fun h => hab (Units.val_injective h)
  have : ((a : F) + b) ^ 2 - 4 * ((a : F) * b - 0 * 0) = ((a : F) - b) ^ 2 := by ring
  rw [this]
  exact pow_ne_zero 2 hab'

theorem isRegularSemisimple_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) : IsRegularSemisimple (toTensorGL K L A g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom := rfl
  have h2 : ((g : Matrix (Fin 2) (Fin 2) A).map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom).det =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom (g : Matrix (Fin 2) (Fin 2) A).det := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_det]
  rw [hval, ← AddMonoidHom.map_trace, h2]
  convert hg.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom using 1
  simp [map_sub, map_pow, map_mul, map_ofNat]

end L3D1

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
      ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
      ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
        @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
        τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
      ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
        ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * I' =
          AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a (a * t) := by
  intro a t ht α β hN τ' hτ' hτ'1 I' hI'

  have hab : a ≠ a * t := by
    intro h; apply ht; exact (mul_eq_left.1 h.symm)
  have hσ : σ ≠ 1 := by
    intro h
    have hall : ∀ τ₀ : L ≃ₐ[K] L, τ₀ = 1 := fun τ₀ => by
      have := hgen τ₀
      rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
      exact this
    have hcard : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1, hall⟩
    rw [IsGalois.card_aut_eq_finrank] at hcard
    exact Nat.not_prime_one (hcard ▸ hdeg)
  have hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) := L3D1.isRegularSemisimple_diagUnits2 hab
  have hregN : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β)) := by
    rw [hN]; exact L3D1.isRegularSemisimple_toTensorGL K L (v.adicCompletion K) hreg
  have hconj : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 := by
    show AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) =
      1⁻¹ * AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) * 1
    rw [hN, inv_one, one_mul, mul_one]

  obtain ⟨τ, hτ, hτ1⟩ := L3D1.exists_haar_mass_one K v (diagUnits2 a (a * t))
  have hcpl := AutomorphicForm.coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one K L σ hgen hdeg hσ
    v a (a * t) hab α β hN τ hτ hτ1 τ' hτ' hτ'1

  obtain ⟨I, hI⟩ := @AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K _ _ v
    (diagUnits2 a (a * t)) hreg τ hτ f hf
  have hI_on : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v)
      (diagUnits2 a (a * t)) τ f I := by
    obtain ⟨w, hw, hIw⟩ := hI
    exact ⟨w, hw, hIw⟩
  have hEq : I' = I := hmatch.1 (diagUnits2 α β) hregN (diagUnits2 a (a * t)) hreg 1 hconj τ τ' hτ hτ' hcpl I I' hI' hI_on

  have hsplit := AutomorphicForm.LocalWeightedOrbital.eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2 K v a (a * t) hab τ hτ
    μ f hf I hI
  have hratio : AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) ≠ 0 := by
    unfold AutomorphicForm.LocalWeightedOrbital.ratio
    rw [norm_ne_zero_iff, sub_ne_zero, Units.val_mul, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    exact fun h => ht (Units.val_injective h.symm)
  rw [hEq, hsplit, hτ1, hμ]
  simp only [ENNReal.toReal_one, inv_one, one_mul]
  rw [← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hratio), one_mul]

end S_AutomorphicForm_ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal (solution)
