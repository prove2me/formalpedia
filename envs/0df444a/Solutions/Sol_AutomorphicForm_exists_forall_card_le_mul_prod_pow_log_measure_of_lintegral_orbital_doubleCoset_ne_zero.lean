-- Prove2me | solution 1 for AutomorphicForm.exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0f98b6cf-5a4c-5952-a509-587137647a31

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Theorems.Thm_AutomorphicForm_eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses
import Theorems.Thm_NumberField_exists_forall_card_le_mul_prod_of_forall_norm_eq_one_of_abs_log_norm_le
import Theorems.Thm_AutomorphicForm_exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace ClassCountGlue

open AutomorphicForm
open scoped TensorProduct.RightActions ENNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem one_le_semiLocalHaar_doubleCoset (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    1 ≤ semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  have hsub : a • semiLocalIntegralSet K L v ⊆ semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨1 * a, ⟨1, one_mem_semiLocalIntegralSet K L v, a, rfl, rfl⟩, k, hk, ?_⟩
    simp only [smul_eq_mul, one_mul]
  calc (1 : ℝ≥0∞) = semiLocalHaar K L v (semiLocalIntegralSet K L v) :=
        (semiLocalHaar_semiLocalIntegralSet K L v).symm
    _ = semiLocalHaar K L v (a • semiLocalIntegralSet K L v) := (measure_smul _ a _).symm
    _ ≤ _ := measure_mono hsub

theorem semiLocalHaar_doubleCoset_lt_top (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) < ∞ := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  exact (((isCompact_semiLocalIntegralSet K L v).mul isCompact_singleton).mul
    (isCompact_semiLocalIntegralSet K L v)).measure_lt_top

theorem log_toReal_semiLocalHaar_doubleCoset_nonneg (v : HeightOneSpectrum (𝓞 K))
    (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    0 ≤ Real.log (semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v)).toReal := by
  refine Real.log_nonneg ?_
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono (semiLocalHaar_doubleCoset_lt_top K L v a).ne (one_le_semiLocalHaar_doubleCoset K L v a)

theorem one_add_mul_le {A ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 1 + A * (1 + ℓ) ≤ (1 + A) * (1 + ℓ) := by
  nlinarith

theorem prod_union_ite {α β : Type*} [CommMonoid β] [DecidableEq α] (S T : Finset α) (X Y : α → β) :
    ∏ v ∈ S ∪ T, (if v ∈ T then X v else Y v) = (∏ v ∈ S \ T, Y v) * ∏ v ∈ T, X v := by
  rw [← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.mp hv).2
  · exact Finset.prod_congr rfl fun v hv => if_pos hv

end ClassCountGlue

end

open AutomorphicForm ClassCountGlue

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
        (∀ t ∈ Δφ,
          (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≠ 0) →
        (Δφ.card : ℝ) ≤ C * ∏ v ∈ T,
          ((1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A) := by
  intro T ws
  classical
  obtain ⟨A₀, hA₀, cS, cinf, hSB⟩ :=
    AutomorphicForm.exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T ws
  obtain ⟨C₁, hC₁, hUB⟩ :=
    NumberField.exists_forall_card_le_mul_prod_of_forall_norm_eq_one_of_abs_log_norm_le K (S ∪ T) cinf
  refine ⟨C₁ * (1 + max cS 0) ^ S.card * (1 + A₀) ^ T.card, by positivity, 1, ?_⟩
  intro ρ φ φf hfact Δφ hΔφ hne

  have hinj : Set.InjOn (fun t : GL (Fin 2) L =>
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)) ↑Δφ :=
    fun t ht t' ht' h =>
      AutomorphicForm.eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses K L σ hgen Δ hΔd hΔdisj
        t (hΔφ ht) t' (hΔφ ht') h
  have hcard := Finset.card_image_of_injOn hinj

  have hℓ : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal :=
    fun v => log_toReal_semiLocalHaar_doubleCoset_nonneg K L v _
  set c : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    if v ∈ T then A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) else max cS 0 with hc
  have hc0 : ∀ v, 0 ≤ c v := by
    intro v
    simp only [hc]
    split_ifs
    · exact mul_nonneg hA₀ (by linarith [hℓ v])
    · exact le_max_right _ _

  have hbox := hUB c hc0 (Δφ.image fun t : GL (Fin 2) L =>
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)) (by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h0, hunit, hT, hS, hinf⟩ := hSB ρ φ φf hfact t (hΔφ ht) (hne t ht)
    refine ⟨h0, fun v hv => hunit v hv, fun v hv => ?_, hinf⟩
    simp only [hc]
    split_ifs with hvT
    · exact hT v hvT
    · exact (hS v ((Finset.mem_union.mp hv).resolve_right hvT) hvT).trans (le_max_left _ _))
  rw [hcard] at hbox
  refine hbox.trans ?_

  have hsplit : ∏ v ∈ S ∪ T, (1 + c v) =
      (∏ v ∈ S \ T, (1 + max cS 0)) * ∏ v ∈ T, (1 + A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) := by
    have : (fun v => 1 + c v) = fun v => if v ∈ T then (1 + A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) else (1 + max cS 0) := by
      funext v; simp only [hc]; split_ifs <;> rfl
    rw [this, prod_union_ite]
  rw [hsplit, Finset.prod_const]
  have h1 : (1 + max cS 0) ^ (S \ T).card ≤ (1 + max cS 0) ^ S.card :=
    pow_le_pow_right₀ (by linarith [le_max_right cS 0]) (Finset.card_le_card Finset.sdiff_subset)
  have h2 : ∏ v ∈ T, (1 + A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) ≤
      (1 + A₀) ^ T.card * ∏ v ∈ T, (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ 1 := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => by linarith [mul_nonneg hA₀ (by linarith [hℓ v] : (0:ℝ) ≤ 1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)]) fun v _ => ?_
    rw [pow_one]
    exact one_add_mul_le (hℓ v)
  have h0' : 0 ≤ ∏ v ∈ T, (1 + A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) :=
    Finset.prod_nonneg fun v _ => by linarith [mul_nonneg hA₀ (by linarith [hℓ v] : (0:ℝ) ≤ 1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)]
  calc C₁ * ((1 + max cS 0) ^ (S \ T).card * ∏ v ∈ T, (1 + A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)))
      ≤ C₁ * ((1 + max cS 0) ^ S.card * ((1 + A₀) ^ T.card * ∏ v ∈ T, (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ 1)) := by
        gcongr
    _ = C₁ * (1 + max cS 0) ^ S.card * (1 + A₀) ^ T.card * ∏ v ∈ T, (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ 1 := by ring

end S_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero (solution)
