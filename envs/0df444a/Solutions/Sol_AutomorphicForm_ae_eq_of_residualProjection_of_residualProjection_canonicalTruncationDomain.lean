-- Prove2me | solution 1 for AutomorphicForm.ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/963b6d75-2cab-512f-954d-5163ce757c0a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
noncomputable section

namespace ResProjUniqueAux
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem memLp_conj {μ : Measure α} {v : α → ℂ} (hv : MemLp v 2 μ) :
    MemLp (fun a => conj (v a)) 2 μ :=
  MemLp.of_le hv (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)
    (Filter.Eventually.of_forall fun a => by simp)

theorem integrable_mul_conj {μ : Measure α} {F v : α → ℂ}
    (hF : MemLp F 2 μ) (hv : MemLp v 2 μ) : Integrable (fun a => F a * conj (v a)) μ := by
  have h : MemLp (F * fun a => conj (v a)) 1 μ := MemLp.mul (memLp_conj hv) hF
  rw [memLp_one_iff_integrable] at h
  exact h

theorem norm_integral_mul_conj_le (μ : Measure α) (F v : α → ℂ)
    (hF : MemLp F 2 μ) (hv : MemLp v 2 μ) :
    ‖∫ a, F a * conj (v a) ∂μ‖ ≤ (eLpNorm F 2 μ).toReal * (eLpNorm v 2 μ).toReal := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hv.toLp v) (hF.toLp F)
  rw [MeasureTheory.L2.inner_def] at h
  have hc : ∫ a, (inner ℂ ((hv.toLp v) a) ((hF.toLp F) a)) ∂μ = ∫ a, F a * conj (v a) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, hF.coeFn_toLp] with a ha hb
    rw [ha, hb, RCLike.inner_apply]
  rw [hc, Lp.norm_toLp, Lp.norm_toLp, mul_comm] at h
  exact h

theorem integral_mul_conj_eq_zero_of_approx {μ : Measure α} {d p : α → ℂ}
    (hd : MemLp d 2 μ) (hp : MemLp p 2 μ)
    (happrox : ∀ ε > (0:ℝ), ∃ r : α → ℂ, MemLp r 2 μ ∧ eLpNorm (p - r) 2 μ < ENNReal.ofReal ε ∧
      ∫ a, d a * conj (r a) ∂μ = 0) :
    ∫ a, d a * conj (p a) ∂μ = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  set W : ℝ := (eLpNorm d 2 μ).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  obtain ⟨r, hr, hlt, horth⟩ := happrox (ε / (W + 1)) (by positivity)
  have i1 := integrable_mul_conj hd (hp.sub hr)
  have i2 := integrable_mul_conj hd hr
  have hsplit : ∫ a, d a * conj (p a) ∂μ =
      ∫ a, d a * conj ((p - r) a) ∂μ + ∫ a, d a * conj (r a) ∂μ := by
    rw [← integral_add i1 i2]
    congr 1; funext a; simp only [Pi.sub_apply, map_sub]; ring
  rw [hsplit, horth, add_zero]
  have hcs := norm_integral_mul_conj_le μ d (p - r) hd (hp.sub hr)
  have hpr : (eLpNorm (p - r) 2 μ).toReal ≤ ε / (W + 1) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hlt.le
  calc ‖∫ a, d a * conj ((p - r) a) ∂μ‖
      ≤ W * (eLpNorm (p - r) 2 μ).toReal := hcs
    _ ≤ W * (ε / (W + 1)) := by gcongr
    _ < 0 + ε := by
        rw [zero_add]
        have hW1 : 0 < W + 1 := by positivity
        calc W * (ε / (W + 1)) = (W / (W + 1)) * ε := by ring
          _ < 1 * ε := by
              gcongr
              rw [div_lt_one hW1]; linarith
          _ = ε := one_mul ε

theorem ae_eq_zero_of_integral_mul_conj_self_eq_zero {μ : Measure α} {d : α → ℂ}
    (hd : MemLp d 2 μ) (h : ∫ a, d a * conj (d a) ∂μ = 0) : d =ᵐ[μ] 0 := by
  have hPn : ‖hd.toLp d‖ ^ 2 = RCLike.re (∫ a, d a * conj (d a) ∂μ) := by
    rw [← @inner_self_eq_norm_sq ℂ, MeasureTheory.L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp] with a ha
    rw [ha, RCLike.inner_apply]
  rw [h, map_zero, sq_eq_zero_iff, norm_eq_zero] at hPn
  have h0 : (hd.toLp d : α → ℂ) =ᵐ[μ] 0 := by
    rw [hPn]; exact Lp.coeFn_zero _ _ _
  exact hd.coeFn_toLp.symm.trans h0

end ResProjUniqueAux

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (p p' : AdelicGL2 (𝓞 K) K → ℂ)
    (_hp : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p) (_hp' : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p')
    (_hpc : (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε))
    (_hpo : (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0))
    (_hp'c : (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p' - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε))
    (_hp'o : (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p' g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) :
    p' =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] p := by
  have hmem : ∀ {w : AdelicGL2 (𝓞 K) K → ℂ}, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w → MemLp w 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    fun {w} hw => ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
      (AutomorphicForm.canonicalTruncationDomain K α β) w).1 hw).2
  have hθ := hmem _hθ
  have hp := hmem _hp
  have hp' := hmem _hp'

  have hd : MemLp (fun g => p g - p' g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := hp.sub hp'
  have horth_r : ∀ r : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r →
      r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
      ∫ g, (p g - p' g) * conj (r g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 := by
    intro r hr hres
    have h1 := _hpo r hr hres
    have h2 := _hp'o r hr hres
    have hrm := hmem hr
    have i1 := ResProjUniqueAux.integrable_mul_conj (hθ.sub hp') hrm
    have i2 := ResProjUniqueAux.integrable_mul_conj (hθ.sub hp) hrm
    have : (fun g => (p g - p' g) * conj (r g)) = fun g => (θ - p') g * conj (r g) - (θ - p) g * conj (r g) := by
      funext g; simp only [Pi.sub_apply]; ring
    rw [this, integral_sub i1 i2]
    have h1' : ∫ g, (θ - p) g * conj (r g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 := by simpa only [Pi.sub_apply] using h1
    have h2' : ∫ g, (θ - p') g * conj (r g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 := by simpa only [Pi.sub_apply] using h2
    rw [h1', h2', sub_zero]

  have hdp : ∫ g, (p g - p' g) * conj (p g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 :=
    ResProjUniqueAux.integral_mul_conj_eq_zero_of_approx hd hp fun ε hε => by
      obtain ⟨r, hres, hr, hlt⟩ := _hpc ε hε
      exact ⟨r, hmem hr, hlt, horth_r r hr hres⟩
  have hdp' : ∫ g, (p g - p' g) * conj (p' g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 :=
    ResProjUniqueAux.integral_mul_conj_eq_zero_of_approx hd hp' fun ε hε => by
      obtain ⟨r, hres, hr, hlt⟩ := _hp'c ε hε
      exact ⟨r, hmem hr, hlt, horth_r r hr hres⟩
  have hdd : ∫ g, (p g - p' g) * conj (p g - p' g) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = 0 := by
    have i1 := ResProjUniqueAux.integrable_mul_conj hd hp
    have i2 := ResProjUniqueAux.integrable_mul_conj hd hp'
    have : (fun g => (p g - p' g) * conj (p g - p' g)) = fun g => (p g - p' g) * conj (p g) - (p g - p' g) * conj (p' g) := by
      funext g; simp only [map_sub]; ring
    rw [this, integral_sub i1 i2, hdp, hdp', sub_zero]
  have h0 := ResProjUniqueAux.ae_eq_zero_of_integral_mul_conj_self_eq_zero hd hdd
  filter_upwards [h0] with g hg
  have : p g - p' g = 0 := by simpa using hg
  exact (sub_eq_zero.mp this).symm

end

end S_AutomorphicForm_ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain (solution)
