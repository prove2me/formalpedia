-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/18894f03-ee9d-5eed-8b3e-d02d0ab3e73d

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem OC.inner_eq {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ ψ : Lp ℂ 2 ν) (v w : X → ℂ)
    (hv : (φ : X → ℂ) =ᵐ[ν] v) (hw : (ψ : X → ℂ) =ᵐ[ν] w) :
    ⟪ψ, φ⟫_ℂ = ∫ g, v g * conj (w g) ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with g hgv hgw
  rw [RCLike.inner_apply, hgv, hgw]

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (x y : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK x)
    (_hxo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
    (_hy : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK y)
    (_hyc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (y - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (y g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 ∧
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, y g * conj (x g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by

  have hM : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK u →
      MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    fun u hu => ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu).2
  set ν := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hν
  have hxM := hM x _hx
  have hyM := hM y _hy
  set X : Lp ℂ 2 ν := hxM.toLp x with hX
  set Y : Lp ℂ 2 ν := hyM.toLp y with hY
  have hXae : (X : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[ν] x := MemLp.coeFn_toLp _
  have hYae : (Y : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[ν] y := MemLp.coeFn_toLp _
  have hinner : ⟪Y, X⟫_ℂ = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (y g)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := OC.inner_eq ν X Y x y hXae hYae

  have hsmall : ∀ ε > (0:ℝ), ‖⟪Y, X⟫_ℂ‖ ≤ ε * ‖X‖ := by
    intro ε hε
    obtain ⟨q, hqres, hqA, hq⟩ := _hyc ε hε
    have hqM := hM q hqA
    set Q : Lp ℂ 2 ν := hqM.toLp q with hQ
    have hQae : (Q : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[ν] q := MemLp.coeFn_toLp _
    have hQX : ⟪Q, X⟫_ℂ = 0 := by
      rw [OC.inner_eq ν X Q x q hXae hQae]
      exact _hxo q hqA hqres
    have hsplit : ⟪Y, X⟫_ℂ = ⟪Y - Q, X⟫_ℂ + ⟪Q, X⟫_ℂ := by rw [← inner_add_left, sub_add_cancel]
    rw [hsplit, hQX, add_zero]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have hYQ : Y - Q = (hyM.sub hqM).toLp (y - q) := by rw [hY, hQ, MemLp.toLp_sub]
    rw [hYQ, Lp.norm_toLp]
    have hlt := hq
    have hfin : eLpNorm (y - q) 2 ν ≠ ⊤ := (hyM.sub hqM).eLpNorm_ne_top
    have := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hlt
    rw [ENNReal.toReal_ofReal hε.le] at this
    exact this.le
  have hzero : ⟪Y, X⟫_ℂ = 0 := by
    by_contra hne
    have hpos : 0 < ‖⟪Y, X⟫_ℂ‖ := norm_pos_iff.2 hne
    have hXpos : 0 < ‖X‖ := by
      by_contra hX0
      have : ‖X‖ = 0 := le_antisymm (not_lt.1 hX0) (norm_nonneg _)
      have h := hsmall 1 one_pos
      rw [this, mul_zero] at h
      exact absurd (lt_of_lt_of_le hpos h) (lt_irrefl _)
    have h := hsmall (‖⟪Y, X⟫_ℂ‖ / (2 * ‖X‖)) (by positivity)
    rw [div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div] at h
    have : ‖X‖ / (2 * ‖X‖) = 1 / 2 := by field_simp
    nlinarith [h, this, hpos]
  have h1 : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (y g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    rw [← hinner]; exact hzero
  refine ⟨h1, ?_⟩
  have hconj := congrArg conj h1
  rw [map_zero, ← integral_conj] at hconj
  have heq : (fun g => conj (x g * conj (y g))) = fun g => y g * conj (x g) := by
    funext g; rw [map_mul, Complex.conj_conj, mul_comm]
  rwa [heq] at hconj

end S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure (solution)
