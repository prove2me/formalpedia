-- Prove2me | solution 1 for AutomorphicForm.rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/42a8f4dd-6a33-5d90-aa01-8b4212123ef7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
open AutomorphicForm

namespace KStabKit

open FLT.SmoothVectors

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem glInf_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (hh : ∀ w : InfinitePlace F, archComponent F w g = archComponent F w h) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (hh w)
  simpa [archComponent_apply] using this

theorem finEntry_eq {g h : AdelicGL2 (𝓞 F) F}
    (h₂ : glFin (𝓞 F) F g = glFin (𝓞 F) F h) (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 := by
  have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  simpa [glFin_apply] using this

theorem adelicGL2_ext' {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h) (h₂ : glFin (𝓞 F) F g = glFin (𝓞 F) F h) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · exact finEntry_eq h₂ i j

theorem glFin_inclAt (w : InfinitePlace F) (r : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w r) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem archComponent_inclAt_self (w : InfinitePlace F) (r : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w r)) = r := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_inclAt_of_ne {w w' : InfinitePlace F} (h : w' ≠ w) (r : GL (Fin 2) w.Completion) :
    archComponent F w' (glArch (𝓞 F) F (adelicArchGLInclAt F w r)) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F h]

theorem commute_of_archComponent_eq_one (w : InfinitePlace F) {k : AdelicGL2 (𝓞 F) F}
    (hk : archComponent F w (glArch (𝓞 F) F k) = 1) (r : GL (Fin 2) w.Completion) :
    k * adelicArchGLInclAt F w r = adelicArchGLInclAt F w r * k := by
  apply adelicGL2_ext'
  · rw [map_mul, map_mul]
    apply glInf_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw : w' = w
    · subst hw; rw [hk, archComponent_inclAt_self, one_mul, mul_one]
    · rw [archComponent_inclAt_of_ne hw, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_inclAt, one_mul, mul_one]

end KStabKit

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K)
      (_hdet : ∀ w : InfinitePlace K,
        ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1),
    (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (fun x => ψf s (x * k))) ∧
    (∀ s, IsArchKFinite K (fun x => ψf s (x * k))) ∧
    (∀ s, IsKfSmooth K (fun x => ψf s (x * k))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 (p.2 * k)) ∧
    (∀ g, Differentiable ℂ (fun s => ψf s (g * k))) ∧
    (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k' : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k' : AdelicGL2 (𝓞 K) K) * k)) ∈ W) ∧
    (∀ (s : ℂ) (k' : adelicMaximalCompact K),
      ψf s ((k' : AdelicGL2 (𝓞 K) K) * k) = ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u * k) = ψf s (g * k)) ∧
    (∀ s : ℂ, (fun x => ψf s (x * k)) ∈ archCutSubmodule K tysK) ∧
    (∫ k', ‖ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)‖ ^ 2 ∂(maximalCompactHaar K)
      = ∫ k', ‖ψf 0 (k' : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) := by
  intro αm
  intro hαm μ ν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty k hk hdet
  refine ⟨fun s => (hψf s).rightTranslate k, ?_, ?_, ?_, fun g => hψfhol (g * k), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s w
    obtain ⟨sset, hs⟩ := hψfK s w
    set r₀ : GL (Fin 2) w.Completion := archComponent K w (glArch (𝓞 K) K k) with hr₀
    have hr₀mem : r₀ ∈ rowIsometrySubgroup w.Completion := (AutomorphicForm.mem_adelicMaximalCompact_iff'.mp hk).2 w
    obtain ⟨k₁, hk₁w, hk₀eq⟩ : ∃ k₁ : AdelicGL2 (𝓞 K) K,
        archComponent K w (glArch (𝓞 K) K k₁) = 1 ∧ k = adelicArchGLInclAt K w r₀ * k₁ := by
      refine ⟨(adelicArchGLInclAt K w r₀)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
      rw [map_mul, map_inv, map_mul, map_inv, KStabKit.archComponent_inclAt_self, hr₀, inv_mul_cancel]
    let L : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      LinearMap.funLeft ℂ ℂ (fun x : AdelicGL2 (𝓞 K) K => x * k₁)
    refine ⟨sset.image L, fun u hu => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    have hmem : (fun x => ψf s (x * adelicArchGLInclAt K w (r * r₀))) ∈ Submodule.span ℂ (sset : Set _) :=
      hs _ (Subgroup.mem_map.mpr ⟨r * r₀, (rowIsometrySubgroup w.Completion).mul_mem hr hr₀mem, rfl⟩)
    have hfun : (fun x => ψf s (x * adelicArchGLInclAt K w r * k))
        = L (fun x => ψf s (x * adelicArchGLInclAt K w (r * r₀))) := by
      funext x
      simp only [L, LinearMap.funLeft_apply]
      rw [hk₀eq]
      congr 1
      calc x * adelicArchGLInclAt K w r * (adelicArchGLInclAt K w r₀ * k₁)
          = x * (adelicArchGLInclAt K w (r * r₀) * k₁) := by simp only [map_mul, mul_assoc]
        _ = x * (k₁ * adelicArchGLInclAt K w (r * r₀)) := by
            rw [KStabKit.commute_of_archComponent_eq_one w hk₁w (r * r₀)]
        _ = x * k₁ * adelicArchGLInclAt K w (r * r₀) := by rw [mul_assoc]
    rw [hfun, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  ·
    intro s
    have hv := hψff s
    rw [AutomorphicForm.isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
    have hnorm : (finiteAdelicGL2Subgroup K).Normal := by
      unfold finiteAdelicGL2Subgroup; infer_instance
    let c : finiteAdelicGL2Subgroup K → finiteAdelicGL2Subgroup K := fun h =>
      ⟨k⁻¹ * (h : AdelicGL2 (𝓞 K) K) * k, by
        have := hnorm.conj_mem (h : AdelicGL2 (𝓞 K) K) h.2 k⁻¹
        rwa [inv_inv] at this⟩
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
        (FLT.SmoothVectors.RightTranslationFn.mk fun h => ψf s (h * k)) : Subgroup (finiteAdelicGL2Subgroup K)) :
          Set (finiteAdelicGL2Subgroup K))
        = c ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup K) (FLT.SmoothVectors.RightTranslationFn.mk (ψf s)) :
            Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) := by
      ext h
      simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      constructor
      · intro hh
        apply FLT.SmoothVectors.RightTranslationFn.ext
        intro x
        have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * k⁻¹)) hh
        simp only [FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk] at this
        simp only [FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk, c]
        simpa [mul_assoc] using this
      · intro hh
        apply FLT.SmoothVectors.RightTranslationFn.ext
        intro x
        have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * k)) hh
        simp only [FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk, c] at this
        simp only [FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk]
        simpa [mul_assoc] using this
    rw [hset]
    exact hv.preimage hc
  ·
    exact hψfjc.comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))
  ·
    intro w
    obtain ⟨W, hWfd, hW⟩ := hψfKu w
    set r₀ : GL (Fin 2) w.Completion := archComponent K w (glArch (𝓞 K) K k) with hr₀
    have hr₀mem : r₀ ∈ rowIsometrySubgroup w.Completion := (AutomorphicForm.mem_adelicMaximalCompact_iff'.mp hk).2 w
    obtain ⟨k₁, hk₁w, hk₀eq⟩ : ∃ k₁ : AdelicGL2 (𝓞 K) K,
        archComponent K w (glArch (𝓞 K) K k₁) = 1 ∧ k = adelicArchGLInclAt K w r₀ * k₁ := by
      refine ⟨(adelicArchGLInclAt K w r₀)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
      rw [map_mul, map_inv, map_mul, map_inv, KStabKit.archComponent_inclAt_self, hr₀, inv_mul_cancel]
    have hι : adelicArchGLInclAt K w r₀ ∈ archRowIsometrySubgroup K w :=
      Subgroup.mem_map.mpr ⟨r₀, hr₀mem, rfl⟩
    let ρ : ↥(archRowIsometrySubgroup K w) → ↥(archRowIsometrySubgroup K w) :=
      fun k' => k' * ⟨adelicArchGLInclAt K w r₀, hι⟩
    let T : (↥(archRowIsometrySubgroup K w) → ℂ) →ₗ[ℂ] (↥(archRowIsometrySubgroup K w) → ℂ) :=
      LinearMap.funLeft ℂ ℂ ρ
    haveI := hWfd
    refine ⟨W.map T, inferInstance, fun s g => ?_⟩
    have hmem := hW s (g * k₁)
    have hfun : (fun k' : ↥(archRowIsometrySubgroup K w) => ψf s (g * (k' : AdelicGL2 (𝓞 K) K) * k))
        = T (fun k' : ↥(archRowIsometrySubgroup K w) => ψf s (g * k₁ * (k' : AdelicGL2 (𝓞 K) K))) := by
      funext k'
      simp only [T, LinearMap.funLeft_apply, ρ, Subgroup.coe_mul]
      congr 1
      rw [hk₀eq]
      obtain ⟨r, hr, hrk⟩ := Subgroup.mem_map.mp k'.2
      rw [← hrk]
      calc g * adelicArchGLInclAt K w r * (adelicArchGLInclAt K w r₀ * k₁)
          = g * (adelicArchGLInclAt K w (r * r₀) * k₁) := by simp only [map_mul, mul_assoc]
        _ = g * (k₁ * adelicArchGLInclAt K w (r * r₀)) := by
            rw [KStabKit.commute_of_archComponent_eq_one w hk₁w (r * r₀)]
        _ = g * k₁ * (adelicArchGLInclAt K w r * adelicArchGLInclAt K w r₀) := by rw [map_mul, mul_assoc]
    rw [hfun]
    exact Submodule.mem_map_of_mem hmem
  ·
    intro s k'
    have hmem : (k' : AdelicGL2 (𝓞 K) K) * k ∈ adelicMaximalCompact K := (adelicMaximalCompact K).mul_mem k'.2 hk
    exact hψfflat s ⟨_, hmem⟩
  ·
    intro s g u hu
    have hconj := NumberField.AdelicLevel.conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
      K N k⁻¹ ((adelicMaximalCompact K).inv_mem hk) u hu
    rw [inv_inv] at hconj
    have := hψflev s (g * k) (k⁻¹ * u * k) hconj
    rw [show g * k * (k⁻¹ * u * k) = g * u * k by group] at this
    exact this
  ·
    intro s
    exact AutomorphicForm.comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
      K tysK (ψf s) (hψfty s) k hk hdet
  ·
    haveI : (maximalCompactHaar K).IsMulRightInvariant := by
      refine ⟨fun g => ?_⟩
      have h := MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul (maximalCompactHaar K) g
      have hu : (MeasureTheory.Measure.map (· * g) (maximalCompactHaar K)) Set.univ = 1 := by
        rw [MeasureTheory.Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ, measure_univ]
      have hc : MeasureTheory.Measure.modularCharacterFun g = 1 := by
        have h2 := congrArg (fun ν : MeasureTheory.Measure (adelicMaximalCompact K) => ν Set.univ) h
        simp only [hu, MeasureTheory.Measure.coe_nnreal_smul_apply, measure_univ, mul_one] at h2
        exact_mod_cast h2.symm
      rw [h, hc, one_smul]
    have h := MeasureTheory.integral_mul_right_eq_self (μ := maximalCompactHaar K)
      (fun k' : adelicMaximalCompact K => ‖ψf 0 (k' : AdelicGL2 (𝓞 K) K)‖ ^ 2) (⟨k, hk⟩ : adelicMaximalCompact K)
    simpa only [Subgroup.coe_mul] using h

end S_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
end P2MW
export P2MW.S_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq (solution)
