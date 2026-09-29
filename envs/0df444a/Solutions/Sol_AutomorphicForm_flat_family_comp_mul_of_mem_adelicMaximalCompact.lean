-- Prove2me | solution 1 for AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/954beaaf-486a-556d-b8d5-b3abec491bdd

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

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

open KStabKit FLT.SmoothVectors

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (k₀ : AdelicGL2 (𝓞 F) F) (_hk₀ : k₀ ∈ adelicMaximalCompact F),
    (∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (fun h => φ s (h * k₀))) ∧
    (∀ s, IsArchKFinite F (fun h => φ s (h * k₀))) ∧
    (∀ s, IsKfSmooth F (fun h => φ s (h * k₀))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 (p.2 * k₀)) ∧
    (∀ g, Differentiable ℂ (fun s => φ s (g * k₀))) ∧
    (∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s (k * k₀) = φ s' (k * k₀)) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat k₀ hk₀
  refine ⟨fun s => (hφ s).rightTranslate k₀, ?_, ?_, ?_, fun g => hφhol (g * k₀), ?_⟩
  ·
    intro s w
    obtain ⟨sset, hs⟩ := hφK s w

    set r₀ : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F k₀) with hr₀
    have hr₀mem : r₀ ∈ rowIsometrySubgroup w.Completion := (mem_adelicMaximalCompact_iff'.mp hk₀).2 w
    obtain ⟨k₁, hk₁w, hk₀eq⟩ : ∃ k₁ : AdelicGL2 (𝓞 F) F,
        archComponent F w (glArch (𝓞 F) F k₁) = 1 ∧ k₀ = adelicArchGLInclAt F w r₀ * k₁ := by
      refine ⟨(adelicArchGLInclAt F w r₀)⁻¹ * k₀, ?_, by rw [mul_inv_cancel_left]⟩
      rw [map_mul, map_inv, map_mul, map_inv, archComponent_inclAt_self, hr₀, inv_mul_cancel]
    let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
      LinearMap.funLeft ℂ ℂ (fun x : AdelicGL2 (𝓞 F) F => x * k₁)
    classical
    refine ⟨sset.image L, fun u hu => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    have hmem : (fun x => φ s (x * adelicArchGLInclAt F w (r * r₀))) ∈ Submodule.span ℂ (sset : Set _) :=
      hs _ (Subgroup.mem_map.mpr ⟨r * r₀, (rowIsometrySubgroup w.Completion).mul_mem hr hr₀mem, rfl⟩)
    have hfun : (fun x => φ s (x * adelicArchGLInclAt F w r * k₀))
        = L (fun x => φ s (x * adelicArchGLInclAt F w (r * r₀))) := by
      funext x
      simp only [L, LinearMap.funLeft_apply]
      rw [hk₀eq]
      congr 1
      calc x * adelicArchGLInclAt F w r * (adelicArchGLInclAt F w r₀ * k₁)
          = x * (adelicArchGLInclAt F w (r * r₀) * k₁) := by simp only [map_mul, mul_assoc]
        _ = x * (k₁ * adelicArchGLInclAt F w (r * r₀)) := by
            rw [commute_of_archComponent_eq_one w hk₁w (r * r₀)]
        _ = x * k₁ * adelicArchGLInclAt F w (r * r₀) := by rw [mul_assoc]
    rw [hfun, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  ·
    intro s
    have hv := hφf s
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hv ⊢

    have hnorm : (finiteAdelicGL2Subgroup F).Normal := by
      unfold finiteAdelicGL2Subgroup; infer_instance
    let c : finiteAdelicGL2Subgroup F → finiteAdelicGL2Subgroup F := fun h =>
      ⟨k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀, by
        have := hnorm.conj_mem (h : AdelicGL2 (𝓞 F) F) h.2 k₀⁻¹
        rwa [inv_inv] at this⟩
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk fun h => φ s (h * k₀)) : Subgroup (finiteAdelicGL2Subgroup F)) :
          Set (finiteAdelicGL2Subgroup F))
        = c ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ s)) :
            Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
      ext h
      simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      constructor
      · intro hh
        apply RightTranslationFn.ext
        intro x
        have := congrArg (fun f => RightTranslationFn.toFun f (x * k₀⁻¹)) hh
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at this
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, c]
        simpa [mul_assoc] using this
      · intro hh
        apply RightTranslationFn.ext
        intro x
        have := congrArg (fun f => RightTranslationFn.toFun f (x * k₀)) hh
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, c] at this
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
        simpa [mul_assoc] using this
    rw [hset]
    exact hv.preimage hc
  ·
    exact hφjc.comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))
  ·
    intro s s' k hkf hka
    have hkK : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkf, hka⟩
    have hkk₀ := (adelicMaximalCompact F).mul_mem hkK hk₀
    exact hφflat s s' (k * k₀) hkk₀.1 hkk₀.2

end S_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact
end P2MW
export P2MW.S_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact (solution)
