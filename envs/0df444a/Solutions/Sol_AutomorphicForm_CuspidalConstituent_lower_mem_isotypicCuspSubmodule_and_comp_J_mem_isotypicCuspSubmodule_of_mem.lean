-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d2c9b898-cc28-5f86-a4a2-1d8e4d5f6348

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "SmoothCusp.heckeCosetSum finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsSmoothCuspAutomorphicFnAt productionPinsOf AdelicGL2 centralScalar HeckeEigensystem archRealGLAt IsArchSmoothAt isArchSmoothAt_const ArchDir archFlowAt archDerivAt archDerivAt_add archDerivAt_smul archRealGLAt_mul_comm_of_glArch_eq_one archDerivAt_comp_mul_right ArchDir.H ArchDir.Fm ArchDir.E IsIsotypicCuspFormAt isotypicCuspSubmodule CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"
namespace RJClose
namespace K2b
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem glArch_heckeGen (v : HeightOneSpectrum (𝓞 F)) : glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact heckeGenAt_fst _ i j

theorem glArch_eq_one_of_mem_doubleCoset {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)) :
    glArch (𝓞 F) F x = 1 := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2, glArch_heckeGen,
    (mem_finiteAdelicGL2Subgroup_iff F u').mp hu'.2, one_mul, one_mul]

theorem archDerivAt_sum {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) {ι : Type*} (s : Finset ι)
    (f : ι → (AdelicGL2 (𝓞 F) F → ℂ)) (hf : ∀ i ∈ s, IsArchSmoothAt hw (f i)) :
    IsArchSmoothAt hw (∑ i ∈ s, f i) ∧ archDerivAt hw d (∑ i ∈ s, f i) = ∑ i ∈ s, archDerivAt hw d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by have h__af := isArchSmoothAt_const hw 0; simp at h__af ⊢; exact h__af, ?_⟩
    funext g
    simp only [Finset.sum_empty]
    show deriv (fun t : ℝ => (0 : AdelicGL2 (𝓞 F) F → ℂ) (g * archFlowAt hw d t)) 0 = (0 : AdelicGL2 (𝓞 F) F → ℂ) g
    simp
  | insert a s ha ih =>
    obtain ⟨hs, hD⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha' := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨ha'.add hs, by rw [archDerivAt_add ha' hs, hD]⟩

noncomputable def lower {w : InfinitePlace F} (hw : w.IsReal) (x : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)

theorem lower_comp_mul_right {w : InfinitePlace F} (hw : w.IsReal) (x : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : glArch (𝓞 F) F k = 1) (g : AdelicGL2 (𝓞 F) F) :
    lower hw x (g * k) = lower hw (fun g => x (g * k)) g := by
  simp only [lower, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, archDerivAt_comp_mul_right hw _ x hk]

theorem lower_comp_mul_left {w : InfinitePlace F} (hw : w.IsReal) (x : AdelicGL2 (𝓞 F) F → ℂ)
    (h g : AdelicGL2 (𝓞 F) F) :
    lower hw x (h * g) = lower hw (fun g => x (h * g)) g := by
  have hd : ∀ d : ArchDir, archDerivAt hw d x (h * g) = archDerivAt hw d (fun g => x (h * g)) g := fun d => by
    show deriv (fun t : ℝ => x (h * g * archFlowAt hw d t)) 0 = deriv (fun t : ℝ => x (h * (g * archFlowAt hw d t))) 0
    simp only [mul_assoc]
  simp only [lower, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hd]

theorem lower_smul {w : InfinitePlace F} (hw : w.IsReal) (a : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) :
    lower hw (a • x) = a • lower hw x := by
  simp only [lower, archDerivAt_smul]
  funext g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem lower_sum {w : InfinitePlace F} (hw : w.IsReal) {ι : Type*} (s : Finset ι)
    (f : ι → (AdelicGL2 (𝓞 F) F → ℂ)) (hf : ∀ i ∈ s, IsArchSmoothAt hw (f i)) :
    lower hw (∑ i ∈ s, f i) = ∑ i ∈ s, lower hw (f i) := by
  simp only [lower, (archDerivAt_sum hw _ s f hf).2]
  funext g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_add]

end AutomorphicForm.RJClose.K2b

open AutomorphicForm.RJClose.K2b in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hsm : ∀ x ∈ V, IsArchSmoothAt hw x)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxV : x ∈ V) (hne : x ≠ 0)
    (hxiso : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) :
    ((archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) ∈ V →
      (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x))
        ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) ∧
    ((fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V →
      (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ) := by

  have hxI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ x :=
    AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F _ _ _ ξ N S Ψ x hxiso hne

  have hVcusp : ∀ y ∈ V, Continuous y ∧ IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ y := fun y hy => by
    obtain ⟨hc', hs'⟩ :=
      AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
        F _ _ _ ξ y (hV.1.le hy)
    have h1 := hs' 1
    have hrt : rightTranslate F 1 y = y := funext fun g => by simp [rightTranslate]
    rw [hrt] at h1
    exact ⟨hc', h1⟩

  have hxk : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → IsArchSmoothAt hw (fun g => x (g * k)) := fun k hk =>
    hsm _ (hV.1.rightTranslate_fin_mem k ((mem_finiteAdelicGL2Subgroup_iff F k).mpr hk) x hxV)
  refine ⟨fun hLV => ?_, fun hJV => ?_⟩
  ·
    by_cases hL0 : lower hw x = 0
    · show lower hw x ∈ _
      rw [hL0]
      exact Submodule.zero_mem _
    have hI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ (lower hw x) :=
      { smoothCusp := (hVcusp _ hLV).2
        continuous := (hVcusp _ hLV).1
        level_invariant := fun g u hu => by
          have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2
          have hxu : (fun g => x (g * u)) = x := funext fun g => hxI.level_invariant g u hu
          rw [lower_comp_mul_right hw x hu1, hxu]
        hecke_eigen := fun v hv => by
          obtain ⟨reps, hreps, heq⟩ := hxI.hecke_eigen v hv
          refine ⟨reps, hreps, fun g => ?_⟩
          have hk : ∀ i, glArch (𝓞 F) F (reps i) = 1 := fun i =>
            glArch_eq_one_of_mem_doubleCoset (hreps.mem_doubleCoset i)
          have hsum : (fun g => ∑ i, x (g * reps i)) = (Ψ.a v) • x := by
            funext g; exact heq g
          calc SmoothCusp.heckeCosetSum F reps (lower hw x) g
              = ∑ i, lower hw (fun g => x (g * reps i)) g := by
                  simp only [SmoothCusp.heckeCosetSum, lower_comp_mul_right hw x (hk _)]
            _ = lower hw (∑ i, fun g => x (g * reps i)) g := by
                  rw [lower_sum hw Finset.univ _ (fun i _ => hxk _ (hk i)), Finset.sum_apply]
            _ = lower hw ((Ψ.a v) • x) g := by
                  congr 2
                  rw [← hsum]
                  funext g
                  simp only [Finset.sum_apply]
            _ = Ψ.a v * lower hw x g := by rw [lower_smul, Pi.smul_apply, smul_eq_mul]
        central_eigen := fun v hv g => by
          have hz : (fun g => x (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det
              (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))).gen v)) * g)) = (Ψ.toRawCentral.b v) • x := by
            funext g; exact hxI.central_eigen v hv g
          rw [lower_comp_mul_left hw x, hz, lower_smul, Pi.smul_apply, smul_eq_mul] }
    exact hI.mem_isotypicCuspSubmodule
  ·
    set z : AdelicGL2 (𝓞 F) F → ℂ := fun g => x (g * archRealGLAt hw UpperHalfPlane.J) with hz_def
    by_cases hz0 : z = 0
    · rw [hz0]; exact Submodule.zero_mem _
    have hcomm : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 →
        archRealGLAt hw UpperHalfPlane.J * k = k * archRealGLAt hw UpperHalfPlane.J := fun k hk =>
      archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk
    have hI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ z :=
      { smoothCusp := (hVcusp _ hJV).2
        continuous := (hVcusp _ hJV).1
        level_invariant := fun g u hu => by
          have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2
          show x (g * u * _) = x (g * _)
          rw [mul_assoc, ← hcomm u hu1, ← mul_assoc, hxI.level_invariant _ u hu]
        hecke_eigen := fun v hv => by
          obtain ⟨reps, hreps, heq⟩ := hxI.hecke_eigen v hv
          refine ⟨reps, hreps, fun g => ?_⟩
          have hk : ∀ i, glArch (𝓞 F) F (reps i) = 1 := fun i =>
            glArch_eq_one_of_mem_doubleCoset (hreps.mem_doubleCoset i)
          show (∑ i, x (g * reps i * _)) = _ * x (g * _)
          have := heq (g * archRealGLAt hw UpperHalfPlane.J)
          simp only [SmoothCusp.heckeCosetSum, mul_assoc] at this ⊢
          simpa only [hcomm _ (hk _)] using this
        central_eigen := fun v hv g => by
          show x (_ * g * _) = _ * x (g * _)
          rw [mul_assoc]
          exact hxI.central_eigen v hv _ }
    exact hI.mem_isotypicCuspSubmodule

end S_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem (solution)
