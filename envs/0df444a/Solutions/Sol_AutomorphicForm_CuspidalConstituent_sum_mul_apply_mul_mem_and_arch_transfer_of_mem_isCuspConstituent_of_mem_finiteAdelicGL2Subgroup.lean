-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/02471b53-d813-54cd-9e03-fdc55f664c41

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

namespace Ws47
namespace C5

theorem adelicArchGLInclAt_mul_comm_of_glArch_eq_one (w : InfinitePlace ℚ) (a : GL (Fin 2) w.Completion)
    {k : AdelicGL2 (𝓞 ℚ) ℚ} (hk : glArch (𝓞 ℚ) ℚ k = 1) :
    adelicArchGLInclAt ℚ w a * k = k * adelicArchGLInclAt ℚ w a := by
  have hfin : glFin (𝓞 ℚ) ℚ (adelicArchGLInclAt ℚ w a) = 1 := glFin_adelicArchGLIncl ℚ _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem rightTranslate_mem_archCutSubmodule_of_glArch_eq_one (tys : ArchTypeFamily ℚ)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ archCutSubmodule ℚ tys) {k : AdelicGL2 (𝓞 ℚ) ℚ}
    (hk : glArch (𝓞 ℚ) ℚ k = 1) :
    CuspidalConstituent.rightTranslate ℚ k φ ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt ℚ w (tys.rep w i)).map (CuspidalConstituent.rightRegular ℚ k)
        ≤ archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    refine comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k' => ?_
    rw [rowIsometryInclAt₀_apply]
    exact (adelicArchGLInclAt_mul_comm_of_glArch_eq_one w _ hk).symm
  have hmap : (⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i)).map (CuspidalConstituent.rightRegular ℚ k)
      ≤ ⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))

end Ws47.C5

open Ws47.C5 in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (hsmV : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∀ x ∈ V, IsArchSmoothAt hw x)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ) (hg : ∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) :
    let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun x => ∑ i, c i * φ (x * g i)
    φ' ∈ V ∧
    (Continuous φ → Continuous φ') ∧
    (∀ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys → φ' ∈ archCutSubmodule ℚ tys) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
      (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
        (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = e * φ x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = e * φ' x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cJ : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) = 0 → (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) = 0) := by
  intro φ'
  classical
  have hgA : ∀ i, glArch (𝓞 ℚ) ℚ (g i) = 1 := fun i => (mem_finiteAdelicGL2Subgroup_iff ℚ (g i)).mp (hg i)

  have hcomb : ∀ s : Finset (Fin m), (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i))
      = ∑ i ∈ s, c i • CuspidalConstituent.rightTranslate ℚ (g i) φ := by
    intro s; funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CuspidalConstituent.rightTranslate_apply]
  have hφ'eq : φ' = ∑ i, c i • CuspidalConstituent.rightTranslate ℚ (g i) φ := hcomb Finset.univ
  have hRV : ∀ i, CuspidalConstituent.rightTranslate ℚ (g i) φ ∈ V := fun i => hV.1.rightTranslate_fin_mem (g i) (hg i) φ hφV
  have hsV : ∀ s : Finset (Fin m), (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i)) ∈ V := by
    intro s; rw [hcomb s]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hRV i)
  have hφ'V : φ' ∈ V := hsV Finset.univ

  have hD : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (d : ArchDir) (s : Finset (Fin m)),
      archDerivAt hw d (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i))
        = fun x => ∑ i ∈ s, c i * archDerivAt hw d φ (x * g i) := by
    intro w hw d s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact archDerivAt_const hw d 0
    | insert a s ha ih =>
      have h1 : (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ insert a s, c i * φ (x * g i))
          = (c a • fun x => φ (x * g a)) + (fun x => ∑ i ∈ s, c i * φ (x * g i)) := by
        funext x; simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hsm1 : IsArchSmoothAt hw (c a • fun x => φ (x * g a)) := ((hsmV w hw φ hφV).comp_mul_right (hgA a)).smul _
      have hsm2 : IsArchSmoothAt hw (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i)) := hsmV w hw _ (hsV s)
      rw [h1, archDerivAt_add hsm1 hsm2, archDerivAt_smul, ih, archDerivAt_comp_mul_right hw d φ (hgA a)]
      funext x
      simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hC : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (s : Finset (Fin m)),
      archCasimirAt hw (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i))
        = fun x => ∑ i ∈ s, c i * archCasimirAt hw φ (x * g i) := by
    intro w hw s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact archCasimirAt_const hw 0
    | insert a s ha ih =>
      have h1 : (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ insert a s, c i * φ (x * g i))
          = (c a • fun x => φ (x * g a)) + (fun x => ∑ i ∈ s, c i * φ (x * g i)) := by
        funext x; simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hsm1 : IsArchSmoothAt hw (c a • fun x => φ (x * g a)) := ((hsmV w hw φ hφV).comp_mul_right (hgA a)).smul _
      have hsm2 : IsArchSmoothAt hw (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ s, c i * φ (x * g i)) := hsmV w hw _ (hsV s)
      rw [h1, archCasimirAt_add hsm1 hsm2, archCasimirAt_smul, ih, archCasimirAt_comp_mul_right hw φ (hgA a)]
      funext x
      simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

  have hL : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) x
        = ∑ i, c i * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) (x * g i) := by
    intro w hw x
    show (archDerivAt hw ArchDir.H (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ Finset.univ, c i * φ (x * g i)) -
        Complex.I • (archDerivAt hw ArchDir.E (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ Finset.univ, c i * φ (x * g i)) +
          archDerivAt hw ArchDir.Fm (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ Finset.univ, c i * φ (x * g i)))) x = _
    rw [hD w hw ArchDir.H, hD w hw ArchDir.E, hD w hw ArchDir.Fm]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨hφ'V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hc
    show Continuous fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φ (x * g i)
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hc.comp (continuous_id.mul continuous_const))
  ·
    intro tys hφ
    rw [hφ'eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (rightTranslate_mem_archCutSubmodule_of_glArch_eq_one tys hφ (hgA i))
  ·
    intro w hw n h k x
    show (∑ i, c i * φ (x * adelicArchGLInclAt ℚ w (k : GL (Fin 2) w.Completion) * g i)) =
      (archWeightCharAt hw n k : ℂ) * ∑ i, c i * φ (x * g i)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, adelicArchGLInclAt_mul_comm_of_glArch_eq_one w _ (hgA i), ← mul_assoc, h k (x * g i)]
    ring
  ·
    intro w hw lam h
    refine ⟨hsmV w hw φ' hφ'V, ?_⟩
    show archCasimirAt hw (fun x : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i ∈ Finset.univ, c i * φ (x * g i)) = _
    rw [hC w hw Finset.univ]
    funext x
    show (∑ i ∈ Finset.univ, c i * archCasimirAt hw φ (x * g i)) = lam * ∑ i ∈ Finset.univ, c i * φ (x * g i)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun h.2 (x * g i)
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [this]; ring
  ·
    intro w hw e h x
    show (∑ i, c i * φ (x * archRealGLAt hw UpperHalfPlane.J * g i)) = e * ∑ i, c i * φ (x * g i)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hw _ (hgA i), ← mul_assoc, h (x * g i)]
    ring
  ·
    intro w hw cJ h x
    rw [hL w hw x]
    show (∑ i, c i * φ (x * archRealGLAt hw UpperHalfPlane.J * g i)) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hw _ (hgA i), ← mul_assoc, h (x * g i)]
    ring
  ·
    intro w hw h
    funext x
    rw [hL w hw x]
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h (x * g i)
    rw [Pi.zero_apply] at this
    rw [this, mul_zero]

end S_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup (solution)
