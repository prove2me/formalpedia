-- Prove2me | solution 1 for AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/307c5b84-e3f2-5e7a-981a-4e4519e6aa52

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α) (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  obtain ⟨hαc, hαsupp⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F α hα

  set αv : AdelicGL2 (𝓞 F) F → ℂ := fun x => α x⁻¹ with hαv
  have hαvc : Continuous αv := hαc.comp continuous_inv
  have hαvsupp : HasCompactSupport αv := hαsupp.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))

  set Λ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun h x => ∫ y, g (x * y) * h y⁻¹ ∂μ with hΛ
  have hΛα : rightConv F g α = Λ αv := by
    funext x; simp only [hΛ, hαv, rightConv_apply, inv_inv, hμ]
  have hint : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, Continuous h → HasCompactSupport h →
      ∀ x, Integrable (fun y => g (x * y) * h y⁻¹) μ := fun h hh hhs x =>
    ((hg.comp (continuous_const.mul continuous_id)).mul (hh.comp continuous_inv)).integrable_of_hasCompactSupport
      (hhs.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))).mul_left
  have hΛadd : ∀ h₁ h₂ : AdelicGL2 (𝓞 F) F → ℂ, Continuous h₁ → HasCompactSupport h₁ → Continuous h₂ → HasCompactSupport h₂ →
      Λ (h₁ + h₂) = Λ h₁ + Λ h₂ := by
    intro h₁ h₂ c₁ s₁ c₂ s₂
    funext x
    simp only [hΛ, Pi.add_apply]
    rw [← integral_add (hint h₁ c₁ s₁ x) (hint h₂ c₂ s₂ x)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛsmul : ∀ (c : ℂ) (h : AdelicGL2 (𝓞 F) F → ℂ), Λ (c • h) = c • Λ h := by
    intro c h
    funext x
    simp only [hΛ, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛeq : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ) (k x : AdelicGL2 (𝓞 F) F), Λ (fun y => h (y * k)) x = Λ h (x * k) := by
    intro h k x
    simp only [hΛ]
    have h1 := integral_mul_left_eq_self (μ := μ) (fun y => g (x * k * y) * h y⁻¹) k⁻¹
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show g (x * y) * h (y⁻¹ * k) = g (x * k * (k⁻¹ * y)) * h (k⁻¹ * y)⁻¹
    rw [mul_inv_rev, inv_inv, mul_assoc x k, mul_inv_cancel_left]

  rw [mem_archCutSubmodule_iff]
  intro w
  set ι : ↥(rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w with hιdef
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    have h1 := congrArg (fun x => archComponent F w (glArch (𝓞 F) F x)) h
    simpa only [hιdef, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
      archComponent_archGLIncl_self] using h1
  have hcut := (mem_archCutSubmodule_iff F tys αv).mp hαt.1 w

  have hcut' : αv ∈ Submodule.span ℂ (⋃ i : Fin (tys.card w),
      {φ : AdelicGL2 (𝓞 F) F → ℂ | ∃ T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
        IsRightEquivariant ι (tys.rep w i).ρ T ∧ φ ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hcut
  obtain ⟨n, c, gen, hsum⟩ := Submodule.mem_span_set'.mp hcut'
  have hgen : ∀ j : Fin n, ∃ (i : Fin (tys.card w)) (T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
      (v : Fin (tys.rep w i).n → ℂ), IsRightEquivariant ι (tys.rep w i).ρ T ∧ T v = (gen j : AdelicGL2 (𝓞 F) F → ℂ) := by
    intro j
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (gen j).2
    obtain ⟨T, hT, v, hv⟩ := hi
    exact ⟨i, T, v, hT, hv⟩
  choose idx Tj vj hTj hTv using hgen

  let W : Type := (j : Fin n) → (Fin (tys.rep w (idx j)).n → ℂ)
  let ρW : Representation ℂ ↥(rowIsometrySubgroup₀ w.Completion) W :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w (idx j)).ρ k).comp (LinearMap.proj j)
      map_one' := by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ 1 (a j) = a j
        rw [map_one]; rfl
      map_mul' := fun k k' => by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ (k * k') (a j) = (tys.rep w (idx j)).ρ k ((tys.rep w (idx j)).ρ k' (a j))
        rw [map_mul]; rfl }
  have ρW_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W) (j : Fin n), ρW k a j = (tys.rep w (idx j)).ρ k (a j) := fun _ _ _ => rfl
  let TW : W →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := ∑ j, (Tj j).comp (LinearMap.proj j)
  have TW_apply : ∀ a : W, TW a = ∑ j, Tj j (a j) := fun a => by
    simp only [TW, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rfl
  have hTW : IsRightEquivariant ι ρW TW := by
    intro k a x
    rw [TW_apply, TW_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ρW_apply]
    exact hTj j k (a j) x

  let Rk : ↥(rowIsometrySubgroup₀ w.Completion) → (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := fun k => LinearMap.funLeft ℂ ℂ fun y : AdelicGL2 (𝓞 F) F => y * ι k
  have Rk_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (h : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F), Rk k h y = h (y * ι k) := fun _ _ _ => rfl
  let V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun k : ↥(rowIsometrySubgroup₀ w.Completion) => Rk k αv)
  have h0supp : HasCompactSupport (0 : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [HasCompactSupport, tsupport, Function.support_zero, closure_empty]; exact isCompact_empty
  have hVcc : ∀ h ∈ V, Continuous h ∧ HasCompactSupport h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨k, rfl⟩ := hh
      exact ⟨hαvc.comp (continuous_id.mul continuous_const), hαvsupp.comp_homeomorph (Homeomorph.mulRight (ι k))⟩
    | zero => exact ⟨continuous_const, h0supp⟩
    | add h₁ h₂ _ _ ih₁ ih₂ => exact ⟨ih₁.1.add ih₂.1, ih₁.2.add ih₂.2⟩
    | smul a h _ ih => exact ⟨ih.1.const_smul a, ih.2.smul_left (f := fun _ => a)⟩
  have hVstab : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)), ∀ h ∈ V, Rk k h ∈ V := by
    intro k h hh
    have hle : V.map (Rk k) ≤ V := by
      refine (Submodule.map_span_le _ _ _).mpr ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext y
      show αv (y * ι (k * k')) = αv (y * ι k * ι k')
      rw [map_mul, mul_assoc]
    exact hle ⟨h, hh, rfl⟩

  let A : Submodule ℂ W := V.comap TW
  have hTWρ : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), TW (ρW k a) = Rk k (TW a) := fun k a => funext fun x => hTW k a x
  have hA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), a ∈ A → ρW k a ∈ A := fun k a ha => by
    show TW (ρW k a) ∈ V
    rw [hTWρ]
    exact hVstab k _ ha
  let TA : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun a => Λ (TW a)
      map_add' := fun a b => by
        rw [Submodule.coe_add, map_add]
        exact hΛadd _ _ (hVcc _ a.2).1 (hVcc _ a.2).2 (hVcc _ b.2).1 (hVcc _ b.2).2
      map_smul' := fun a x => by
        rw [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact hΛsmul a _ }
  have hTA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : ↥A) (x : AdelicGL2 (𝓞 F) F), TA ⟨ρW k a, hA k a a.2⟩ x = TA a (x * ι k) := by
    intro k a x
    show Λ (TW (ρW k a)) x = Λ (TW a) (x * ι k)
    rw [hTWρ]
    exact hΛeq (TW a) (ι k) x
  obtain ⟨Text, hText, hTextA⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι hι ρW A hA TA hTA

  let a₀ : W := fun j => c j • vj j
  have hTWa₀ : TW a₀ = αv := by
    rw [TW_apply, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Tj j (c j • vj j) = c j • (gen j : AdelicGL2 (𝓞 F) F → ℂ)
    rw [map_smul, hTv]
  have ha₀ : a₀ ∈ A := by
    show TW a₀ ∈ V
    rw [hTWa₀]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    show αv (y * ι 1) = αv y
    rw [map_one, mul_one]
  have hgoal : rightConv F g α = Text a₀ := by
    rw [hΛα, ← hTWa₀]
    have h := congrArg (fun f : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) => f ⟨a₀, ha₀⟩) hTextA
    exact h.symm
  rw [hgoal, show a₀ = ∑ j, Pi.single j (a₀ j) from (Finset.univ_sum_single a₀).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_

  have hTj' : IsRightEquivariant ι (tys.rep w (idx j)).ρ
      (Text.comp (LinearMap.single ℂ (fun j => Fin (tys.rep w (idx j)).n → ℂ) j)) := by
    intro k u x
    show Text (Pi.single j ((tys.rep w (idx j)).ρ k u)) x = Text (Pi.single j u) (x * ι k)
    rw [← hText k (Pi.single j u) x]
    have hsingle : ρW k (Pi.single j u) = Pi.single j ((tys.rep w (idx j)).ρ k u) := by
      funext j'
      rw [ρW_apply]
      by_cases hj : j' = j
      · subst hj; simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne hj, map_zero]
    rw [hsingle]
  exact Submodule.mem_iSup_of_mem (idx j) (mem_typeSubmodule_of_isRightEquivariant hTj' (a₀ j))

end S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
end P2MW
export P2MW.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite (solution)
