-- Prove2me | solution 1 for AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a0eaaf81-da7b-50a0-9d47-69193d009bde

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply

set_option autoImplicit false

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ := by
  classical

  let ev : M → ((M →ₗ[A] N) →ₗ[A] N) := fun m =>
    { toFun := fun g => g m, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have ev_apply : ∀ (m : M) (g : M →ₗ[A] N), ev m g = g m := fun _ _ => rfl

  have hev : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (m : M),
      θ x m = AdicCompletion.map I (ev m) x := by
    intro x m
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [hθ x n g hg m, AdicCompletion.map_val_apply, ← hg, LinearMap.reduceModIdeal_apply, ev_apply]

  obtain ⟨s, f, hf⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let p : (Fin s → A) →ₗ[A] M := Fintype.linearCombination A f
  have p_apply : ∀ c : Fin s → A, p c = ∑ i, c i • f i := fun c => Fintype.linearCombination_apply A f c
  have hp : Function.Surjective p := by
    intro m
    have hm : m ∈ Submodule.span A (Set.range f) := by rw [hf]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hm
    exact ⟨c, by rw [p_apply, hc]⟩
  have p_single : ∀ i : Fin s, p (Pi.single i 1) = f i := fun i => by
    rw [show p (Pi.single i 1) = Fintype.linearCombination A f (Pi.single i 1) from rfl,
      Fintype.linearCombination_apply_single, one_smul]

  let j : (M →ₗ[A] N) →ₗ[A] (Fin s → N) := LinearMap.pi fun i => ev (f i)
  have j_apply : ∀ (g : M →ₗ[A] N) (i : Fin s), j g i = g (f i) := fun _ _ => rfl
  have proj_comp_j : ∀ i : Fin s, LinearMap.proj i ∘ₗ j = ev (f i) := fun i => rfl
  have hj : Function.Injective j := by
    intro g g' h
    refine LinearMap.ext_on_range hf fun i => ?_
    rw [← j_apply, ← j_apply, h]

  obtain ⟨r, k, hk⟩ := Module.Finite.exists_fin (R := A) (M := ↥(LinearMap.ker p))

  let dc : Fin r → ((Fin s → N) →ₗ[A] N) := fun t => ∑ i, (k t : Fin s → A) i • LinearMap.proj i
  have dc_apply : ∀ (t : Fin r) (y : Fin s → N), dc t y = ∑ i, (k t : Fin s → A) i • y i := by
    intro t y
    simp only [dc, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  let d : (Fin s → N) →ₗ[A] (Fin r → N) := LinearMap.pi dc
  have proj_comp_d : ∀ t : Fin r, LinearMap.proj t ∘ₗ d = dc t := fun t => rfl

  have hdj : ∀ g : M →ₗ[A] N, d (j g) = 0 := by
    intro g
    funext t
    show dc t (j g) = 0
    rw [dc_apply]
    simp only [j_apply]
    rw [← show g (p (k t : Fin s → A)) = ∑ i, (k t : Fin s → A) i • g (f i) by
      rw [p_apply, map_sum]; simp only [map_smul]]
    rw [LinearMap.mem_ker.mp (k t).2, map_zero]
  have hker_d : ∀ y : Fin s → N, d y = 0 → ∃ g : M →ₗ[A] N, j g = y := by
    intro y hy
    let yt : (Fin s → A) →ₗ[A] N := Fintype.linearCombination A y
    have yt_apply : ∀ c, yt c = ∑ i, c i • y i := fun c => Fintype.linearCombination_apply A y c
    have hK : LinearMap.ker p ≤ LinearMap.ker yt := by
      intro κ hκ
      have hκ' : (⟨κ, hκ⟩ : ↥(LinearMap.ker p)) ∈ Submodule.span A (Set.range k) := by
        rw [hk]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hκ'
      have hκc : κ = ∑ t, c t • (k t : Fin s → A) := by
        have := congrArg (fun z : ↥(LinearMap.ker p) => (z : Fin s → A)) hc
        simpa using this.symm
      rw [LinearMap.mem_ker, hκc, map_sum]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [map_smul, yt_apply, ← dc_apply]
      have : dc t y = d y t := rfl
      rw [this, hy, Pi.zero_apply, smul_zero]
    let g : M →ₗ[A] N :=
      (LinearMap.ker p).liftQ yt hK ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap
    have g_p : ∀ c, g (p c) = yt c := by
      intro c
      show (LinearMap.ker p).liftQ yt hK ((p.quotKerEquivOfSurjective hp).symm (p c)) = yt c
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    refine ⟨g, funext fun i => ?_⟩
    rw [j_apply, ← p_single, g_p, yt_apply]
    simp [Pi.single_apply]
  let dR : (Fin s → N) →ₗ[A] ↥(LinearMap.range d) := d.rangeRestrict
  have hdR : Function.Surjective dR := LinearMap.surjective_rangeRestrict d
  have sub_comp_dR : (LinearMap.range d).subtype ∘ₗ dR = d := LinearMap.ext fun _ => rfl
  have hexact : Function.Exact j dR := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨g, hg⟩ := hker_d y hy
      exact ⟨g, hg⟩
    · rintro _ ⟨g, rfl⟩
      exact hdj g

  have map_dc : ∀ (t : Fin r) (y : AdicCompletion I (Fin s → N)),
      AdicCompletion.map I (dc t) y = ∑ i, (k t : Fin s → A) i • AdicCompletion.map I (LinearMap.proj i) y := by
    intro t y
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    rw [AdicCompletion.map_val_apply, ← hw, LinearMap.reduceModIdeal_apply, dc_apply,
      AdicCompletion.val_sum_apply]
    simp only [AdicCompletion.val_smul_apply, AdicCompletion.map_val_apply, ← hw,
      LinearMap.reduceModIdeal_apply, LinearMap.proj_apply]
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply]

  have pi_inj : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (y y' : AdicCompletion I (ι → N)),
      (∀ i, AdicCompletion.map I (LinearMap.proj i) y = AdicCompletion.map I (LinearMap.proj i) y') →
      y = y' := by
    intro ι _ _ y y' h
    apply (AdicCompletion.piEquivOfFintype I (fun _ : ι => N)).injective
    rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.piEquivOfFintype_apply]
    funext i
    exact h i
  constructor
  ·
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply AdicCompletion.map_injective I hj
    rw [map_zero]
    refine pi_inj _ _ fun i => ?_
    rw [map_zero, AdicCompletion.map_comp_apply, proj_comp_j, ← hev, hx, LinearMap.zero_apply]
  ·
    intro F
    let z : Fin s → AdicCompletion I N := fun i => F (f i)
    let yh : AdicCompletion I (Fin s → N) := (AdicCompletion.piEquivOfFintype I (fun _ : Fin s => N)).symm z
    have hyh : ∀ i, AdicCompletion.map I (LinearMap.proj i) yh = F (f i) := by
      intro i
      have := (AdicCompletion.piEquivOfFintype I (fun _ : Fin s => N)).apply_symm_apply z
      rw [AdicCompletion.piEquivOfFintype_apply] at this
      exact congrFun this i
    have hd0 : AdicCompletion.map I d yh = 0 := by
      refine pi_inj _ _ fun t => ?_
      rw [map_zero, AdicCompletion.map_comp_apply, proj_comp_d, map_dc]
      simp only [hyh]
      rw [← show F (p (k t : Fin s → A)) = ∑ i, (k t : Fin s → A) i • F (f i) by
        rw [p_apply, map_sum]; simp only [map_smul]]
      rw [LinearMap.mem_ker.mp (k t).2, map_zero]
    have hdR0 : AdicCompletion.map I dR yh = 0 := by
      apply AdicCompletion.map_injective I (Submodule.injective_subtype (LinearMap.range d))
      rw [map_zero, AdicCompletion.map_comp_apply, sub_comp_dR, hd0]
    obtain ⟨x, hx⟩ := ((AdicCompletion.map_exact hj hexact hdR) yh).mp hdR0
    refine ⟨x, LinearMap.ext_on_range hf fun i => ?_⟩
    rw [hev, ← proj_comp_j, ← AdicCompletion.map_comp_apply, hx, hyh]

end S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply
end P2MW
export P2MW.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply (solution)
