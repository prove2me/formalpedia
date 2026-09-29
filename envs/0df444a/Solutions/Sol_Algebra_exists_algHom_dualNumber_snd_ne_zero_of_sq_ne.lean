-- Prove2me | solution 1 for Algebra.exists_algHom_dualNumber_snd_ne_zero_of_sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/03c89f5e-42aa-5933-b6c7-02845fe6b4b4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne

set_option autoImplicit false

theorem solution
    (Ω : Type*) [Field Ω] (S : Type*) [CommRing S] [Algebra Ω S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (hres : Function.Surjective (algebraMap Ω (S ⧸ 𝔪)))
    (hne : 𝔪 ^ 2 ≠ 𝔪) :
    ∃ (φ : S →ₐ[Ω] DualNumber Ω) (s : S), TrivSqZeroExt.snd (φ s) ≠ 0 := by
  classical

  haveI : Nontrivial (S ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top ‹_›)
  have hle : 𝔪 ^ 2 ≤ 𝔪 := Ideal.pow_le_self two_ne_zero
  set T := S ⧸ 𝔪 ^ 2
  let πT : S →ₐ[Ω] T := Ideal.Quotient.mkₐ Ω (𝔪 ^ 2)
  let ρ : T →ₐ[Ω] S ⧸ 𝔪 := Ideal.Quotient.factorₐ Ω hle
  have hρ : ∀ s : S, ρ (πT s) = Ideal.Quotient.mk 𝔪 s := fun s => rfl
  have hbij : Function.Bijective (Algebra.ofId Ω (S ⧸ 𝔪)) :=
    ⟨(algebraMap Ω (S ⧸ 𝔪)).injective, hres⟩
  let e : Ω ≃ₐ[Ω] S ⧸ 𝔪 := AlgEquiv.ofBijective (Algebra.ofId Ω (S ⧸ 𝔪)) hbij
  have he : ∀ c : Ω, e c = algebraMap Ω (S ⧸ 𝔪) c := fun c => rfl
  let p : T →ₐ[Ω] Ω := (e.symm : S ⧸ 𝔪 →ₐ[Ω] Ω).comp ρ
  have hp : ∀ t : T, e (p t) = ρ t := fun t => e.apply_symm_apply (ρ t)

  have hker : ∀ t : T, ρ t = 0 ↔ ∃ m ∈ 𝔪, πT m = t := by
    intro t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := 𝔪 ^ 2) t
    constructor
    · intro h0
      refine ⟨s, ?_, rfl⟩
      have : Ideal.Quotient.mk 𝔪 s = 0 := by rw [← hρ]; exact h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · rintro ⟨m, hm, hms⟩
      have : (πT m : T) = Ideal.Quotient.mk (𝔪 ^ 2) s := hms
      rw [← this, hρ]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hsq : ∀ u v : T, ρ u = 0 → ρ v = 0 → u * v = 0 := by
    intro u v hu hv
    obtain ⟨m, hm, rfl⟩ := (hker u).mp hu
    obtain ⟨m', hm', rfl⟩ := (hker v).mp hv
    rw [← map_mul]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (by rw [pow_two]; exact Ideal.mul_mem_mul hm hm')

  have hdec : ∀ t : T, ρ (t - algebraMap Ω T (p t)) = 0 := by
    intro t
    rw [map_sub, AlgHom.commutes, ← he, hp, sub_self]

  have hlt : 𝔪 ^ 2 < 𝔪 := lt_of_le_of_ne hle hne
  obtain ⟨m₀, hm₀, hm₀'⟩ := SetLike.exists_of_lt hlt
  set t₀ : T := πT m₀ with ht₀
  have ht₀ne : t₀ ≠ 0 := fun h0 => hm₀' ((Ideal.Quotient.eq_zero_iff_mem).mp h0)
  have hρt₀ : ρ t₀ = 0 := (hker t₀).mpr ⟨m₀, hm₀, rfl⟩
  have hpt₀ : p t₀ = 0 := by
    apply e.injective
    rw [hp, hρt₀, map_zero]

  let W : Submodule Ω T := Submodule.span Ω {(1 : T)}
  have ht₀W : Submodule.Quotient.mk (p := W) t₀ ≠ 0 := by
    intro h0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h0
    obtain ⟨c, hc⟩ := h0
    have : p t₀ = c := by
      rw [← hc, map_smul, map_one, smul_eq_mul, mul_one]
    rw [hpt₀] at this
    rw [← this, zero_smul] at hc
    exact ht₀ne hc.symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual Ω (T ⧸ W), ψ (Submodule.Quotient.mk t₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ht₀W ((Module.forall_dual_apply_eq_zero_iff Ω _).mp hall)
  let δ : T →ₗ[Ω] Ω := ψ.comp W.mkQ
  have hδ1 : δ 1 = 0 := by
    show ψ (W.mkQ 1) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_span_singleton_self _), map_zero]
  have hδalg : ∀ c : Ω, δ (algebraMap Ω T c) = 0 := by
    intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hδ1, smul_zero]
  have hδt₀ : δ t₀ ≠ 0 := hψ

  have hleib : ∀ x y : T, δ (x * y) = p x * δ y + p y * δ x := by
    intro x y
    set u := x - algebraMap Ω T (p x) with hu
    set v := y - algebraMap Ω T (p y) with hv
    have huv : u * v = 0 := hsq u v (hdec x) (hdec y)
    have hδu : δ u = δ x := by rw [hu, map_sub, hδalg, sub_zero]
    have hδv : δ v = δ y := by rw [hv, map_sub, hδalg, sub_zero]
    have : x * y = algebraMap Ω T (p x * p y) + ((p x) • v + (p y) • u) + u * v := by
      rw [hu, hv, map_mul, Algebra.smul_def, Algebra.smul_def]; ring
    rw [this, huv, add_zero, map_add, hδalg, zero_add, map_add, map_smul, map_smul, hδu, hδv,
      smul_eq_mul, smul_eq_mul]

  let f : T →ₗ[Ω] DualNumber Ω :=
    { toFun := fun t => TrivSqZeroExt.inl (p t) + TrivSqZeroExt.inr (δ t)
      map_add' := fun x y => by
        apply TrivSqZeroExt.ext <;> simp [map_add]
      map_smul' := fun c x => by
        apply TrivSqZeroExt.ext <;> simp [map_smul] }
  have hf : ∀ t, f t = TrivSqZeroExt.inl (p t) + TrivSqZeroExt.inr (δ t) := fun t => rfl
  have hf1 : f 1 = 1 := by
    rw [hf]; apply TrivSqZeroExt.ext <;> simp [hδ1]
  have hfmul : ∀ x y : T, f (x * y) = f x * f y := by
    intro x y
    rw [hf, hf, hf]
    apply TrivSqZeroExt.ext
    · simp [map_mul]
    · simp [hleib, TrivSqZeroExt.snd_mul, smul_eq_mul]
      ring
  let φT : T →ₐ[Ω] DualNumber Ω := AlgHom.ofLinearMap f hf1 hfmul
  refine ⟨φT.comp πT, m₀, ?_⟩
  show TrivSqZeroExt.snd (f t₀) ≠ 0
  rw [hf]
  simpa using hδt₀

end S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne
end P2MW
export P2MW.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne (solution)
