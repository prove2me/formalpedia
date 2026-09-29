-- Prove2me | solution 1 for AutomorphicForm.exists_units_mul_sigmaTensor_eq_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/73e3bbfd-42c2-5a70-a4de-30d9b402ea23

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
import Theorems.Thm_AutomorphicForm_sigmaTensor_apply_eq_self_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace Ws35H
namespace H90

section Sigma
variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A τ (l ⊗ₜ[K] a) = τ l ⊗ₜ[K] a := by
  show (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A)) (l ⊗ₜ[K] a) = τ l ⊗ₜ[K] a
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem sigmaTensor_mul (τ τ' : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A (τ * τ') x =
      AutomorphicForm.sigmaTensor K L A τ (AutomorphicForm.sigmaTensor K L A τ' x) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul]; rfl

theorem sigmaTensor_one (x : L ⊗[K] A) : AutomorphicForm.sigmaTensor K L A 1 x = x := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul l a => rw [sigmaTensor_tmul]; rfl

theorem sigmaTensor_pow (τ : L ≃ₐ[K] L) (i : ℕ) (x : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A (τ ^ i) x = (⇑(AutomorphicForm.sigmaTensor K L A τ))^[i] x := by
  induction i generalizing x with
  | zero => rw [pow_zero, sigmaTensor_one, Function.iterate_zero, id]
  | succ i ih => rw [pow_succ, sigmaTensor_mul, ih, ← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem congr_apply_eq_sigmaTensor (τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[K] A) x = AutomorphicForm.sigmaTensor K L A τ x := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul l a => rw [sigmaTensor_tmul, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]; rfl

theorem sigmaTensor_includeRight (τ : L ≃ₐ[K] L) (a : A) :
    AutomorphicForm.sigmaTensor K L A τ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  rw [sigmaTensor_tmul, map_one]

end Sigma

section Galois
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include hgen in
theorem orderOf_eq_finrank : orderOf σ = Module.finrank K L :=
  (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)

include hgen in
theorem pow_finrank_eq_one : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank K L σ hgen]; exact pow_orderOf_eq_one σ

include hgen in
theorem prod_range_pow_eq_prod_univ {M : Type*} [CommMonoid M] (f : (L ≃ₐ[K] L) → M) :
    ∏ i ∈ Finset.range (Module.finrank K L), f (σ ^ i) = ∏ τ : L ≃ₐ[K] L, f τ := by
  classical
  have hord := orderOf_eq_finrank K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) ↑(Finset.range (Module.finrank K L)) := by
    rw [Finset.coe_range, ← hord]; exact pow_injOn_Iio_orderOf
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hord, orderOf_eq_card_of_forall_mem_zpowers hgen,
      Nat.card_eq_fintype_card]
  rw [← himg, Finset.prod_image hinj]

include hgen in

theorem mem_range_of_fixed (x : L) (hx : σ x = x) : x ∈ (algebraMap K L).range := by
  have hfix : ∀ τ : L ≃ₐ[K] L, τ x = x := by
    intro τ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hx]; exact ih
    | pred n ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, AlgEquiv.mul_apply]
      have : σ⁻¹ x = x := by
        conv_lhs => rw [← hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
      rw [this]; exact ih
  have := (IsGalois.mem_bot_iff_fixed x).mpr hfix
  rw [IntermediateField.mem_bot] at this
  obtain ⟨k, hk⟩ := this
  exact ⟨k, hk⟩

include hgen in
theorem pow_injective_fin {i j : ℕ} (hi : i < Module.finrank K L) (hj : j < Module.finrank K L)
    (h : σ ^ i = σ ^ j) : i = j := by
  have hord := orderOf_eq_finrank K L σ hgen
  exact pow_injOn_Iio_orderOf (by rw [hord]; exact hi) (by rw [hord]; exact hj) h

end Galois

end Ws35H.H90

namespace Ws35H
namespace H90

section Main
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "σE" => AutomorphicForm.sigmaTensor K L (HeightOneSpectrum.adicCompletion K v) σ

include hgen in

theorem prod_iterate_eq_one_of_norm_eq_one (x : L ⊗[K] Kv) (hx : Algebra.norm Kv x = 1) :
    ∏ i ∈ Finset.range (Module.finrank K L), (⇑σE)^[i] x = 1 := by
  have h := Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois K L Kv x
  rw [hx, map_one] at h
  rw [h, ← prod_range_pow_eq_prod_univ K L σ hgen]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← sigmaTensor_pow, congr_apply_eq_sigmaTensor]

def d (x : L ⊗[K] Kv) (i : ℕ) : L ⊗[K] Kv := ∏ j ∈ Finset.range i, (⇑σE)^[j] x

theorem d_zero (x : L ⊗[K] Kv) : d K L σ v x 0 = 1 := by simp [d]

theorem d_succ (x : L ⊗[K] Kv) (i : ℕ) : d K L σ v x (i + 1) = x * σE (d K L σ v x i) := by
  simp only [d]
  rw [Finset.prod_range_succ', map_prod, Function.iterate_zero, id, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _

def S (x θ : L ⊗[K] Kv) : L ⊗[K] Kv :=
  ∑ i ∈ Finset.range (Module.finrank K L), d K L σ v x i * (⇑σE)^[i] θ

include hgen in

theorem mul_sigma_S (x θ : L ⊗[K] Kv) (hx : ∏ i ∈ Finset.range (Module.finrank K L), (⇑σE)^[i] x = 1) :
    x * σE (S K L σ v x θ) = S K L σ v x θ := by
  simp only [S, map_sum, map_mul, Finset.mul_sum]
  have hterm : ∀ i, x * (σE (d K L σ v x i) * σE ((⇑σE)^[i] θ)) = d K L σ v x (i + 1) * (⇑σE)^[i + 1] θ := by
    intro i; rw [d_succ, Function.iterate_succ_apply']; ring
  simp only [hterm]

  set n := Module.finrank K L with hndef
  have hn : d K L σ v x n * (⇑σE)^[n] θ = d K L σ v x 0 * (⇑σE)^[0] θ := by
    rw [d_zero, Function.iterate_zero, id]
    have h1 : d K L σ v x n = 1 := hx
    have h2 : (⇑σE)^[n] θ = θ := by rw [← sigmaTensor_pow, hndef, pow_finrank_eq_one K L σ hgen, sigmaTensor_one]
    rw [h1, h2, one_mul]
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (hndef ▸ Module.finrank_pos)).symm⟩
  rw [hm] at hn ⊢
  rw [Finset.sum_range_succ, hn, Finset.sum_range_succ' (fun i => d K L σ v x i * (⇑σE)^[i] θ)]

include hgen in
theorem isUnit_of_prod_eq_one (x : L ⊗[K] Kv) (hx : ∏ i ∈ Finset.range (Module.finrank K L), (⇑σE)^[i] x = 1) :
    IsUnit x := by
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K L = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hn, Finset.prod_range_succ', Function.iterate_zero, id] at hx
  exact IsUnit.of_mul_eq_one_right _ hx

end Main

end Ws35H.H90

namespace Ws35H
namespace H90

section Main2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "σE" => AutomorphicForm.sigmaTensor K L (HeightOneSpectrum.adicCompletion K v) σ

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsub : Subsingleton (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := inferInstance
  have : Subsingleton (L ⊗[K] Kv) :=
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toEquiv.subsingleton
  exact not_subsingleton (L ⊗[K] Kv) this

theorem iterate_sigmaTensor_tmul_one (i : ℕ) (ℓ : L) :
    (⇑σE)^[i] (ℓ ⊗ₜ[K] (1 : Kv)) = ((σ ^ i) ℓ) ⊗ₜ[K] (1 : Kv) := by
  rw [← sigmaTensor_pow, sigmaTensor_tmul]

include hgen in

theorem exists_S_tmul_ne_zero (x : L ⊗[K] Kv) : ∃ ℓ : L, S K L σ v x (ℓ ⊗ₜ[K] 1) ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨w₀⟩ := nonempty_extension K L v
  set φ := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with hφ
  set ψ : L ⊗[K] Kv →+* w₀.1.adicCompletion L :=
    (Pi.evalRingHom (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) w₀).comp φ.toRingEquiv.toRingHom with hψ
  have hψ_tmul : ∀ ℓ : L, ψ (ℓ ⊗ₜ[K] (1 : Kv)) = algebraMap L (w₀.1.adicCompletion L) ℓ := by
    intro ℓ
    show φ (ℓ ⊗ₜ[K] (1 : Kv)) w₀ = _
    show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v (ℓ ⊗ₜ[K] (1 : Kv)) w₀ = _
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, mul_one]
  set n := Module.finrank K L with hn

  set F : Fin n → (L →* w₀.1.adicCompletion L) := fun i =>
    (algebraMap L (w₀.1.adicCompletion L)).toMonoidHom.comp ((σ ^ (i : ℕ)).toAlgHom.toRingHom.toMonoidHom) with hF
  have hFapply : ∀ (i : Fin n) (ℓ : L), F i ℓ = algebraMap L (w₀.1.adicCompletion L) ((σ ^ (i : ℕ)) ℓ) :=
    fun i ℓ => rfl
  have hFinj : Function.Injective F := by
    intro i j hij
    apply Fin.ext
    apply pow_injective_fin K L σ hgen i.2 j.2
    ext ℓ
    have := congrArg (fun f : L →* w₀.1.adicCompletion L => f ℓ) hij
    simp only [hFapply] at this
    exact (algebraMap L (w₀.1.adicCompletion L)).injective this
  have hli : LinearIndependent (w₀.1.adicCompletion L) (fun i => (⇑(F i) : L → w₀.1.adicCompletion L)) :=
    (linearIndependent_monoidHom L (w₀.1.adicCompletion L)).comp F hFinj
  have hdep : ∑ i ∈ (Finset.univ : Finset (Fin n)), ψ (d K L σ v x i) • (⇑(F i) : L → w₀.1.adicCompletion L) = 0 := by
    funext ℓ
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, hFapply, smul_eq_mul]
    have := congrArg ψ (hall ℓ)
    rw [map_zero, S, map_sum] at this
    rw [← this, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, iterate_sigmaTensor_tmul_one, hψ_tmul]
  have hpos : 0 < n := hn ▸ Module.finrank_pos
  have h0 := linearIndependent_iff'.mp hli Finset.univ (fun i => ψ (d K L σ v x i)) hdep ⟨0, hpos⟩ (Finset.mem_univ _)
  simp only [d_zero, map_one] at h0
  exact one_ne_zero h0

omit [IsGalois K L] in
theorem sigmaTensor_inv_apply (y : L ⊗[K] Kv) :
    AutomorphicForm.sigmaTensor K L Kv σ⁻¹ (σE y) = y := by
  rw [← sigmaTensor_mul, inv_mul_cancel, sigmaTensor_one]

omit [IsGalois K L] in
theorem sigmaTensor_apply_inv (y : L ⊗[K] Kv) :
    σE (AutomorphicForm.sigmaTensor K L Kv σ⁻¹ y) = y := by
  rw [← sigmaTensor_mul, mul_inv_cancel, sigmaTensor_one]

include hgen in

theorem isUnit_of_mul_sigma_eq (x y : L ⊗[K] Kv) (hxu : IsUnit x) (hy : x * σE y = y) (hy0 : y ≠ 0) :
    IsUnit y := by
  classical
  set φ := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with hφ
  set p := φ y with hp
  set q : Π w : v.Extension (𝓞 L), w.1.adicCompletion L := fun w => if p w = 0 then 0 else (p w)⁻¹ with hq
  set a : L ⊗[K] Kv := φ.symm q with ha
  set e : L ⊗[K] Kv := a * y with he

  have hey : e * y = y := by
    apply φ.injective
    rw [map_mul, map_mul, ha, AlgEquiv.apply_symm_apply]
    funext w
    simp only [Pi.mul_apply, hq]
    split_ifs with h
    · rw [← hp, h, mul_zero]
    · rw [← hp]; field_simp

  obtain ⟨xu, rfl⟩ := hxu
  have hσy : σE y = (↑xu⁻¹ : L ⊗[K] Kv) * y := by
    rw [← hy, ← mul_assoc, Units.inv_mul, one_mul, hy]
  have hσ'y : AutomorphicForm.sigmaTensor K L Kv σ⁻¹ y = AutomorphicForm.sigmaTensor K L Kv σ⁻¹ (↑xu : L ⊗[K] Kv) * y := by
    conv_lhs => rw [← hy]
    rw [map_mul, sigmaTensor_inv_apply]

  have hσey : σE e * y = y := by
    have h1 : e * AutomorphicForm.sigmaTensor K L Kv σ⁻¹ y = AutomorphicForm.sigmaTensor K L Kv σ⁻¹ y := by
      rw [hσ'y, mul_left_comm, hey]
    have h2 := congrArg σE h1
    rw [map_mul, sigmaTensor_apply_inv] at h2
    exact h2

  have hσe : σE e = (σE a * (↑xu⁻¹ : L ⊗[K] Kv)) * y := by
    rw [he, map_mul, hσy, mul_assoc]

  have hfix : σE e = e := by
    calc σE e = (σE a * (↑xu⁻¹ : L ⊗[K] Kv)) * y := hσe
      _ = (σE a * (↑xu⁻¹ : L ⊗[K] Kv)) * (e * y) := by rw [hey]
      _ = e * ((σE a * (↑xu⁻¹ : L ⊗[K] Kv)) * y) := by ring
      _ = e * σE e := by rw [← hσe]
      _ = (a * y) * σE e := by rw [he]
      _ = a * (σE e * y) := by ring
      _ = a * y := by rw [hσey]
      _ = e := rfl

  have hrange := (AutomorphicForm.sigmaTensor_apply_eq_self_iff K L Kv σ
    (fun z hz => mem_range_of_fixed K L σ hgen z hz) e).mp hfix
  obtain ⟨t, ht⟩ := hrange
  rw [Algebra.TensorProduct.includeRight_apply] at ht

  have hee : e * e = e := by
    calc e * e = a * (e * y) := by rw [he]; ring
      _ = a * y := by rw [hey]
      _ = e := he.symm

  have ht2 : (1 : L) ⊗ₜ[K] (t * (1 - t)) = 0 := by
    have : (1 : L) ⊗ₜ[K] (t * (1 - t)) = e - e * e := by
      rw [← ht, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_sub, mul_one, TensorProduct.tmul_sub]
    rw [this, hee, sub_self]
  have ht3 : t * (1 - t) = 0 := by
    by_contra hne
    have hu : IsUnit ((1 : L) ⊗ₜ[K] (t * (1 - t))) := by
      have := (isUnit_iff_ne_zero.mpr hne).map
        (Algebra.TensorProduct.includeRight : Kv →ₐ[K] L ⊗[K] Kv)
      rwa [Algebra.TensorProduct.includeRight_apply] at this
    rw [ht2] at hu
    exact not_isUnit_zero hu
  rcases mul_eq_zero.mp ht3 with h0 | h1
  ·
    exfalso; apply hy0
    rw [← hey, ← ht, h0, TensorProduct.tmul_zero, zero_mul]
  ·
    have : t = 1 := by rwa [sub_eq_zero, eq_comm] at h1
    rw [this] at ht
    have h1e : e = 1 := by rw [← ht]; rfl
    exact IsUnit.of_mul_eq_one_right a (by rw [← he, h1e])

include hgen in

theorem hilbert90 (x : L ⊗[K] Kv) (hx : Algebra.norm Kv x = 1) :
    ∃ y : (L ⊗[K] Kv)ˣ, x * σE (y : L ⊗[K] Kv) = y := by
  have hprod := prod_iterate_eq_one_of_norm_eq_one K L σ hgen v x hx
  obtain ⟨ℓ, hℓ⟩ := exists_S_tmul_ne_zero K L σ hgen v x
  have hfix := mul_sigma_S K L σ hgen v x (ℓ ⊗ₜ[K] 1) hprod
  have hu := isUnit_of_mul_sigma_eq K L σ hgen v x _ (isUnit_of_prod_eq_one K L σ hgen v x hprod) hfix hℓ
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hfix⟩

end Main2

end Ws35H.H90

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (x : L ⊗[K] v.adicCompletion K) (hx : Algebra.norm (v.adicCompletion K) x = 1) :
    ∃ y : (L ⊗[K] v.adicCompletion K)ˣ,
      x * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y = y :=
  Ws35H.H90.hilbert90 K L σ hgen v x hx

end
end S_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one (solution)
