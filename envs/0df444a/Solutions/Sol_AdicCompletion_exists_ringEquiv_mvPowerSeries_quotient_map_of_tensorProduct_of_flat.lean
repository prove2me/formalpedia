-- Prove2me | solution 1 for AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8305e43c-c308-5cb9-83cd-c842b4669acd

import Mathlib
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
import Theorems.Thm_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat

set_option autoImplicit false

namespace StalkBC

p2m_open "Ideal Quotient Ideal.Quotient AdicCompletion"

section Generic

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk I hle r]

theorem exists_sub_algebraMap_mem_map_pow (hI : I.FG) (x : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, x - algebraMap R (AdicCompletion I R) r ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨r, ?_⟩
  have hle : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by
    rw [smul_eq_mul, Ideal.mul_top]
  have h1 : x - algebraMap R (AdicCompletion I R) r ∈
      (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, ← factor_evalₐ_eq_eval I _ hle, map_sub,
      ← hr, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of,
      sub_self, _root_.map_zero]
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

theorem ringHom_ext_of_isHausdorff (hI : I.FG) {C : Type*} [CommRing C] (J : Ideal C)
    [IsHausdorff J C] (g₁ g₂ : AdicCompletion I R →+* C)
    (h₁ : ∀ r ∈ I, g₁ (algebraMap R (AdicCompletion I R) r) ∈ J)
    (h₂ : ∀ r ∈ I, g₂ (algebraMap R (AdicCompletion I R) r) ∈ J)
    (h : ∀ r : R, g₁ (algebraMap R (AdicCompletion I R) r) = g₂ (algebraMap R (AdicCompletion I R) r)) :
    g₁ = g₂ := by
  refine RingHom.ext fun x => ?_
  refine (IsHausdorff.eq_iff_smodEq (I := J)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow I hI x n
  have key : ∀ g : AdicCompletion I R →+* C, (∀ r ∈ I, g (algebraMap R (AdicCompletion I R) r) ∈ J) →
      g (x - algebraMap R (AdicCompletion I R) r) ∈ J ^ n := by
    intro g hg
    have hIJ : I ≤ J.comap (g.comp (algebraMap R (AdicCompletion I R))) := fun r hr => hg r hr
    have hpow : I ^ n ≤ (J ^ n).comap (g.comp (algebraMap R (AdicCompletion I R))) :=
      (Ideal.pow_right_mono hIJ n).trans (Ideal.le_comap_pow _ n)
    have hmap : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤ (J ^ n).comap g := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      exact hpow
    exact hmap hr
  have e : g₁ x - g₂ x = g₁ (x - algebraMap R _ r) - g₂ (x - algebraMap R _ r) := by
    rw [map_sub, map_sub, h r]; ring
  rw [e]
  exact Ideal.sub_mem _ (key g₁ h₁) (key g₂ h₂)

theorem exists_ringHom_comp_algebraMap {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S]
    (f : R →+* S) (hf : ∀ x ∈ I, f x ∈ J) :
    ∃ g : AdicCompletion I R →+* S, ∀ x : R, g (algebraMap R (AdicCompletion I R) x) = f x := by
  have hmap : Ideal.map f I ≤ J := Ideal.map_le_iff_le_comap.mpr fun x hx => hf x hx
  have hpow : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let fam : (n : ℕ) → AdicCompletion I R →+* S ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) f (hpow n)).comp (evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)
  have hfam : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow J hle).comp (fam n) = fam m := by
    intro m n hle
    apply RingHom.ext
    intro x
    change Ideal.Quotient.factorPow J hle (Ideal.quotientMap (J ^ n) f (hpow n) (evalₐ I n x)) =
      Ideal.quotientMap (J ^ m) f (hpow m) (evalₐ I m x)
    rw [← factorPow_evalₐ I hle x]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    rw [← hr, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]
  let g : AdicCompletion I R →+* S := IsAdicComplete.liftRingHom J fam hfam
  refine ⟨g, fun x => ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := J)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  change Ideal.Quotient.mk (J ^ n) (IsAdicComplete.liftRingHom J fam hfam _) = _
  rw [IsAdicComplete.mk_liftRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  change Ideal.quotientMap (J ^ n) f (hpow n) (evalₐ I n (of I R x)) = _
  rw [evalₐ_of, Ideal.quotientMap_mk]

theorem isAdicComplete_map (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  (IsAdicComplete.map_algebraMap_iff (R := R) (S := AdicCompletion I R) (M := AdicCompletion I R)
    (I := I)).mpr (AdicCompletion.isAdicComplete hI)

theorem nontrivial_of_ne_top (hI : I ≠ ⊤) : Nontrivial (AdicCompletion I R) := by
  have h1 : (I ^ 1) ≠ ⊤ := by rwa [pow_one]
  haveI : Nontrivial (R ⧸ I ^ 1) := Ideal.Quotient.nontrivial_iff.mpr h1
  exact (surjective_evalₐ I 1).nontrivial

theorem isUnit_add_of_mem_jacobson_bot' {C : Type*} [CommRing C] {v j : C} (hv : IsUnit v)
    (hj : j ∈ (⊥ : Ideal C).jacobson) : IsUnit (v + j) := by
  obtain ⟨u, rfl⟩ := hv
  have h1 : IsUnit (j * ↑u⁻¹ + 1) := Ideal.mem_jacobson_bot.mp hj _
  have h2 : (↑u : C) + j = (j * ↑u⁻¹ + 1) * ↑u := by
    rw [add_mul, one_mul, mul_assoc, Units.inv_mul, mul_one, add_comm]
  rw [h2]
  exact h1.mul (Units.isUnit u)

theorem isLocalRing_and_maximalIdeal_eq {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal] (hfg : I.FG) :
    ∃ _ : IsLocalRing (AdicCompletion I R),
      IsLocalRing.maximalIdeal (AdicCompletion I R) = I.map (algebraMap R (AdicCompletion I R)) := by
  haveI := isAdicComplete_map I hfg
  haveI : Nontrivial (AdicCompletion I R) := nontrivial_of_ne_top I hI.ne_top
  set J : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R)) with hJ
  have hJjac : J ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson := IsAdicComplete.le_jacobson_bot J

  have hunit : ∀ x : AdicCompletion I R, x ∉ J → IsUnit x := by
    intro x hx
    obtain ⟨d, hd⟩ := exists_sub_algebraMap_mem_map_pow I hfg x 1
    rw [pow_one] at hd
    have hdI : d ∉ I := by
      intro hdI
      apply hx
      have : x = (x - algebraMap R _ d) + algebraMap R _ d := by ring
      rw [this]
      exact J.add_mem hd (Ideal.mem_map_of_mem _ hdI)
    obtain ⟨y, i, hi, hyi⟩ := hI.exists_inv hdI
    have h1 : IsUnit (algebraMap R (AdicCompletion I R) d * algebraMap R (AdicCompletion I R) y) := by
      have e : algebraMap R (AdicCompletion I R) d * algebraMap R (AdicCompletion I R) y =
          1 + (- algebraMap R (AdicCompletion I R) i) := by
        rw [← _root_.map_mul, ← _root_.map_one (algebraMap R (AdicCompletion I R)), ← _root_.map_neg,
          ← _root_.map_add]
        congr 1
        rw [← hyi]
        ring
      rw [e]
      exact isUnit_add_of_mem_jacobson_bot' isUnit_one (hJjac (J.neg_mem (Ideal.mem_map_of_mem _ hi)))
    have h2 : IsUnit (algebraMap R (AdicCompletion I R) d) := isUnit_of_mul_isUnit_left h1
    have : x = algebraMap R _ d + (x - algebraMap R _ d) := by ring
    rw [this]
    exact isUnit_add_of_mem_jacobson_bot' h2 (hJjac hd)

  have hJne : J ≠ ⊤ := by
    intro h
    have : (⊥ : Ideal (AdicCompletion I R)).jacobson = ⊤ := top_le_iff.mp (h ▸ hJjac)
    rw [Ideal.jacobson_eq_top_iff] at this
    exact bot_ne_top this
  have hnon : ∀ x ∈ J, ¬ IsUnit x := fun x hx hu => hJne (Ideal.eq_top_of_isUnit_mem _ hx hu)
  haveI : IsLocalRing (AdicCompletion I R) := by
    refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
    have ha' : a ∈ J := by by_contra h; exact ha (hunit a h)
    have hb' : b ∈ J := by by_contra h; exact hb (hunit b h)
    exact hnon _ (J.add_mem ha' hb')
  refine ⟨inferInstance, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp hx (hunit x h)
  · intro x hx
    exact (IsLocalRing.mem_maximalIdeal _).mpr (hnon x hx)

end Generic

section LocalPS

open MvPowerSeries IsLocalRing

variable {K : Type*} [CommRing K]

theorem span_pair_eq_span_range :
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1} =
      Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) K)) := by
  congr 1
  ext f
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two, eq_comm]

theorem mem_span_pair_of_constantCoeff_eq_zero (s : MvPowerSeries (Fin 2) K)
    (hs : constantCoeff s = 0) : s ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1} := by
  rw [span_pair_eq_span_range, MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]
  exact hs

theorem map_mem_span_pair {L : Type*} [CommRing L] (f : K →+* L) (s : MvPowerSeries (Fin 2) K)
    (hs : s ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1}) :
    MvPowerSeries.map f s ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) L), X 1} := by
  have : (Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1}).map (MvPowerSeries.map f) ≤
      Ideal.span {(X 0 : MvPowerSeries (Fin 2) L), X 1} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [map_X]; exact Ideal.subset_span (by simp)
    · rw [map_X]; exact Ideal.subset_span (by simp)
  exact this (Ideal.mem_map_of_mem _ hs)

variable [IsLocalRing K]

theorem mem_maximalIdeal_iff_constantCoeff (s : MvPowerSeries (Fin 2) K) :
    s ∈ maximalIdeal (MvPowerSeries (Fin 2) K) ↔ constantCoeff s ∈ maximalIdeal K := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

theorem mem_span_pair_sup_of_constantCoeff_mem (s : MvPowerSeries (Fin 2) K)
    (hs : constantCoeff s ∈ maximalIdeal K) :
    s ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1} ⊔
      (maximalIdeal K).map (C : K →+* MvPowerSeries (Fin 2) K) := by
  have e : s = (s - C (constantCoeff s)) + C (constantCoeff s) := by ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Ideal.mem_map_of_mem _ hs)
  apply mem_span_pair_of_constantCoeff_eq_zero
  rw [map_sub, constantCoeff_C, sub_self]

noncomputable def resL (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K) :
    MvPowerSeries (Fin 2) K ⧸ Ideal.span {g} →+* ResidueField K :=
  Ideal.Quotient.lift _ ((residue K).comp constantCoeff) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [RingHom.comp_apply, _root_.map_mul, _root_.map_mul, (residue_eq_zero_iff _).mpr hg, mul_zero]

@[scoped simp] theorem resL_mk (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K)
    (s : MvPowerSeries (Fin 2) K) :
    resL g hg (Ideal.Quotient.mk _ s) = residue K (constantCoeff s) :=
  Ideal.Quotient.lift_mk _ _ _

theorem resL_surjective (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K) :
    Function.Surjective (resL g hg) := fun w => by
  obtain ⟨w, rfl⟩ := residue_surjective w
  exact ⟨Ideal.Quotient.mk _ (C w), by rw [resL_mk, constantCoeff_C]⟩

theorem mem_map_maximalIdeal_of_resL_eq_zero (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K)
    (t : MvPowerSeries (Fin 2) K ⧸ Ideal.span {g}) (ht : resL g hg t = 0) :
    t ∈ (maximalIdeal (MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g})) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [resL_mk, residue_eq_zero_iff] at ht
  exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal_iff_constantCoeff s).mpr ht)

theorem resL_eq_zero_of_mem_map_maximalIdeal (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K)
    (t : MvPowerSeries (Fin 2) K ⧸ Ideal.span {g})
    (ht : t ∈ (maximalIdeal (MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g}))) :
    resL g hg t = 0 := by
  have hle : (maximalIdeal (MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g})) ≤
      RingHom.ker (resL g hg) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker, resL_mk, residue_eq_zero_iff]
    exact (mem_maximalIdeal_iff_constantCoeff s).mp hs
  exact hle ht

theorem resL_eq_zero_of_mem_map_span_pair_sup (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K)
    (t : MvPowerSeries (Fin 2) K ⧸ Ideal.span {g})
    (ht : t ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1} ⊔
      (maximalIdeal K).map (C : K →+* MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g}))) :
    resL g hg t = 0 := by
  apply resL_eq_zero_of_mem_map_maximalIdeal g hg t
  refine Ideal.map_mono ?_ ht
  refine sup_le ?_ ?_
  · rw [Ideal.span_le]
    rintro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;>
      simp only [SetLike.mem_coe, mem_maximalIdeal_iff_constantCoeff, constantCoeff_X, Ideal.zero_mem]
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff_constantCoeff, constantCoeff_C]
    exact ha

theorem isAdicComplete_quotient_local [IsNoetherianRing K] [IsAdicComplete (maximalIdeal K) K]
    (g : MvPowerSeries (Fin 2) K) :
    IsAdicComplete ((maximalIdeal (MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g})))
      (MvPowerSeries (Fin 2) K ⧸ Ideal.span {g}) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) K) := MvPowerSeries.isNoetherianRing_fin K 2
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin 2) K)) (MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.isAdicComplete_maximalIdeal
  haveI : Module.Finite (MvPowerSeries (Fin 2) K) (MvPowerSeries (Fin 2) K ⧸ Ideal.span {g}) := inferInstance
  have hc : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin 2) K)) (MvPowerSeries (Fin 2) K ⧸ Ideal.span {g}) :=
    IsAdicComplete.of_finite_of_isNoetherianRing _ _
  rw [← Ideal.Quotient.algebraMap_eq]
  exact (IsAdicComplete.map_algebraMap_iff (R := MvPowerSeries (Fin 2) K)
    (S := MvPowerSeries (Fin 2) K ⧸ Ideal.span {g}) (M := MvPowerSeries (Fin 2) K ⧸ Ideal.span {g})
    (I := maximalIdeal (MvPowerSeries (Fin 2) K))).mpr hc

end LocalPS

section Chart

open MvPowerSeries IsLocalRing

variable {R₀ : Type*} [CommRing R₀] (𝔫₀ : Ideal R₀) {W : Type*} [CommRing W] [IsLocalRing W]

theorem constantCoeff_mem_of_ringEquiv [𝔫₀.IsMaximal] (g : MvPowerSeries (Fin 2) W)
    (e₀ : AdicCompletion 𝔫₀ R₀ ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) :
    constantCoeff g ∈ maximalIdeal W := by
  haveI : Nontrivial (AdicCompletion 𝔫₀ R₀) := nontrivial_of_ne_top 𝔫₀ (Ideal.IsMaximal.ne_top inferInstance)
  haveI : Nontrivial (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) := e₀.injective.nontrivial
  have hne : Ideal.span {g} ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hu : ¬ IsUnit g := fun hu => hne (Ideal.span_singleton_eq_top.mpr hu)
  rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
  exact (mem_maximalIdeal _).mpr hu

theorem resL_ringEquiv_eq_zero_of_mem_map [𝔫₀.IsMaximal] (h𝔫₀ : 𝔫₀.FG) (g : MvPowerSeries (Fin 2) W)
    (e₀ : AdicCompletion 𝔫₀ R₀ ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {g})
    (hg : constantCoeff g ∈ maximalIdeal W)
    (y : AdicCompletion 𝔫₀ R₀) (hy : y ∈ 𝔫₀.map (algebraMap R₀ (AdicCompletion 𝔫₀ R₀))) :
    resL g hg (e₀ y) = 0 := by
  haveI := isAdicComplete_map 𝔫₀ h𝔫₀
  set K₀ : Ideal (AdicCompletion 𝔫₀ R₀) := RingHom.ker ((resL g hg).comp e₀.toRingHom) with hK₀
  have hmax : K₀.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ ((resL_surjective g hg).comp e₀.surjective)
  have hle : 𝔫₀.map (algebraMap R₀ (AdicCompletion 𝔫₀ R₀)) ≤ K₀ :=
    (IsAdicComplete.le_jacobson_bot _).trans (sInf_le ⟨bot_le, hmax⟩)
  exact hle hy

end Chart

section Main

open MvPowerSeries TensorProduct IsLocalRing

noncomputable def tau {k κ : Type*} [CommRing k] [CommRing κ] (σ : k →+* κ)
    (h : MvPowerSeries (Fin 2) k) :
    (MvPowerSeries (Fin 2) k ⧸ Ideal.span {h}) →+*
      (MvPowerSeries (Fin 2) κ ⧸ Ideal.span {MvPowerSeries.map σ h}) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPowerSeries.map σ)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [RingHom.comp_apply, _root_.map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

@[scoped simp] theorem tau_mk {k κ : Type*} [CommRing k] [CommRing κ] (σ : k →+* κ)
    (h : MvPowerSeries (Fin 2) k) (s : MvPowerSeries (Fin 2) k) :
    tau σ h (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (MvPowerSeries.map σ s) :=
  Ideal.Quotient.lift_mk _ _ _

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)]
    [PerfectField (ResidueField A₀)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀] [Algebra A₀ W₀]
    (hW₀ : maximalIdeal W₀ = (maximalIdeal A₀).map (algebraMap A₀ W₀))
    (g₀ : MvPowerSeries (Fin 2) W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀})
    (he₀ : ∀ a : A₀, e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) (algebraMap A₀ B₀ a)) = (Ideal.Quotient.mk (Ideal.span {g₀})) (C (algebraMap A₀ W₀ a)))
    (ψ : W₀ →+* (AdicCompletion (maximalIdeal A) A))
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ W₀ a) = (algebraMap A (AdicCompletion (maximalIdeal A) A)) (algebraMap A₀ A a))
    (χ : B₀ →+* ResidueField A)
    (hχ : ∀ (b : B₀) (w : W₀),
      e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b) - (Ideal.Quotient.mk (Ideal.span {g₀})) (C w) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map (Ideal.Quotient.mk (Ideal.span {g₀})) →
      ∃ a : A, IsLocalRing.residue A a = χ b ∧ ψ w - (algebraMap A (AdicCompletion (maximalIdeal A) A)) a ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
    (ev : (A ⊗[A₀] B₀) →+* ResidueField A)
    (hev : ∀ (a : A) (b : B₀), ev (a ⊗ₜ[A₀] b) = IsLocalRing.residue A a * χ b) :
    ∃ (_ : (RingHom.ker ev).IsMaximal)
      (e : (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) ≃+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀})),
      (∀ a : A, e ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) (algebraMap A (A ⊗[A₀] B₀) a)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a))) ∧
      (∀ (b : B₀) (s : MvPowerSeries (Fin 2) W₀), e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b) = (Ideal.Quotient.mk (Ideal.span {g₀})) s →
        e ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) ((1 : A) ⊗ₜ[A₀] b)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (MvPowerSeries.map ψ s)) := by
  classical

  obtain ⟨instAloc, instAhom, hAc, hAmap, hAdense⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq A
  haveI := instAloc
  haveI := instAhom
  haveI := hAc
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal A) A) := AdicCompletion.isNoetherianRing_of_isNoetherianRing _

  have hg₀ : constantCoeff g₀ ∈ maximalIdeal W₀ := constantCoeff_mem_of_ringEquiv 𝔪₀ g₀ e₀
  have hψ𝔪 : ∀ w ∈ maximalIdeal W₀, ψ w ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
    intro w hw
    rw [hW₀] at hw
    have hle : (maximalIdeal A₀).map (algebraMap A₀ W₀) ≤ (maximalIdeal (AdicCompletion (maximalIdeal A) A)).comap ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, hψ]
      exact map_nonunit (algebraMap A (AdicCompletion (maximalIdeal A) A)) _ (map_nonunit (algebraMap A₀ A) a ha)
    exact hle hw
  have hg₀' : constantCoeff (MvPowerSeries.map ψ g₀) ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
    rw [constantCoeff_map]
    exact hψ𝔪 _ hg₀

  have hevs : Function.Surjective ev := fun x => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨a ⊗ₜ 1, by rw [hev, _root_.map_one, mul_one]⟩
  have h𝔪max : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hevs
  haveI : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing A₀ B₀
  haveI : IsNoetherianRing (A ⊗[A₀] B₀) := Algebra.FiniteType.isNoetherianRing A (A ⊗[A₀] B₀)
  have h𝔪₀fg : 𝔪₀.FG := IsNoetherian.noetherian 𝔪₀
  have h𝔪fg : (RingHom.ker ev).FG := IsNoetherian.noetherian _
  have h𝔪Afg : (maximalIdeal A).FG := IsNoetherian.noetherian _

  let ρ : ResidueField A →+* ResidueField (AdicCompletion (maximalIdeal A) A) := IsLocalRing.ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
  have hρ : ∀ a : A, ρ (IsLocalRing.residue A a) = IsLocalRing.residue (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a) := fun a =>
    IsLocalRing.ResidueField.map_residue _ a
  have hρinj : Function.Injective ρ := ρ.injective

  have hχ' : ∀ (b : B₀) (s : MvPowerSeries (Fin 2) W₀), e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b) = (Ideal.Quotient.mk (Ideal.span {g₀})) s →
      ρ (χ b) = IsLocalRing.residue (AdicCompletion (maximalIdeal A) A) (ψ (constantCoeff s)) := by
    intro b s hs
    obtain ⟨a, ha, hmem⟩ := hχ b (constantCoeff s) (by
      rw [hs, ← map_sub]
      refine Ideal.mem_map_of_mem _ (mem_span_pair_sup_of_constantCoeff_mem _ ?_)
      rw [map_sub, constantCoeff_C, sub_self]
      exact Ideal.zero_mem _)
    rw [← ha, hρ, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [hAmap] at hmem
    exact hmem

  obtain ⟨instBloc, hmaxJ⟩ := isLocalRing_and_maximalIdeal_eq (RingHom.ker ev) h𝔪fg
  haveI := instBloc
  set J : Ideal (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := (RingHom.ker ev).map (algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) with hJ
  haveI hJc : IsAdicComplete J (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := isAdicComplete_map (RingHom.ker ev) h𝔪fg
  haveI : IsHausdorff (maximalIdeal (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := by rw [hmaxJ]; infer_instance

  have hE0 : ∀ y ∈ 𝔪₀.map (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)), resL g₀ hg₀ (e₀ y) = 0 :=
    resL_ringEquiv_eq_zero_of_mem_map 𝔪₀ h𝔪₀fg g₀ e₀ hg₀
  have hinc : ∀ b ∈ 𝔪₀, ((1 : A) ⊗ₜ[A₀] b : (A ⊗[A₀] B₀)) ∈ RingHom.ker ev := by
    intro b hb
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b))
    have h1 : IsLocalRing.residue W₀ (constantCoeff s) = 0 := by
      rw [← resL_mk g₀ hg₀, hs]
      exact hE0 _ (Ideal.mem_map_of_mem _ hb)
    have h2 : ρ (χ b) = 0 := by
      rw [hχ' b s hs.symm, IsLocalRing.residue_eq_zero_iff]
      exact hψ𝔪 _ ((IsLocalRing.residue_eq_zero_iff _).mp h1)
    rw [RingHom.mem_ker, hev, _root_.map_one, one_mul]
    exact hρinj (by rw [h2, _root_.map_zero])
  have hincA : ∀ a ∈ maximalIdeal A, (a ⊗ₜ[A₀] (1 : B₀) : (A ⊗[A₀] B₀)) ∈ RingHom.ker ev := by
    intro a ha
    rw [RingHom.mem_ker, hev, _root_.map_one, mul_one, IsLocalRing.residue_eq_zero_iff]
    exact ha

  obtain ⟨ι, hι⟩ := exists_ringHom_comp_algebraMap 𝔪₀ J
    ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))).comp (Algebra.TensorProduct.includeRight (R := A₀) (A := A) (B := B₀)).toRingHom)
    (fun b hb => Ideal.mem_map_of_mem _ (hinc b hb))
  replace hι : ∀ b : B₀, ι ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b) = (algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) ((1 : A) ⊗ₜ[A₀] b) := hι
  obtain ⟨lam, hlam⟩ := exists_ringHom_comp_algebraMap (maximalIdeal A) J
    ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))).comp (Algebra.TensorProduct.includeLeftRingHom (R := A₀) (A := A) (B := B₀)))
    (fun a ha => Ideal.mem_map_of_mem _ (hincA a ha))
  replace hlam : ∀ a : A, lam ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a) = (algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) (a ⊗ₜ[A₀] (1 : B₀)) := hlam
  have hιJ : (𝔪₀.map (algebraMap B₀ (AdicCompletion 𝔪₀ B₀))).map ι ≤ J := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.comp_apply, hι]
    exact Ideal.mem_map_of_mem _ (hinc b hb)
  have hlamJ : ∀ m ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A), lam m ∈ J := by
    intro m hm
    rw [← hAmap] at hm
    have hle : ((maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))).map lam ≤ J := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.comp_apply, hlam]
      exact Ideal.mem_map_of_mem _ (hincA a ha)
    exact hle (Ideal.mem_map_of_mem _ hm)

  have IJ : ∀ (y : AdicCompletion 𝔪₀ B₀) (w : W₀),
      resL g₀ hg₀ (e₀ y) = IsLocalRing.residue W₀ w → ι y - lam (ψ w) ∈ J := by
    intro y w hyw
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow 𝔪₀ h𝔪₀fg y 1
    rw [pow_one] at hr
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) r))
    have h1 : IsLocalRing.residue W₀ (constantCoeff s) = IsLocalRing.residue W₀ w := by
      have h0 := hE0 _ hr
      rw [map_sub, map_sub, hyw, sub_eq_zero] at h0
      rw [← resL_mk g₀ hg₀, hs, h0]
    have h1' : ψ (constantCoeff s) - ψ w ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
      rw [← map_sub]
      apply hψ𝔪
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact h1
    obtain ⟨a, ha⟩ := hAdense (ψ w)
    have h2 : χ r = IsLocalRing.residue A a := by
      apply hρinj
      rw [hχ' r s hs.symm, hρ, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      have e1 : ψ (constantCoeff s) - (algebraMap A (AdicCompletion (maximalIdeal A) A)) a = (ψ (constantCoeff s) - ψ w) + (ψ w - (algebraMap A (AdicCompletion (maximalIdeal A) A)) a) := by ring
      rw [e1]
      exact Ideal.add_mem _ h1' ha
    have h3 : ((1 : A) ⊗ₜ[A₀] r : (A ⊗[A₀] B₀)) - (a ⊗ₜ[A₀] (1 : B₀)) ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, map_sub, hev, hev, _root_.map_one, one_mul, _root_.map_one, mul_one, h2, sub_self]
    have h4 : ι ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) r) - lam ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a) ∈ J := by
      rw [hι, hlam, ← map_sub]
      exact Ideal.mem_map_of_mem _ h3
    have h5 : ι (y - (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) r) ∈ J := hιJ (Ideal.mem_map_of_mem _ hr)
    have h6 : lam (ψ w - (algebraMap A (AdicCompletion (maximalIdeal A) A)) a) ∈ J := hlamJ _ ha
    have h7 : ι y - lam (ψ w) =
        ι (y - (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) r) + (ι ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) r) - lam ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) - lam (ψ w - (algebraMap A (AdicCompletion (maximalIdeal A) A)) a) := by
      rw [map_sub, map_sub]; ring
    rw [h7]
    exact J.sub_mem (J.add_mem h5 h4) h6

  haveI : IsLocalHom (algebraMap A₀ W₀) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : algebraMap A₀ W₀ a ∈ maximalIdeal W₀ := by
      rw [hW₀]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hna)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : HenselianLocalRing W₀ :=
    { toIsLocalRing := inferInstance
      is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal W₀) f hf a₀ h₁ (h₂.map _) }
  let r₀ : B₀ →ₐ[A₀] ResidueField W₀ :=
    { toRingHom := (resL g₀ hg₀).comp (e₀.toRingHom.comp (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)))
      commutes' := fun a => by
        have e1 : ((resL g₀ hg₀).comp (e₀.toRingHom.comp (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)))) (algebraMap A₀ B₀ a) =
            resL g₀ hg₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) (algebraMap A₀ B₀ a))) := rfl
        refine e1.trans ?_
        rw [he₀, resL_mk, constantCoeff_C]
        rfl }
  have hr₀s : Function.Surjective r₀ := by
    intro x
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, hb⟩ := exists_sub_algebraMap_mem_map_pow 𝔪₀ h𝔪₀fg (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (C w))) 1
    rw [pow_one] at hb
    refine ⟨b, ?_⟩
    change resL g₀ hg₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b)) = IsLocalRing.residue W₀ w
    have h0 := hE0 _ hb
    rw [map_sub, map_sub, RingEquiv.apply_symm_apply, resL_mk, constantCoeff_C, sub_eq_zero] at h0
    exact h0.symm
  haveI : Algebra.FiniteType A₀ (ResidueField W₀) :=
    (inferInstance : Algebra.FiniteType A₀ B₀).of_surjective r₀ hr₀s
  haveI : Algebra.FiniteType (ResidueField A₀) (ResidueField W₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A₀ (ResidueField A₀) (ResidueField W₀)
  haveI : Module.Finite (ResidueField A₀) (ResidueField W₀) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsAlgebraic (ResidueField A₀) (ResidueField W₀) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hu₁loc : IsLocalHom (lam.comp ψ) := by
    refine ⟨fun w hw => ?_⟩
    by_contra hnw
    have h1 : lam (ψ w) ∈ J := hlamJ _ (hψ𝔪 w ((IsLocalRing.mem_maximalIdeal _).mpr hnw))
    rw [← hmaxJ] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 hw

  have hrig : ∀ w : W₀, ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (C w))) = lam (ψ w) := by
    have key := IsLocalRing.ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable
      A₀ W₀ (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) hW₀ (lam.comp ψ) (ι.comp (e₀.symm.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {g₀})).comp (C : W₀ →+* MvPowerSeries (Fin 2) W₀))))
      (RingHom.ext fun a => by
        change lam (ψ (algebraMap A₀ W₀ a)) = ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (C (algebraMap A₀ W₀ a))))
        rw [← he₀, RingEquiv.symm_apply_apply, hι, hψ, hlam,
          ← Algebra.TensorProduct.algebraMap_apply' (R := A₀) (A := A) (B := B₀) a]
        rfl)
      (fun w => by
        change lam (ψ w) - ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (C w))) ∈ maximalIdeal (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))
        rw [hmaxJ, ← neg_sub]
        exact J.neg_mem (IJ (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (C w))) w
          (by rw [RingEquiv.apply_symm_apply, resL_mk, constantCoeff_C])))
    intro w
    exact (RingHom.congr_fun key w).symm

  set x : Fin 2 → (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := fun i => ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (X i))) with hxdef
  have hxJ : ∀ i, x i ∈ J := by
    intro i
    have h0 := IJ (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (X i))) 0
      (by rw [RingEquiv.apply_symm_apply, resL_mk, constantCoeff_X, _root_.map_zero])
    rwa [_root_.map_zero, _root_.map_zero, sub_zero] at h0
  letI algAB : Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := lam.toAlgebra
  obtain ⟨θ, hθ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := (AdicCompletion (maximalIdeal A) A)) J x hxJ
  have hθC : ∀ c : (AdicCompletion (maximalIdeal A) A), θ (C c) = lam c := by
    intro c
    have hc := θ.commutes c
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hc
    exact hc

  have hΘ : ∀ s : MvPowerSeries (Fin 2) W₀, θ (MvPowerSeries.map ψ s) = ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) s)) := by
    letI : Algebra W₀ (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) := (lam.comp ψ).toAlgebra
    let Θ₁ : MvPowerSeries (Fin 2) W₀ →ₐ[W₀] (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) :=
      { toRingHom := θ.toRingHom.comp (MvPowerSeries.map ψ)
        commutes' := fun w => by
          change θ (MvPowerSeries.map ψ (algebraMap W₀ (MvPowerSeries (Fin 2) W₀) w)) = lam (ψ w)
          rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C, hθC] }
    let Θ₂ : MvPowerSeries (Fin 2) W₀ →ₐ[W₀] (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) :=
      { toRingHom := ι.comp (e₀.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {g₀})))
        commutes' := fun w => by
          change ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (algebraMap W₀ (MvPowerSeries (Fin 2) W₀) w))) = lam (ψ w)
          rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hrig] }
    have hΘ12 : Θ₁ = Θ₂ :=
      MvPowerSeries.algHom_ext_of_apply_X_mem J Θ₁ Θ₂
        (fun i => by
          change θ (MvPowerSeries.map ψ (X i)) ∈ J
          rw [map_X, hθ]
          exact hxJ i)
        (fun i => by
          change θ (MvPowerSeries.map ψ (X i)) = ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (X i)))
          rw [map_X, hθ])
    intro s
    exact AlgHom.congr_fun hΘ12 s

  have hθg : θ (MvPowerSeries.map ψ g₀) = 0 := by
    rw [hΘ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g₀), _root_.map_zero,
      _root_.map_zero]
  let θbar : (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) →+* (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) :=
    Ideal.Quotient.lift _ θ.toRingHom fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      change θ (c * MvPowerSeries.map ψ g₀) = 0
      rw [_root_.map_mul, hθg, mul_zero]
  have hθbar : ∀ s, θbar ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) s) = θ s := fun s => Ideal.Quotient.lift_mk _ _ _

  set J_T : Ideal (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) := (maximalIdeal (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A))).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) with hJT
  haveI hTc : IsAdicComplete J_T (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) := isAdicComplete_quotient_local (MvPowerSeries.map ψ g₀)

  have halgT₀ : ∀ a₀ : A₀, algebraMap A₀ (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) a₀ = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) (algebraMap A₀ A a₀))) := by
    intro a₀
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply, AdicCompletion.algebraMap_apply,
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  let f₁ : A →ₐ[A₀] (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) :=
    { toRingHom := (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})).comp ((C : (AdicCompletion (maximalIdeal A) A) →+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A))).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))
      commutes' := fun a₀ => by
        have e1 : ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})).comp ((C : (AdicCompletion (maximalIdeal A) A) →+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A))).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))) (algebraMap A₀ A a₀) =
            (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) (algebraMap A₀ A a₀))) := rfl
        exact e1.trans (halgT₀ a₀).symm }
  let f₂ : B₀ →ₐ[A₀] (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) :=
    { toRingHom := (tau ψ g₀).comp (e₀.toRingHom.comp (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)))
      commutes' := fun a₀ => by
        have e1 : ((tau ψ g₀).comp (e₀.toRingHom.comp (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)))) (algebraMap A₀ B₀ a₀) =
            tau ψ g₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) (algebraMap A₀ B₀ a₀))) := rfl
        refine e1.trans ?_
        rw [he₀, tau_mk, map_C, hψ]
        exact (halgT₀ a₀).symm }
  have hcomm : ∀ (a : A) (b : B₀), Commute (f₁ a) (f₂ b) := fun _ _ => Commute.all _ _
  let φ : (A ⊗[A₀] B₀) →+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) := (Algebra.TensorProduct.lift f₁ f₂ hcomm).toRingHom
  have hf₁ : ∀ a : A, f₁ a = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) := fun a => rfl
  have hf₂ : ∀ b : B₀, f₂ b = tau ψ g₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b)) := fun b => rfl
  have hφ : ∀ (a : A) (b : B₀), φ (a ⊗ₜ[A₀] b) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) * tau ψ g₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b)) := by
    intro a b
    have e1 : φ (a ⊗ₜ[A₀] b) = f₁ a * f₂ b := Algebra.TensorProduct.lift_tmul f₁ f₂ hcomm a b
    rw [e1, hf₁, hf₂]

  have hresφ : ∀ z : (A ⊗[A₀] B₀), resL (MvPowerSeries.map ψ g₀) hg₀' (φ z) = ρ (ev z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a b =>
        obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b))
        rw [hφ, hev, _root_.map_mul, _root_.map_mul, resL_mk, constantCoeff_C, ← hs, tau_mk, resL_mk,
          constantCoeff_map, hρ, hχ' b s hs.symm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ𝔪 : ∀ z ∈ RingHom.ker ev, φ z ∈ J_T := fun z hz =>
    mem_map_maximalIdeal_of_resL_eq_zero _ hg₀' _ (by rw [hresφ, RingHom.mem_ker.mp hz, _root_.map_zero])

  obtain ⟨φh, hφh⟩ := exists_ringHom_comp_algebraMap (RingHom.ker ev) J_T φ hφ𝔪
  replace hφh : ∀ z : (A ⊗[A₀] B₀), φh ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) z) = φ z := hφh

  have hτJ : ∀ y ∈ 𝔪₀.map (algebraMap B₀ (AdicCompletion 𝔪₀ B₀)), tau ψ g₀ (e₀ y) ∈ J_T := by
    intro y hy
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ y)
    have h1 : IsLocalRing.residue W₀ (constantCoeff s) = 0 := by
      rw [← resL_mk g₀ hg₀, hs]
      exact hE0 y hy
    rw [← hs, tau_mk]
    apply mem_map_maximalIdeal_of_resL_eq_zero _ hg₀'
    rw [resL_mk, constantCoeff_map, IsLocalRing.residue_eq_zero_iff]
    exact hψ𝔪 _ ((IsLocalRing.residue_eq_zero_iff _).mp h1)
  have hφι : ∀ y : AdicCompletion 𝔪₀ B₀, φh (ι y) = tau ψ g₀ (e₀ y) := by
    have key := ringHom_ext_of_isHausdorff 𝔪₀ h𝔪₀fg J_T (φh.comp ι) ((tau ψ g₀).comp e₀.toRingHom)
      (fun b hb => by
        change φh (ι ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b)) ∈ J_T
        rw [hι, hφh]
        exact hφ𝔪 _ (hinc b hb))
      (fun b hb => hτJ _ (Ideal.mem_map_of_mem _ hb))
      (fun b => by
        change φh (ι ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b)) = tau ψ g₀ (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b))
        rw [hι, hφh, hφ, _root_.map_one, _root_.map_one, _root_.map_one, one_mul])
    intro y
    exact RingHom.congr_fun key y

  have hφlam : ∀ c : (AdicCompletion (maximalIdeal A) A), φh (lam c) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C c) := by
    have key := ringHom_ext_of_isHausdorff (maximalIdeal A) h𝔪Afg J_T (φh.comp lam)
      ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})).comp (C : (AdicCompletion (maximalIdeal A) A) →+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A))))
      (fun a ha => by
        change φh (lam ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) ∈ J_T
        rw [hlam, hφh]
        exact hφ𝔪 _ (hincA a ha))
      (fun a ha => by
        change (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) ∈ J_T
        refine Ideal.mem_map_of_mem _ ((mem_maximalIdeal_iff_constantCoeff _).mpr ?_)
        rw [constantCoeff_C]
        exact map_nonunit (algebraMap A (AdicCompletion (maximalIdeal A) A)) a ha)
      (fun a => by
        change φh (lam ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a))
        rw [hlam, hφh, hφ, _root_.map_one, _root_.map_one, _root_.map_one, mul_one])
    intro c
    exact RingHom.congr_fun key c

  have hΨ : ∀ s : (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)), φh (θ s) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) s := by
    let Ψ₁ : (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)) →ₐ[(AdicCompletion (maximalIdeal A) A)] (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) :=
      { toRingHom := φh.comp θ.toRingHom
        commutes' := fun c => by
          have e1 : (φh.comp θ.toRingHom) (algebraMap (AdicCompletion (maximalIdeal A) A) (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)) c) = φh (θ (algebraMap (AdicCompletion (maximalIdeal A) A) (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)) c)) := rfl
          refine e1.trans ?_
          rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθC, hφlam,
            ← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
            RingHom.id_apply] }
    let Ψ₂ : (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)) →ₐ[(AdicCompletion (maximalIdeal A) A)] (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) := Ideal.Quotient.mkₐ (AdicCompletion (maximalIdeal A) A) _
    have hX : ∀ i, φh (θ (X i)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (X i) := by
      intro i
      rw [hθ, hxdef]
      change φh (ι (e₀.symm ((Ideal.Quotient.mk (Ideal.span {g₀})) (X i)))) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (X i)
      rw [hφι, RingEquiv.apply_symm_apply, tau_mk, map_X]
    have hΨ12 : Ψ₁ = Ψ₂ :=
      MvPowerSeries.algHom_ext_of_apply_X_mem J_T Ψ₁ Ψ₂
        (fun i => by
          change φh (θ (X i)) ∈ J_T
          rw [hX]
          refine Ideal.mem_map_of_mem _ ((mem_maximalIdeal_iff_constantCoeff _).mpr ?_)
          rw [constantCoeff_X]
          exact Ideal.zero_mem _)
        (fun i => hX i)
    intro s
    exact AlgHom.congr_fun hΨ12 s
  have hcomp1 : ∀ t, φh (θbar t) = t := by
    intro t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [hθbar, hΨ]

  have hθφ : ∀ z : (A ⊗[A₀] B₀), θbar (φ z) = (algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a b =>
        obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap B₀ (AdicCompletion 𝔪₀ B₀)) b))
        rw [hφ, _root_.map_mul, hθbar, hθC, hlam, ← hs, tau_mk, hθbar, hΘ, hs,
          RingEquiv.symm_apply_apply, hι, ← _root_.map_mul, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomp2 : ∀ z : (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)), θbar (φh z) = z := by
    have key := ringHom_ext_of_isHausdorff (RingHom.ker ev) h𝔪fg J (θbar.comp φh) (RingHom.id _)
      (fun d hd => by
        change θbar (φh ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) d)) ∈ J
        rw [hφh, hθφ]
        exact Ideal.mem_map_of_mem _ hd)
      (fun d hd => Ideal.mem_map_of_mem _ hd)
      (fun d => by
        change θbar (φh ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) d)) = (algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) d
        rw [hφh, hθφ])
    intro z
    exact RingHom.congr_fun key z

  let e : (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀)) ≃+* (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.map ψ g₀}) := RingEquiv.ofRingHom φh θbar (RingHom.ext hcomp1) (RingHom.ext hcomp2)
  refine ⟨h𝔪max, e, fun a => ?_, fun b s hs => ?_⟩
  · change φh ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) (algebraMap A (A ⊗[A₀] B₀) a)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (C ((algebraMap A (AdicCompletion (maximalIdeal A) A)) a))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hφh, hφ,
      _root_.map_one, _root_.map_one, _root_.map_one, mul_one]
  · change φh ((algebraMap (A ⊗[A₀] B₀) (AdicCompletion (RingHom.ker ev) (A ⊗[A₀] B₀))) ((1 : A) ⊗ₜ[A₀] b)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ψ g₀})) (MvPowerSeries.map ψ s)
    rw [hφh, hφ, _root_.map_one, _root_.map_one, _root_.map_one, one_mul, hs, tau_mk]

end Main

end StalkBC
p2m_reactivate "P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat.StalkBC"

open IsLocalRing TensorProduct MvPowerSeries in
theorem solution
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    [PerfectField (ResidueField A₀)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀] [Module.Flat A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀] [Algebra A₀ W₀]

    (hW₀ : maximalIdeal W₀ = (maximalIdeal A₀).map (algebraMap A₀ W₀))
    (g₀ : MvPowerSeries (Fin 2) W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀})
    (he₀ : ∀ a : A₀, e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) (algebraMap A₀ B₀ a)) =
      Ideal.Quotient.mk (Ideal.span {g₀}) (C (algebraMap A₀ W₀ a)))
    (ψ : W₀ →+* AdicCompletion (maximalIdeal A) A)
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ W₀ a) = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap A₀ A a))
    (χ : B₀ →+* ResidueField A)
    (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a))
    (hχ : ∀ (b : B₀) (w : W₀),
      e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
          (Ideal.Quotient.mk (Ideal.span {g₀})) →
      ∃ a : A, IsLocalRing.residue A a = χ b ∧
        ψ w - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
          (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    let Â := AdicCompletion (maximalIdeal A) A
    let B := A ⊗[A₀] B₀
    let ev : B →+* ResidueField A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
        ({ toRingHom := χ, commutes' := fun a => by
            rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]; exact hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
        (fun _ _ => Commute.all _ _)).toRingHom
    let 𝔪 : Ideal B := RingHom.ker ev
    ∃ (_ : 𝔪.IsMaximal)
      (e : AdicCompletion 𝔪 B ≃+* MvPowerSeries (Fin 2) Â ⧸ Ideal.span {MvPowerSeries.map ψ g₀}),
      (∀ a : A, e (algebraMap B (AdicCompletion 𝔪 B) (algebraMap A B a)) =
        Ideal.Quotient.mk _ (C (algebraMap A Â a))) ∧
      (∀ (b : B₀) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) = Ideal.Quotient.mk (Ideal.span {g₀}) s →
        e (algebraMap B (AdicCompletion 𝔪 B) ((1 : A) ⊗ₜ[A₀] b)) =
          Ideal.Quotient.mk _ (MvPowerSeries.map ψ s)) := by
  intro Â B ev 𝔪
  exact StalkBC.main A₀ A B₀ 𝔪₀ W₀ hW₀ g₀ e₀ he₀ ψ hψ χ hχ ev (fun _ _ => rfl)

end S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
end P2MW
export P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat (solution)
