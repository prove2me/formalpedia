-- Prove2me | solution 1 for Algebra.exists_presentation_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/98423d7b-da6d-58fa-bba0-54e44b18c732

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Basic
import Theorems.Thm_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Theorems.Thm_MvPowerSeries_algHom_surjective_of_apply_X_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_presentation_of_residueField

universe u v w x

open IsLocalRing

namespace FrobDictREDK

section FiniteOverLocal

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  [Module.Finite 𝒪 T]

theorem eq_top_of_sup_smul_top (N : Submodule 𝒪 T)
    (h : (⊤ : Submodule 𝒪 T) ≤ N ⊔ (maximalIdeal 𝒪) • ⊤) : N = ⊤ :=
  top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (maximalIdeal_le_jacobson _) h)

theorem isUnit_one_sub_of_mem_map (m : T) (hm : m ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :
    IsUnit (1 - m) := by

  let N : Submodule 𝒪 T := LinearMap.range (LinearMap.mulLeft 𝒪 (1 - m))
  have hN : N = ⊤ := by
    refine eq_top_of_sup_smul_top N fun t _ => ?_
    have ht : t = (1 - m) * t + m * t := by ring
    rw [ht]
    refine Submodule.add_mem_sup ⟨t, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨v, hv⟩ : (1 : T) ∈ N := by rw [hN]; trivial
  exact IsUnit.of_mul_eq_one v hv

theorem isLocalRing_of_quotient [Nontrivial T]
    [IsLocalRing (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T))] : IsLocalRing T := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  set J := (maximalIdeal 𝒪).map (algebraMap 𝒪 T)
  have key : ∀ b : T, IsUnit (Ideal.Quotient.mk J b) → IsUnit b := by
    intro b hb
    obtain ⟨c, hc⟩ := hb.exists_right_inv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq] at hc
    have hu : IsUnit (1 - (1 - b * c)) := isUnit_one_sub_of_mem_map _ (by
      have := J.neg_mem hc; rwa [neg_sub] at this)
    rw [sub_sub_cancel] at hu
    exact isUnit_of_mul_isUnit_left hu
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk J a) with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key (1 - a) (by simpa using h))

theorem map_maximalIdeal_le [IsLocalRing T] :
    (maximalIdeal 𝒪).map (algebraMap 𝒪 T) ≤ maximalIdeal T := by
  intro m hm
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h := isUnit_one_sub_of_mem_map ((↑u⁻¹ : T) * ↑u) (Ideal.mul_mem_left _ _ hm)
  rw [Units.inv_mul, sub_self] at h
  exact not_isUnit_zero h

scoped instance isLocalHom_algebraMap [IsLocalRing T] : IsLocalHom (algebraMap 𝒪 T) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : algebraMap 𝒪 T a ∈ maximalIdeal T :=
    map_maximalIdeal_le (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hna))
  exact (mem_maximalIdeal _).mp hmem ha

end FiniteOverLocal

end FrobDictREDK
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

namespace FrobDictREDK

open MvPowerSeries

section Main

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

local notation "k" => IsLocalRing.ResidueField 𝒪
local notation "𝔪" => IsLocalRing.maximalIdeal 𝒪

noncomputable def red (n : ℕ) : MvPowerSeries (Fin n) 𝒪 →ₐ[𝒪] MvPowerSeries (Fin n) k :=
  MvPowerSeries.mapAlgHom (σ := Fin n) (Algebra.ofId 𝒪 k)

omit [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem red_apply (n : ℕ) (p : MvPowerSeries (Fin n) 𝒪) :
    red n p = MvPowerSeries.map (IsLocalRing.residue 𝒪) p := rfl

omit [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem coeff_red (n : ℕ) (p : MvPowerSeries (Fin n) 𝒪) (m : Fin n →₀ ℕ) :
    MvPowerSeries.coeff m (red n p) = IsLocalRing.residue 𝒪 (MvPowerSeries.coeff m p) := by
  rw [red_apply, MvPowerSeries.coeff_map]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem red_X (n : ℕ) (i : Fin n) : red (𝒪 := 𝒪) n (MvPowerSeries.X i) = MvPowerSeries.X i := by
  rw [red_apply, MvPowerSeries.map_X]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem red_surjective (n : ℕ) : Function.Surjective (red (𝒪 := 𝒪) n) := by
  intro q
  refine ⟨fun m => (IsLocalRing.residue_surjective (q m)).choose, ?_⟩
  ext m
  rw [coeff_red]
  exact (IsLocalRing.residue_surjective (q m)).choose_spec

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem mem_ker_red_iff (n : ℕ) (p : MvPowerSeries (Fin n) 𝒪) :
    red n p = 0 ↔ p ∈ (𝔪).map (MvPowerSeries.C (σ := Fin n) (R := 𝒪)) := by
  constructor
  · intro hp
    have hcoef : ∀ m, MvPowerSeries.coeff m p ∈ 𝔪 := fun m => by
      rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_red, hp, map_zero]
    obtain ⟨r, μ, hμ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian 𝔪)
    have hc : ∀ m, ∃ c : Fin r → 𝒪, ∑ l, c l * μ l = MvPowerSeries.coeff m p := fun m => by
      have hm : MvPowerSeries.coeff m p ∈ Submodule.span 𝒪 (Set.range μ) := by rw [hμ]; exact hcoef m
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪).mp hm
      exact ⟨c, by simpa [smul_eq_mul] using hc⟩
    choose c hc using hc
    let q : Fin r → MvPowerSeries (Fin n) 𝒪 := fun l m => c m l
    have hq : ∀ l m, MvPowerSeries.coeff m (q l) = c m l := fun l m => rfl
    have hp_eq : p = ∑ l, MvPowerSeries.C (μ l) * q l := by
      ext m
      rw [map_sum, ← hc m]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [MvPowerSeries.coeff_C_mul, mul_comm, hq]
    rw [hp_eq]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← hμ]; exact Submodule.subset_span ⟨l, rfl⟩
  · intro hp
    refine Submodule.span_induction (p := fun q _ => red n q = 0) ?_ (map_zero _) (fun a b _ _ ha hb => by
      show red n (a + b) = 0
      rw [map_add, ha, hb, add_zero]) (fun a b _ hb => by
      show red n (a • b) = 0
      rw [smul_eq_mul, map_mul, hb, mul_zero]) hp
    rintro _ ⟨a, ha, rfl⟩
    rw [red_apply, MvPowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem sub_C_constantCoeff_mem_span_X {R : Type v} [CommRing R] (n : ℕ) (p : MvPowerSeries (Fin n) R) :
    p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) := by
  have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p))
    (fun m hm => by
      have hm0 : m = 0 := by
        have : m.degree = 0 := by omega
        exact (Finsupp.degree_eq_zero_iff m).mp this
      subst hm0
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  rwa [pow_one] at h

end Main
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

end FrobDictREDK
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

namespace FrobDictREDK

open MvPowerSeries

section Main2

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

local notation "k" => IsLocalRing.ResidueField 𝒪
local notation "𝔪" => IsLocalRing.maximalIdeal 𝒪

theorem main {n : ℕ} (g : Fin n → MvPowerSeries (Fin n) k)
    (e : (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)) ≃ₐ[𝒪]
      (T ⧸ (𝔪).map (algebraMap 𝒪 T)))
    [Nontrivial (T ⧸ (𝔪).map (algebraMap 𝒪 T))] :
    ∃ f : Fin n → MvPowerSeries (Fin n) 𝒪,
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  classical

  set 𝔪T : Ideal T := (𝔪).map (algebraMap 𝒪 T) with h𝔪T
  set J : Ideal (MvPowerSeries (Fin n) k) := Ideal.span (Set.range g) with hJ
  let qT : T →ₐ[𝒪] T ⧸ 𝔪T := Ideal.Quotient.mkₐ 𝒪 𝔪T
  let qJ : MvPowerSeries (Fin n) k →ₐ[𝒪] MvPowerSeries (Fin n) k ⧸ J := Ideal.Quotient.mkₐ 𝒪 J

  haveI : Nontrivial (MvPowerSeries (Fin n) k ⧸ J) := e.surjective.nontrivial
  haveI : IsLocalRing (MvPowerSeries (Fin n) k ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (T ⧸ 𝔪T) := IsLocalRing.of_surjective' e.toRingEquiv.toRingHom e.surjective
  haveI : Nontrivial T := (Ideal.Quotient.mk_surjective (I := 𝔪T)).nontrivial
  haveI : IsLocalRing T := isLocalRing_of_quotient (𝒪 := 𝒪)
  haveI : IsNoetherianRing T := IsNoetherianRing.of_finite 𝒪 T
  haveI hlocqT : IsLocalHom (Ideal.Quotient.mk 𝔪T) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI hlocqJ : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let tb : Fin n → T ⧸ 𝔪T := fun i => e (Ideal.Quotient.mk J (MvPowerSeries.X i))
  have htb_nu : ∀ i, ¬ IsUnit (tb i) := fun i hu => by
    have hu' : IsUnit (Ideal.Quotient.mk J (MvPowerSeries.X i : MvPowerSeries (Fin n) k)) := by
      have := hu.map e.symm
      simpa [tb] using this
    have hX : ¬ IsUnit (MvPowerSeries.X i : MvPowerSeries (Fin n) k) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]; exact not_isUnit_zero
    exact hX ((isUnit_map_iff (Ideal.Quotient.mk J) _).mp hu')
  choose t ht using fun i => Ideal.Quotient.mk_surjective (I := 𝔪T) (tb i)
  have ht_mem : ∀ i, t i ∈ maximalIdeal T := fun i => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact htb_nu i (ht i ▸ hu.map (Ideal.Quotient.mk 𝔪T))

  haveI : IsAdicComplete (maximalIdeal T) T := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪) (T := T)
  obtain ⟨ψ, hψ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin n) (𝒪 := 𝒪) (maximalIdeal T) t ht_mem

  have hθC : ∀ c : 𝒪, e (Ideal.Quotient.mk J (MvPowerSeries.C (IsLocalRing.residue 𝒪 c))) =
      Ideal.Quotient.mk 𝔪T (algebraMap 𝒪 T c) := fun c => by
    have h1 : MvPowerSeries.C (IsLocalRing.residue 𝒪 c) = algebraMap 𝒪 (MvPowerSeries (Fin n) k) c := by
      rw [MvPowerSeries.algebraMap_apply, IsLocalRing.ResidueField.algebraMap_eq]
    rw [h1, ← Ideal.Quotient.mkₐ_eq_mk 𝒪, ← Ideal.Quotient.mkₐ_eq_mk 𝒪, AlgHom.commutes, AlgEquiv.commutes,
      AlgHom.commutes]

  have h𝒪 : Function.Surjective
      (⇑(Ideal.Quotient.mk (Ideal.span (Set.range t))) ∘ ⇑(algebraMap 𝒪 T)) := by
    let It : Ideal T := Ideal.span (Set.range t)

    let N : Submodule 𝒪 (T ⧸ It) := Submodule.span 𝒪 {1}
    have hN : N = ⊤ := by
      refine eq_top_of_sup_smul_top N ?_
      rintro q -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q

      obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk 𝔪T s))
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (MvPowerSeries.constantCoeff p)
      have hp' := sub_C_constantCoeff_mem_span_X n p

      have hθX : (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k))).map
          ((e : _ ≃ₐ[𝒪] _).toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)) =
            It.map (Ideal.Quotient.mk 𝔪T) := by
        rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
        congr 2
        funext i
        simp only [Function.comp_apply, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          AlgEquiv.coe_ringEquiv]
        exact (ht i).symm
      have hmem : (e : _ ≃ₐ[𝒪] _).toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)
          (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) ∈ It.map (Ideal.Quotient.mk 𝔪T) := by
        rw [← hθX]; exact Ideal.mem_map_of_mem _ hp'
      obtain ⟨w, hw, hw'⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk 𝔪T)
        Ideal.Quotient.mk_surjective).mp hmem

      have hθp : ((e : _ ≃ₐ[𝒪] _).toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)) p =
          Ideal.Quotient.mk 𝔪T s := by
        simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
          Function.comp_apply, hp, AlgEquiv.apply_symm_apply]
      have hθc : ((e : _ ≃ₐ[𝒪] _).toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J))
          (MvPowerSeries.C (MvPowerSeries.constantCoeff p)) = Ideal.Quotient.mk 𝔪T (algebraMap 𝒪 T c) := by
        simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
          Function.comp_apply, ← hc, hθC]
      have hdiff : s - algebraMap 𝒪 T c - w ∈ 𝔪T := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, hw', map_sub, hθp, hθc, sub_self]

      have hs : s = algebraMap 𝒪 T c + w + (s - algebraMap 𝒪 T c - w) := by ring
      rw [hs, map_add, map_add]
      refine Submodule.add_mem_sup (N.add_mem ?_ ?_) ?_
      · exact Submodule.mem_span_singleton.mpr ⟨c, by rw [Algebra.smul_def, mul_one, Ideal.Quotient.mk_algebraMap]⟩
      · rw [Ideal.Quotient.eq_zero_iff_mem.mpr hw]; exact N.zero_mem
      · rw [Ideal.smul_top_eq_map]
        have : (𝔪T).map (Ideal.Quotient.mk It) ≤ (𝔪).map (algebraMap 𝒪 (T ⧸ It)) := by
          rw [h𝔪T, Ideal.map_map]; rfl
        exact this (Ideal.mem_map_of_mem _ hdiff)
    intro q
    have hq : q ∈ N := by rw [hN]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hq
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]; rfl⟩
  have hψsurj : Function.Surjective ψ := MvPowerSeries.algHom_surjective_of_apply_X_eq ψ t hψ ht_mem h𝒪

  haveI : IsNoetherianRing (T ⧸ 𝔪T) :=
    isNoetherianRing_of_surjective T _ (Ideal.Quotient.mk 𝔪T) Ideal.Quotient.mk_surjective
  have hagree : qT.comp ψ = (e : _ →ₐ[𝒪] _).comp (qJ.comp (red n)) := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (T ⧸ 𝔪T)) _ _ (fun i => ?_) (fun i => ?_)
    · change Ideal.Quotient.mk 𝔪T (ψ (MvPowerSeries.X i)) ∈ _
      rw [hψ]
      exact map_nonunit _ _ (ht_mem i)
    · change Ideal.Quotient.mk 𝔪T (ψ (MvPowerSeries.X i)) = e (Ideal.Quotient.mk J (red n (MvPowerSeries.X i)))
      rw [hψ, ht, red_X]
  have hagree' : ∀ p, Ideal.Quotient.mk 𝔪T (ψ p) = e (Ideal.Quotient.mk J (red n p)) := fun p =>
    congr($hagree p)

  choose G hG using fun i => red_surjective (𝒪 := 𝒪) n (g i)
  obtain ⟨s, b, hb⟩ := Module.Finite.exists_fin (R := 𝒪) (M := T)
  choose h hh using fun j => hψsurj (b j)
  have hGmem : ∀ i, ψ (G i) ∈ (𝔪) • Submodule.span 𝒪 (Set.range b) := fun i => by
    rw [hb, Ideal.smul_top_eq_map]
    change ψ (G i) ∈ 𝔪T
    rw [← Ideal.Quotient.eq_zero_iff_mem, hagree', hG,
      Ideal.Quotient.eq_zero_iff_mem.mpr (show g i ∈ J from Ideal.subset_span ⟨i, rfl⟩), map_zero]
  choose a ha ha' using fun i => (Submodule.mem_ideal_smul_span_iff_exists_sum (𝔪) b (ψ (G i))).mp (hGmem i)
  have hCalg : ∀ c : 𝒪, (MvPowerSeries.C c : MvPowerSeries (Fin n) 𝒪) = algebraMap 𝒪 _ c := fun c => by
    rw [MvPowerSeries.algebraMap_apply]; rfl
  have hψC : ∀ c : 𝒪, ψ (MvPowerSeries.C c) = algebraMap 𝒪 T c := fun c => by rw [hCalg, AlgHom.commutes]
  let F : Fin n → MvPowerSeries (Fin n) 𝒪 := fun i =>
    G i - (a i).sum fun j c => MvPowerSeries.C c * h j
  have hFker : ∀ i, ψ (F i) = 0 := fun i => by
    simp only [F, map_sub, map_finsuppSum, map_mul, hψC, hh]
    rw [sub_eq_zero, ← ha' i]
    exact Finsupp.sum_congr fun j _ => by rw [Algebra.smul_def]
  have hFred : ∀ i, red n (F i) = g i := fun i => by
    simp only [F, map_sub, map_finsuppSum, map_mul, hG, sub_eq_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    show red n (MvPowerSeries.C (a i j)) * red n (h j) = 0
    rw [red_apply n (MvPowerSeries.C _), MvPowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr (ha i j),
      map_zero, zero_mul]

  let IF : Ideal (MvPowerSeries (Fin n) 𝒪) := Ideal.span (Set.range F)
  have hIFker : ∀ q ∈ IF, ψ q = 0 := fun q hq => by
    refine Submodule.span_induction (p := fun q _ => ψ q = 0) ?_ (map_zero _)
      (fun a b _ _ ha hb => by show ψ (a + b) = 0; rw [map_add, ha, hb, add_zero])
      (fun a b _ hb => by show ψ (a • b) = 0; rw [smul_eq_mul, map_mul, hb, mul_zero]) hq
    rintro _ ⟨i, rfl⟩; exact hFker i
  let ψ' : (MvPowerSeries (Fin n) 𝒪 ⧸ IF) →ₐ[𝒪] T := Ideal.Quotient.liftₐ IF ψ hIFker
  have hψ'mk : ∀ q, ψ' (Ideal.Quotient.mk IF q) = ψ q := fun q => rfl
  have hψ'surj : Function.Surjective ψ' := fun y => by
    obtain ⟨q, rfl⟩ := hψsurj y
    exact ⟨Ideal.Quotient.mk IF q, rfl⟩

  haveI : IsNoetherianRing (MvPowerSeries (Fin n) 𝒪) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsNoetherianRing (MvPowerSeries (Fin n) 𝒪 ⧸ IF) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk IF) Ideal.Quotient.mk_surjective
  haveI : Nontrivial (MvPowerSeries (Fin n) 𝒪 ⧸ IF) := by
    refine Ideal.Quotient.nontrivial_iff.mpr fun hIF => ?_
    have h1 : ψ 1 = 0 := hIFker 1 (hIF ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : IsLocalRing (MvPowerSeries (Fin n) 𝒪 ⧸ IF) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IF) Ideal.Quotient.mk_surjective
  haveI hlocIF : IsLocalHom (Ideal.Quotient.mk IF) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ IF)) := by
    refine ⟨fun c hc => ?_⟩
    rw [show algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ IF) c = Ideal.Quotient.mk IF (MvPowerSeries.C c) by
      rw [hCalg, Ideal.Quotient.mk_algebraMap]] at hc
    have hc' := (isUnit_map_iff (Ideal.Quotient.mk IF) _).mp hc
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at hc'
    exact hc'

  have hker : RingHom.ker ψ' ≤ (𝔪).map (algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ IF)) := by
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hp0 : ψ p = 0 := by rwa [RingHom.mem_ker, hψ'mk] at hq

    have hredp : red n p ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply e.injective
      rw [← hagree', hp0, map_zero, map_zero]
    have hJred : J = IF.map (red n) := by
      rw [hJ, Ideal.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact (hFred i).symm
    rw [hJred] at hredp
    obtain ⟨q, hq, hqp⟩ := (Ideal.mem_map_iff_of_surjective (red n) (red_surjective n)).mp hredp
    have hpq : p - q ∈ (𝔪).map (MvPowerSeries.C (σ := Fin n) (R := 𝒪)) := by
      rw [← mem_ker_red_iff, map_sub, hqp, sub_self]
    have hsplit : Ideal.Quotient.mk IF p = Ideal.Quotient.mk IF (p - q) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
    rw [hsplit]
    have hmap : ((𝔪).map (MvPowerSeries.C (σ := Fin n) (R := 𝒪))).map (Ideal.Quotient.mk IF) =
        (𝔪).map (algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ IF)) := by
      rw [Ideal.map_map]
      congr 1
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hpq

  have hinj : Function.Injective ψ' :=
    AlgHom.injective_of_surjective_of_ker_le_map_maximalIdeal ψ' hψ'surj hker
  exact ⟨F, ⟨AlgEquiv.ofBijective ψ' ⟨hinj, hψ'surj⟩⟩⟩

end Main2
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

end FrobDictREDK
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

namespace FrobDictREDK

section Final

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

omit [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Module.Finite 𝒪 T]
  [Module.Free 𝒪 T] in

theorem trivial_case [Subsingleton T] :
    ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  refine ⟨1, fun _ => 1, ⟨?_⟩⟩
  have htop : Ideal.span (Set.range fun _ : Fin 1 => (1 : MvPowerSeries (Fin 1) 𝒪)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one
  haveI : Subsingleton (MvPowerSeries (Fin 1) 𝒪 ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
      (1 : MvPowerSeries (Fin 1) 𝒪))) := Ideal.Quotient.subsingleton_iff.mpr htop
  let φ : (MvPowerSeries (Fin 1) 𝒪 ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
      (1 : MvPowerSeries (Fin 1) 𝒪))) →ₐ[𝒪] T :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _ }
  exact AlgEquiv.ofBijective φ ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end Final
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

end FrobDictREDK
p2m_reactivate "P2MW.S_Algebra_exists_presentation_of_residueField.FrobDictREDK"

open FrobDictREDK in
theorem solution
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (hk : ∃ (n : ℕ) (g : Fin n → MvPowerSeries (Fin n) (IsLocalRing.ResidueField 𝒪)),
      Nonempty ((MvPowerSeries (Fin n) (IsLocalRing.ResidueField 𝒪) ⧸ Ideal.span (Set.range g)) ≃ₐ[𝒪]
        (T ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T)))) :
    ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  obtain ⟨n, g, ⟨e⟩⟩ := hk
  by_cases hT : Nontrivial (T ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T))
  · obtain ⟨f, hf⟩ := main g e
    exact ⟨n, f, hf⟩
  ·
    rw [not_nontrivial_iff_subsingleton, Ideal.Quotient.subsingleton_iff] at hT
    haveI : Subsingleton T := by
      have htop : (⊤ : Submodule 𝒪 T) ≤ (IsLocalRing.maximalIdeal 𝒪) • ⊤ := by
        rw [Ideal.smul_top_eq_map, hT]; exact le_rfl
      have hbot : (⊤ : Submodule 𝒪 T) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top htop
          (IsLocalRing.maximalIdeal_le_jacobson _)
      exact subsingleton_of_forall_eq 0 fun y => (Submodule.mem_bot 𝒪).mp (hbot ▸ Submodule.mem_top)
    exact trivial_case

end S_Algebra_exists_presentation_of_residueField
end P2MW
export P2MW.S_Algebra_exists_presentation_of_residueField (solution)
