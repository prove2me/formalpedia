-- Prove2me | solution 1 for ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a018ed04-42e7-5ff1-b092-05b4767e9abd

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
import Theorems.Thm_ArtinL_Abelian_natCeil_swanConductor_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.ramificationGroup_zero Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq Abelian.natCeil_swanConductor_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "inertiaGroup ramificationGroup ramificationGroup_zero IsUnramifiedAt swanConductor conductorExponent conductor exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq natCeil_swanConductor_eq"
namespace CondLocal
p2m_open "ArtinL.Abelian ArtinL"

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

local notation "G" => (L ≃ₐ[K] L)

theorem sum_one_sub_apply_eq (ψ : G →* ℂˣ) (H : Subgroup G) [Fintype ↥H] [Decidable (∀ σ ∈ H, ψ σ = 1)] :
    ∑ t : ↥H, (1 - ((ψ (t : G) : ℂˣ) : ℂ)) =
      ((Nat.card ↥H * (if ∀ σ ∈ H, ψ σ = 1 then 0 else 1) : ℕ) : ℂ) := by
  classical
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  let f : ↥H →* ℂ := (Units.coeHom ℂ).comp (ψ.comp H.subtype)
  have hsum : ∑ t : ↥H, ((ψ (t : G) : ℂˣ) : ℂ) = ∑ t : ↥H, f t := rfl
  have hiff : f = 1 ↔ ∀ σ ∈ H, ψ σ = 1 := by
    constructor
    · intro h σ hσ
      have h1 : f ⟨σ, hσ⟩ = 1 := by rw [h]; rfl
      exact Units.ext h1
    · intro h
      ext ⟨σ, hσ⟩
      show ((ψ σ : ℂˣ) : ℂ) = 1
      rw [h σ hσ, Units.val_one]
  rw [hsum, sum_hom_units f]
  by_cases h : ∀ σ ∈ H, ψ σ = 1
  · rw [if_pos (hiff.mpr h), if_pos h, Nat.card_eq_fintype_card]; push_cast; ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, Nat.card_eq_fintype_card]; push_cast; ring

theorem exists_forall_inertia_pow_eq_bot (Q : Ideal (𝓞 L)) [Q.IsMaximal] :
    ∃ N : ℕ, ∀ j, N ≤ j → (Q ^ (j + 1)).inertia G = ⊥ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hQ : Q ≠ ⊤ := Ideal.IsPrime.ne_top'
  have h1 : ∀ σ : G, σ ≠ 1 → ∃ n : ℕ, ∀ j, n ≤ j → σ ∉ (Q ^ (j + 1)).inertia G := by
    intro σ hσ
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 L, σ • x ≠ x := by
      by_contra h
      push Not at h
      apply hσ
      apply AlgEquiv.ext
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
      have ha := congrArg (algebraMap (𝓞 L) L) (h a)
      have hb' := congrArg (algebraMap (𝓞 L) L) (h b)
      rw [map_div₀, show σ (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a from ha,
        show σ (algebraMap (𝓞 L) L b) = algebraMap (𝓞 L) L b from hb']
      rfl
    have hne : σ • x - x ≠ 0 := sub_ne_zero.mpr hx
    have : σ • x - x ∉ ⨅ n : ℕ, Q ^ n := by
      rw [Ideal.iInf_pow_eq_bot_of_isDomain Q hQ]; exact hne
    rw [Submodule.mem_iInf] at this
    push Not at this
    obtain ⟨n, hn⟩ := this
    refine ⟨n, fun j hj hmem => hn ?_⟩
    exact Ideal.pow_le_pow_right (by omega) (hmem x)
  choose! n hn using h1
  refine ⟨Finset.univ.sup n, fun j hj => (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ => ?_⟩
  by_contra hσ1
  exact hn σ hσ1 j ((Finset.le_sup (Finset.mem_univ σ)).trans hj) hσ

omit [IsGalois K L] in
theorem inertia_pow_le_inertia (Q : Ideal (𝓞 L)) (j : ℕ) : (Q ^ (j + 1)).inertia G ≤ Q.inertia G := by
  intro σ hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero j) (hσ x)

end ArtinL.Abelian.CondLocal

open ArtinL.Abelian.CondLocal in
open scoped Classical in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Q.under (𝓞 K) = w.asIdeal) :
    ∑ᶠ j : ℕ, ∑ t : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), (1 - ((ψ (t : L ≃ₐ[K] L) : ℂˣ) : ℂ)) =
      ((w.asIdeal.ramificationIdx' Q * ArtinL.Abelian.conductorExponent ψ w : ℕ) : ℂ) := by
  haveI := w.isMaximal
  haveI hQl : Q.LiesOver w.asIdeal := ⟨hQ.symm⟩

  have he : w.asIdeal.ramificationIdx' Q = Nat.card ↥(Q.inertia (L ≃ₐ[K] L)) := by
    letI := Ideal.Quotient.field w.asIdeal
    letI := Ideal.Quotient.field Q
    haveI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
    haveI : PerfectField (𝓞 K ⧸ w.asIdeal) := inferInstance
    haveI : Algebra.IsSeparable (𝓞 K ⧸ w.asIdeal) (𝓞 L ⧸ Q) := Algebra.IsAlgebraic.isSeparable_of_perfectField
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal Q (L ≃ₐ[K] L),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) w.asIdeal Q]

  obtain ⟨τ, -, hτ⟩ := ArtinL.Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq K L w Q hQ
  have hcard : ∀ i : ℕ, Nat.card ↥((Q ^ (i + 1)).inertia (L ≃ₐ[K] L)) = Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w i) :=
    fun i => (hτ i).2.1
  have htriv : ∀ i : ℕ, (∀ σ ∈ (Q ^ (i + 1)).inertia (L ≃ₐ[K] L), ψ σ = 1) ↔ ∀ σ ∈ ArtinL.Abelian.ramificationGroup K L w i, ψ σ = 1 :=
    fun i => (hτ i).2.2 ψ

  let ind : ℕ → ℕ := fun i => if ∀ σ ∈ ArtinL.Abelian.ramificationGroup K L w i, ψ σ = 1 then 0 else 1

  obtain ⟨N, hN⟩ := exists_forall_inertia_pow_eq_bot (K := K) (L := L) Q
  have hcard0 : ∀ j, N ≤ j → Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w j) = 1 := fun j hj => by
    rw [← hcard j, hN j hj, Subgroup.card_bot]
  have hind0 : ∀ j, N ≤ j → ind j = 0 := fun j hj => by
    simp only [ind]
    rw [if_pos]
    rw [← htriv j, hN j hj]
    intro σ hσ; rw [Subgroup.mem_bot] at hσ; rw [hσ, map_one]

  have hLHS : ∑ᶠ j : ℕ, ∑ t : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), (1 - ((ψ (t : L ≃ₐ[K] L) : ℂˣ) : ℂ)) =
      ((∑ j ∈ Finset.range N, Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w j) * ind j : ℕ) : ℂ) := by
    have hterm : ∀ j : ℕ, ∑ t : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), (1 - ((ψ (t : L ≃ₐ[K] L) : ℂˣ) : ℂ)) =
        ((Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w j) * ind j : ℕ) : ℂ) := fun j => by
      rw [sum_one_sub_apply_eq ψ ((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), hcard j]
      simp only [ind, htriv j]
    simp_rw [hterm]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
    · push_cast; rfl
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      push Not at hlt
      apply hj
      rw [hind0 j hlt, mul_zero, Nat.cast_zero]
  rw [hLHS]
  congr 1

  have hG0 : ArtinL.Abelian.ramificationGroup K L w 0 = ArtinL.Abelian.inertiaGroup K L w := ArtinL.Abelian.ramificationGroup_zero w
  have he' : w.asIdeal.ramificationIdx' Q = Nat.card ↥(ArtinL.Abelian.inertiaGroup K L w) := by
    have h0 := hcard 0
    rw [zero_add, pow_one] at h0
    rw [he, h0, hG0]
  have hNpos : ∀ M, N ≤ M → ∑ j ∈ Finset.range M, Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w j) * ind j =
      ∑ j ∈ Finset.range N, Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w j) * ind j := by
    intro M hM
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [Finset.sum_range_add, add_eq_left]
    exact Finset.sum_eq_zero fun i _ => by rw [hind0 (N + i) (by omega), mul_zero]

  have hle : ∀ j, ArtinL.Abelian.ramificationGroup K L w j ≤ ArtinL.Abelian.inertiaGroup K L w := fun j => by
    rw [← hG0]
    exact inertia_pow_le_inertia (K := K) (L := L) (LanglandsTunnell.P2.Artin.primeAbove K L w) j |>.trans (by
      show (LanglandsTunnell.P2.Artin.primeAbove K L w ^ (0 + 1)).inertia (L ≃ₐ[K] L) ≥ (LanglandsTunnell.P2.Artin.primeAbove K L w).inertia (L ≃ₐ[K] L)
      rw [zero_add, pow_one])
  symm
  by_cases hram : ArtinL.Abelian.IsUnramifiedAt ψ w
  ·
    have hind : ∀ j, ind j = 0 := fun j => by
      simp only [ind]; rw [if_pos]
      exact fun σ hσ => hram σ (hle j hσ)
    have hsw : ArtinL.Abelian.swanConductor ψ w = 0 := by
      unfold ArtinL.Abelian.swanConductor
      refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
      rw [if_pos (fun σ hσ => hram σ (hle (i + 1) hσ)), mul_zero]
    rw [Finset.sum_eq_zero (fun j _ => by rw [hind j, mul_zero])]
    unfold ArtinL.Abelian.conductorExponent
    rw [if_pos hram, hsw, Nat.ceil_zero, add_zero, mul_zero]
  ·
    have hind0' : ind 0 = 1 := by
      simp only [ind]; rw [if_neg]; rwa [hG0]
    have hceil := ArtinL.Abelian.natCeil_swanConductor_eq K L ψ w hram
    have hsw_sum : ArtinL.Abelian.swanConductor ψ w = ∑ i ∈ Finset.range N,
        ((Nat.card ↥(ArtinL.Abelian.ramificationGroup K L w (i + 1)) : ℚ) / (Nat.card ↥(ArtinL.Abelian.inertiaGroup K L w) : ℚ) *
          (if ∀ σ ∈ ArtinL.Abelian.ramificationGroup K L w (i + 1), ψ σ = 1 then 0 else 1)) := by
      unfold ArtinL.Abelian.swanConductor
      apply finsum_eq_sum_of_support_subset
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      push Not at hlt
      apply hi
      have h0 := hind0 (i + 1) (by omega)
      by_cases hc : ∀ σ ∈ ArtinL.Abelian.ramificationGroup K L w (i + 1), ψ σ = 1
      · rw [if_pos hc, mul_zero]
      · exfalso
        simp only [ind, if_neg hc] at h0
        exact one_ne_zero h0

    rw [← hNpos (N + 1) (by omega), Finset.sum_range_succ', hind0', mul_one, hG0, ← he']
    apply Nat.cast_injective (R := ℚ)
    unfold ArtinL.Abelian.conductorExponent
    rw [if_neg hram]
    push_cast
    rw [hceil, hsw_sum, mul_add, mul_one, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have he0 : (Nat.card ↥(ArtinL.Abelian.inertiaGroup K L w) : ℚ) ≠ 0 := by
      have : 0 < Nat.card ↥(ArtinL.Abelian.inertiaGroup K L w) := Nat.card_pos
      exact_mod_cast this.ne'
    rw [he']
    simp only [ind]
    split_ifs <;> push_cast <;> field_simp

end S_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
end P2MW
export P2MW.S_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent (solution)
