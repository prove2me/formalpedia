-- Prove2me | solution 1 for Algebra.card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/db03eb59-515b-5ad0-bb77-5a4734ab2576

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq

set_option maxHeartbeats 800000
set_option autoImplicit false
universe u

open IsLocalRing Polynomial

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

def IsPureSlope (r : ℕ) (n : W) (d : ℕ) (f : Polynomial W) : Prop :=
  f.Monic ∧ f.natDegree = d ∧
    (∀ i : ℕ, i ≤ d → ((d - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W n ≤
      (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff i)) ∧
    ((d : ℕ∞) * IsDiscreteValuationRing.addVal W n = (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff 0))

namespace HCprime

section Algebra

variable {R : Type*} [CommRing R] {O : Type*} [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]

theorem aeval_eq_zero_of_aeval_charpoly_mulLeft (a : O) (p : R[X]) (hp : aeval a p = 0)
    (L : Type*) [Field L] [Algebra R L] (x : L) (hx : aeval x (LinearMap.mulLeft R a).charpoly = 0) :
    aeval x p = 0 := by
  set T : Module.End R O := LinearMap.mulLeft R a with hTdef
  have hT : aeval T p = 0 := by
    have h1 : T = Algebra.lmul R O a := LinearMap.ext fun _ => rfl
    rw [h1, aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvalue (T.baseChange L) x := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange, IsRoot, eval_map,
      ← aeval_def, hx]
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  have h2 : aeval (T.baseChange L) (p.map (algebraMap R L)) = 0 := by
    rw [aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom R L O T) p = 0
    rw [aeval_algHom_apply, hT, map_zero]
  have h3 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap R L)) hy
  rw [h2, LinearMap.zero_apply, eval_map, ← aeval_def, eq_comm, smul_eq_zero] at h3
  exact h3.resolve_right hy.2

end Algebra

section Normed

theorem apply_multiset_sum_le_of_isNonarchimedean {α : Type*} [AddCommMonoid α] {g : α → ℝ}
    (hg : IsNonarchimedean g) {C : ℝ} (h0 : g 0 ≤ C) (s : Multiset α) (hs : ∀ x ∈ s, g x ≤ C) :
    g s.sum ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using h0
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (hg _ _).trans (max_le (hs a (Multiset.mem_cons_self a s))
      (ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)))

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem spectralMulAlgNorm_multiset_prod_eq_pow (s : Multiset L) {ρ : ℝ}
    (hρ : ∀ α ∈ s, spectralNorm K L α = ρ) : spectralMulAlgNorm K L s.prod = ρ ^ s.card := by
  rw [map_multiset_prod, Multiset.map_congr rfl (fun a ha => (spectralMulAlgNorm_def (K := K) a).trans (hρ a ha)),
    Multiset.map_const', Multiset.prod_replicate]

theorem norm_coeff_le_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots, spectralNorm K L α = ρ) (k : ℕ) (hk : k ≤ f.natDegree) :
    ‖f.coeff k‖ ≤ ρ ^ (f.natDegree - k) := by
  set fL := f.map (algebraMap K L) with hfLdef
  have hfL : fL.Monic := hf.map _
  have hdeg : fL.natDegree = f.natDegree := hf.natDegree_map _
  have hcard : fL.roots.card = fL.natDegree := splits_iff_card_roots.mp hs
  have hcoef := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
  rw [hfL.leadingCoeff, one_mul] at hcoef
  have e1 : ‖f.coeff k‖ = spectralMulAlgNorm K L (fL.coeff k) := by
    rw [coeff_map, spectralMulAlgNorm_def, spectralNorm_extends]
  rw [e1, hcoef, map_mul, map_pow, map_neg_eq_map, map_one, one_pow, one_mul, hdeg, Multiset.esymm]
  refine apply_multiset_sum_le_of_isNonarchimedean (g := spectralMulAlgNorm K L)
    (fun x y => isNonarchimedean_spectralNorm x y) (by rw [map_zero]; positivity) _ ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  rw [spectralMulAlgNorm_multiset_prod_eq_pow t (fun a ha => hρ a (Multiset.mem_of_le ht.1 ha)), ht.2]

theorem norm_coeff_zero_eq_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ}
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots, spectralNorm K L α = ρ) :
    ‖f.coeff 0‖ = ρ ^ f.natDegree := by
  set fL := f.map (algebraMap K L) with hfLdef
  have hfL : fL.Monic := hf.map _
  have hdeg : fL.natDegree = f.natDegree := hf.natDegree_map _
  have hcard : fL.roots.card = fL.natDegree := splits_iff_card_roots.mp hs
  have e1 : ‖f.coeff 0‖ = spectralMulAlgNorm K L (fL.coeff 0) := by
    rw [coeff_map, spectralMulAlgNorm_def, spectralNorm_extends]
  rw [e1, hs.coeff_zero_eq_prod_roots_of_monic hfL, map_mul, map_pow, map_neg_eq_map, map_one, one_pow,
    one_mul, spectralMulAlgNorm_multiset_prod_eq_pow _ hρ, hcard, hdeg]

theorem norm_coeff_pow_le_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots, spectralNorm K L α = ρ) (k : ℕ) :
    ‖f.coeff k‖ ^ f.natDegree ≤ ‖f.coeff 0‖ ^ (f.natDegree - k) := by
  by_cases hk : k ≤ f.natDegree
  · rw [norm_coeff_zero_eq_of_spectralNorm_roots_eq f hf hs hρ, ← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_coeff_le_of_spectralNorm_roots_eq f hf hs hρ0 hρ k hk) _
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, Nat.sub_eq_zero_of_le (by omega), pow_zero]
    exact pow_le_one₀ le_rfl zero_le_one

end Normed

section Bridge

variable (W)

@[reducible] noncomputable def adicValuedFrac : Valued (FractionRing W) (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal W).adicValued

attribute [local instance] adicValuedFrac

theorem v_apply (x : FractionRing W) :
    Valued.v x = (IsDiscreteValuationRing.maximalIdeal W).valuation (FractionRing W) x := rfl

@[reducible] noncomputable def rankOneFrac : (Valued.v : Valuation (FractionRing W) (WithZero (Multiplicative ℤ))).RankOne :=
  @Valuation.IsRankOneDiscrete.rankOne _ _ _ _ Valued.v
    (IsDiscreteValuationRing.isRankOneDiscrete W (FractionRing W)) 2 one_lt_two

attribute [local instance] rankOneFrac

open scoped Valued

noncomputable example : NontriviallyNormedField (FractionRing W) := inferInstance
example : IsUltrametricDist (FractionRing W) := inferInstance

theorem dvd_of_v_le {x y : W}
    (h : Valued.v (algebraMap W (FractionRing W) x) ≤ Valued.v (algebraMap W (FractionRing W) y)) : y ∣ x := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff,
      map_eq_zero_iff _ (IsFractionRing.injective W (FractionRing W))] at h
    rw [h]
  · have hy' : algebraMap W (FractionRing W) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr hy
    have hle : Valued.v (algebraMap W (FractionRing W) x / algebraMap W (FractionRing W) y) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one₀ ((Valuation.pos_iff _).mpr hy')).mpr h
    obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
    refine ⟨z, IsFractionRing.injective W (FractionRing W) ?_⟩
    rw [map_mul, hz, mul_div_cancel₀ _ hy']

theorem addVal_le_of_norm_le {x y : W}
    (h : ‖algebraMap W (FractionRing W) x‖ ≤ ‖algebraMap W (FractionRing W) y‖) :
    IsDiscreteValuationRing.addVal W y ≤ IsDiscreteValuationRing.addVal W x :=
  IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (dvd_of_v_le W (Valued.toNormedField.norm_le_iff.mp h))

theorem mem_pow_iff_v_le {ϖ : W} (hϖ : Irreducible ϖ) (z : W) (k : ℕ) :
    z ∈ maximalIdeal W ^ k ↔
      Valued.v (algebraMap W (FractionRing W) z) ≤ Valued.v (algebraMap W (FractionRing W) ϖ ^ k) := by
  rw [← map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    rw [map_mul, Valuation.map_mul]
    exact mul_le_of_le_one_right' ((IsDiscreteValuationRing.maximalIdeal W).valuation_le_one w)
  · exact dvd_of_v_le W

theorem exists_pow_lt_withZero {q γ : WithZero (Multiplicative ℤ)} (hq0 : q ≠ 0) (hq : q < 1) (hγ : γ ≠ 0) :
    ∃ k : ℕ, q ^ k < γ := by
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, q = WithZero.exp a := ⟨q.log, (WithZero.exp_log hq0).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = WithZero.exp b := ⟨γ.log, (WithZero.exp_log hγ).symm⟩
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hq
  refine ⟨b.natAbs + 1, ?_⟩
  rw [← WithZero.exp_nsmul, WithZero.exp_lt_exp, nsmul_eq_mul]
  push_cast
  have ha : a ≤ -1 := by omega
  have h1 : (|b| + 1) * a ≤ (|b| + 1) * (-1) := mul_le_mul_of_nonneg_left ha (by positivity)
  linarith [neg_abs_le b]

set_option backward.isDefEq.respectTransparency false in
open Filter Topology in

theorem completeSpace_fractionRing [IsAdicComplete (maximalIdeal W) W] : CompleteSpace (FractionRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  set π : FractionRing W := algebraMap W (FractionRing W) ϖ with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr hϖ.ne_zero
  have hvπ0 : ∀ k : ℕ, Valued.v (π ^ k) ≠ 0 := fun k => by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hπ0
  have hvπ1 : Valued.v π < 1 := by
    rw [v_apply, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hϖ.not_isUnit
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  rw [(Valued.hasBasis_uniformity (FractionRing W) (WithZero (Multiplicative ℤ))).cauchySeq_iff] at hu
  have hu' : ∀ k : ℕ, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → Valued.v (u n - u m) < Valued.v (π ^ k) := by
    intro k
    obtain ⟨N, hN⟩ := hu (Units.mk0 (Valued.v.restrict (π ^ k))
      (mt (Valuation.restrict_eq_zero_iff _).mp (hvπ0 k))) trivial
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    simp only [Set.mem_setOf_eq, Units.val_mk0] at h
    rwa [Valuation.restrict_lt_iff] at h
  choose N hN using hu'
  let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N
  have hMN : ∀ {j k : ℕ}, j ≤ k → N j ≤ M k := fun {j k} h =>
    Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  have hlift : ∀ k, ∃ y : W, algebraMap W (FractionRing W) y = u (M k) - u (M 0) := by
    intro k
    apply IsDiscreteValuationRing.exists_lift_of_le_one
    have := hN 0 (M 0) (hMN le_rfl) (M k) (hMN (Nat.zero_le _))
    rw [pow_zero, Valuation.map_one] at this
    exact this.le
  choose y hy using hlift
  have hprec : ∀ {m n : ℕ}, m ≤ n → y m ≡ y n [SMOD (maximalIdeal W ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, mem_pow_iff_v_le W hϖ, map_sub, hy, hy,
      sub_sub_sub_cancel_right]
    exact (hN m (M n) (hMN hmn) (M m) (hMN le_rfl)).le
  obtain ⟨Lim, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := maximalIdeal W) (R := W)) hprec
  refine ⟨u (M 0) + algebraMap W (FractionRing W) Lim, ?_⟩
  rw [tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).mpr γ.ne_zero
  obtain ⟨k, hk⟩ := exists_pow_lt_withZero ((Valuation.ne_zero_iff _).mpr hπ0) hvπ1 hγ0
  rw [mem_atTop_sets]
  refine ⟨M k, fun n hn => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  have e1 : u n - (u (M 0) + algebraMap W (FractionRing W) Lim) =
      (u n - u (M k)) + algebraMap W (FractionRing W) (y k - Lim) := by
    rw [map_sub, hy]; ring
  rw [e1]
  refine lt_of_le_of_lt (Valued.v.map_add _ _) (lt_of_le_of_lt (max_le (hN k (M k) (hMN le_rfl) n ((hMN le_rfl).trans hn)).le ?_) ?_)
  · rw [← mem_pow_iff_v_le W hϖ, ← Ideal.mul_top (maximalIdeal W ^ k), ← smul_eq_mul, ← SModEq.sub_mem]
    exact hL k
  · rw [Valuation.map_pow]; exact hk

end Bridge

section Main

open IsDiscreteValuationRing

attribute [local instance] adicValuedFrac rankOneFrac
open scoped Valued

set_option backward.isDefEq.respectTransparency false in

theorem norm_charpoly_coeff_pow_le [IsAdicComplete (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) (i : ℕ) :
    ‖algebraMap W (FractionRing W) ((LinearMap.mulLeft W a).charpoly.coeff i)‖ ^ Module.finrank W O ≤
      ‖algebraMap W (FractionRing W) ((LinearMap.mulLeft W a).charpoly.coeff 0)‖ ^ (Module.finrank W O - i) := by
  haveI : CompleteSpace (FractionRing W) := completeSpace_fractionRing W
  set K := FractionRing W with hK
  set χ := (LinearMap.mulLeft W a).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _
  have hdeg : χ.natDegree = Module.finrank W O := LinearMap.charpoly_natDegree _
  set χK := χ.map (algebraMap W K) with hχK
  have hmonK : χK.Monic := hmon.map _
  have hdegK : χK.natDegree = Module.finrank W O := by rw [hmon.natDegree_map, hdeg]
  let L := AlgebraicClosure K

  have hint : IsIntegral W a := Algebra.IsIntegral.isIntegral a
  set m := minpoly W a with hm
  have hmirr : Irreducible (m.map (algebraMap W K)) :=
    ((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map).mp (minpoly.irreducible hint)
  have hmmon : (m.map (algebraMap W K)).Monic := (minpoly.monic hint).map _

  set ρ : ℝ := spectralValue (m.map (algebraMap W K)) with hρ
  have hroots : ∀ α ∈ (χK.map (algebraMap K L)).roots, spectralNorm K L α = ρ := by
    intro α hα
    have hχα : aeval α χ = 0 := by
      rw [mem_roots ((hmonK.map _).ne_zero), IsRoot, hχK, map_map, ← IsScalarTower.algebraMap_eq, eval_map,
        ← aeval_def] at hα
      exact hα
    have hmα : aeval α (m.map (algebraMap W K)) = 0 := by
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_aeval_charpoly_mulLeft a m (minpoly.aeval W a) L α hχα
    rw [spectralNorm, ← minpoly.eq_of_irreducible_of_monic hmirr hmα hmmon]
  have key := norm_coeff_pow_le_of_spectralNorm_roots_eq (L := L) χK hmonK (IsAlgClosed.splits _)
    (spectralValue_nonneg _) hroots i
  rwa [hdegK, hχK, coeff_map, coeff_map] at key

private theorem _root_.P1Arch.HCprime.charpoly_mulLeft_isPureSlope_of_isDomain [IsAdicComplete (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    IsPureSlope (Module.finrank W O) (Algebra.norm W a) (Module.finrank W O) (LinearMap.mulLeft W a).charpoly := by
  set d := Module.finrank W O with hd
  set χ := (LinearMap.mulLeft W a).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _
  have hdeg : χ.natDegree = d := LinearMap.charpoly_natDegree _
  have hc0 : addVal W (Algebra.norm W a) = addVal W (χ.coeff 0) := by
    have h1 : Algebra.norm W a = (-1) ^ d * χ.coeff 0 := by
      rw [Algebra.norm_apply, ← LinearMap.det_eq_sign_charpoly_coeff]
      congr 1
    rw [h1, addVal_mul, addVal_pow, AddValuation.map_neg, addVal_one, nsmul_zero, zero_add]
  refine ⟨hmon, hdeg, ?_, by rw [hc0]⟩
  intro i hi
  have key := norm_charpoly_coeff_pow_le (W := W) O a i
  rw [← norm_pow, ← norm_pow, ← map_pow, ← map_pow] at key
  have h2 := addVal_le_of_norm_le W key
  rw [addVal_pow, addVal_pow, nsmul_eq_mul, nsmul_eq_mul] at h2
  rw [hc0]
  exact h2

p2m_export "P1Arch.HCprime" "charpoly_mulLeft_isPureSlope_of_isDomain"
end Main

end HCprime

private theorem _root_.P1Arch.charpoly_mulLeft_isPureSlope_of_isDomain [IsAdicComplete (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    IsPureSlope (Module.finrank W O) (Algebra.norm W a) (Module.finrank W O) (LinearMap.mulLeft W a).charpoly :=
  HCprime.charpoly_mulLeft_isPureSlope_of_isDomain O a

p2m_export "P1Arch" "charpoly_mulLeft_isPureSlope_of_isDomain"
end P1Arch

universe v w

namespace P1Arch
namespace EmbSlope

open IsLocalRing IsDiscreteValuationRing Polynomial

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
variable (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal Ô)

section Restrict
include hv

theorem v_algebraMap_unit (u : Ôˣ) : v (algebraMap Ô C u) = 1 := by
  have hnot : ∀ w : Ôˣ, ¬ v (algebraMap Ô C w) < 1 := fun w h =>
    (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ((hv w).mp h))) w.isUnit
  have h1 : 1 ≤ v (algebraMap Ô C u) := not_lt.mp (hnot u)
  have h2 : 1 ≤ v (algebraMap Ô C ↑u⁻¹) := not_lt.mp (hnot u⁻¹)
  have hprod : v (algebraMap Ô C u) * v (algebraMap Ô C ↑u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm ?_ h1
  calc v (algebraMap Ô C u) = v (algebraMap Ô C u) * 1 := (mul_one _).symm
    _ ≤ v (algebraMap Ô C u) * v (algebraMap Ô C ↑u⁻¹) := mul_le_mul_right h2 _
    _ = 1 := hprod

theorem v_algebraMap_irreducible_lt_one {ϖ : Ô} (hϖ : Irreducible ϖ) : v (algebraMap Ô C ϖ) < 1 :=
  (hv ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))

theorem v_algebraMap_eq_pow {ϖ : Ô} (hϖ : Irreducible ϖ) {a : Ô} (ha : a ≠ 0) :
    ∃ n : ℕ, addVal Ô a = n ∧ v (algebraMap Ô C a) = v (algebraMap Ô C ϖ) ^ n := by
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨n, addVal_def _ u hϖ n rfl, ?_⟩
  rw [map_mul, map_pow, map_mul, map_pow, v_algebraMap_unit v hv u, one_mul]

theorem v_pow_le_of_addVal_le {ϖ : Ô} (hϖ : Irreducible ϖ) {N c : Ô} (hN : N ≠ 0) (d i : ℕ)
    (h : ((d - i : ℕ) : ℕ∞) * addVal Ô N ≤ (d : ℕ∞) * addVal Ô c) :
    v (algebraMap Ô C c) ^ d ≤ v (algebraMap Ô C N) ^ (d - i) := by
  have hθ1 : v (algebraMap Ô C ϖ) ≤ 1 := (v_algebraMap_irreducible_lt_one v hv hϖ).le
  obtain ⟨nN, hnN, hvN⟩ := v_algebraMap_eq_pow v hv hϖ hN
  by_cases hc : c = 0
  · subst hc
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · rw [map_zero, map_zero, zero_pow hd.ne']; exact zero_le'
  obtain ⟨nc, hnc, hvc⟩ := v_algebraMap_eq_pow v hv hϖ hc
  rw [hnN, hnc] at h
  have h' : (d - i) * nN ≤ d * nc := by exact_mod_cast h
  rw [hvc, hvN, ← pow_mul, ← pow_mul]
  exact pow_le_pow_right_of_le_one' hθ1 (by rw [mul_comm nN, mul_comm nc]; exact h')

end Restrict

section Main

theorem aeval_self_charpoly_mulLeft {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (x : S) : aeval x (LinearMap.mulLeft R x).charpoly = 0 := by
  set χ := (LinearMap.mulLeft R x).charpoly with hχ
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft R x)
  rw [← hχ] at h
  have h1 : LinearMap.mulLeft R x = Algebra.lmul R S x := LinearMap.ext fun _ => rfl
  rw [h1, aeval_algHom_apply] at h
  simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using LinearMap.congr_fun h 1

include hv in

theorem v_algHom_pow_finrank_eq [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô]
    (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
    (T : Type u) [CommRing T] [IsDomain T] [Algebra Ô T] [Module.Free Ô T] [Module.Finite Ô T]
    (x : T) (φ : T →ₐ[Ô] C) :
    v (φ x) ^ Module.finrank Ô T = v (algebraMap Ô C (Algebra.norm Ô x)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible Ô
  set d := Module.finrank Ô T with hd
  have hdpos : 0 < d := Module.finrank_pos

  by_cases hx : x = 0
  · subst hx
    simp [Algebra.norm_zero, zero_pow hdpos.ne']
  have hN : Algebra.norm Ô x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  obtain ⟨hmon, hdeg, hineq, -⟩ := P1Arch.charpoly_mulLeft_isPureSlope_of_isDomain (W := Ô) T x
  rw [← hd] at hdeg hineq
  set χ := (LinearMap.mulLeft Ô x).charpoly with hχ

  have hc0 : Algebra.norm Ô x = (-1) ^ d * χ.coeff 0 := by
    rw [Algebra.norm_apply, ← LinearMap.det_eq_sign_charpoly_coeff]
    congr 1
  set A := v (algebraMap Ô C (Algebra.norm Ô x)) with hA
  have hA0 : A ≠ 0 := fun h => hN (hv0 _ h)
  have hAc0 : v (algebraMap Ô C (χ.coeff 0)) = A := by
    rw [hA, hc0, map_mul, map_pow, map_neg, map_one, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg,
      Valuation.map_one, one_pow, one_mul]

  set Y := v (φ x) with hY
  have hsum : ∑ i ∈ Finset.range (d + 1), algebraMap Ô C (χ.coeff i) * φ x ^ i = 0 := by
    have h := aeval_self_charpoly_mulLeft (R := Ô) x
    rw [← hχ] at h
    have h2 : aeval (φ x) χ = 0 := by rw [aeval_algHom_apply, h, map_zero]
    rw [aeval_eq_sum_range, hdeg] at h2
    simpa only [Algebra.smul_def] using h2

  have hterm : ∀ i, v (algebraMap Ô C (χ.coeff i) * φ x ^ i) = v (algebraMap Ô C (χ.coeff i)) * Y ^ i := by
    intro i; rw [Valuation.map_mul, Valuation.map_pow]
  have hci : ∀ i, i ≤ d → v (algebraMap Ô C (χ.coeff i)) ^ d ≤ A ^ (d - i) := fun i hi =>
    v_pow_le_of_addVal_le v hv hϖ hN d i (hineq i hi)
  have htop : algebraMap Ô C (χ.coeff d) * φ x ^ d = φ x ^ d := by
    rw [show χ.coeff d = 1 by rw [← hdeg]; exact hmon.coeff_natDegree, map_one, one_mul]
  rcases lt_trichotomy (Y ^ d) A with hlt | heq | hgt
  ·
    exfalso
    have hdom : ∀ i ∈ Finset.range d, v (algebraMap Ô C (χ.coeff (i + 1)) * φ x ^ (i + 1)) < A := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hterm]

      by_contra hge
      push Not at hge
      have h1 : A ^ d ≤ (v (algebraMap Ô C (χ.coeff (i + 1))) * Y ^ (i + 1)) ^ d := pow_le_pow_left' hge d
      have h2 : (v (algebraMap Ô C (χ.coeff (i + 1))) * Y ^ (i + 1)) ^ d ≤ A ^ (d - (i + 1)) * (Y ^ d) ^ (i + 1) := by
        rw [mul_pow, ← pow_mul, mul_comm (i + 1) d, pow_mul]
        exact mul_le_mul_left (hci (i + 1) (by omega)) _
      have h3 : A ^ (d - (i + 1)) * (Y ^ d) ^ (i + 1) < A ^ (d - (i + 1)) * A ^ (i + 1) :=
        mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hlt zero_le' (by omega)) (pow_pos (zero_lt_iff.mpr hA0) _)
      rw [← pow_add, show d - (i + 1) + (i + 1) = d by omega] at h3
      exact lt_irrefl _ ((h1.trans h2).trans_lt h3)
    have hlt' := v.map_sum_lt hA0 hdom
    rw [Finset.sum_range_succ'] at hsum
    rw [eq_neg_of_add_eq_zero_left hsum, Valuation.map_neg, hterm, pow_zero, mul_one, hAc0] at hlt'
    exact lt_irrefl _ hlt'
  · exact heq
  ·
    exfalso
    have hY0 : Y ^ d ≠ 0 := ne_zero_of_lt hgt
    have hdom : ∀ i ∈ Finset.range d, v (algebraMap Ô C (χ.coeff i) * φ x ^ i) < Y ^ d := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hterm]
      by_contra hge
      push Not at hge
      have h1 : (Y ^ d) ^ d ≤ (v (algebraMap Ô C (χ.coeff i)) * Y ^ i) ^ d := pow_le_pow_left' hge d
      have h2 : (v (algebraMap Ô C (χ.coeff i)) * Y ^ i) ^ d ≤ A ^ (d - i) * (Y ^ d) ^ i := by
        rw [mul_pow, ← pow_mul, mul_comm i d, pow_mul]
        exact mul_le_mul_left (hci i hi.le) _
      have h3 : A ^ (d - i) * (Y ^ d) ^ i < (Y ^ d) ^ (d - i) * (Y ^ d) ^ i :=
        mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hgt zero_le' (by omega)) (pow_pos (zero_lt_iff.mpr hY0) _)
      rw [← pow_add, show d - i + i = d by omega] at h3
      exact lt_irrefl _ ((h1.trans h2).trans_lt h3)
    have hlt' := v.map_sum_lt hY0 hdom
    rw [Finset.sum_range_succ] at hsum
    rw [eq_neg_of_add_eq_zero_left hsum, Valuation.map_neg, htop, Valuation.map_pow] at hlt'
    exact lt_irrefl _ hlt'

end Main

end P1Arch.EmbSlope

open IsLocalRing

namespace P1Arch

section PiLength
variable (R : Type u) [Ring R]

theorem length_pi_fintype (ι : Type v) [Fintype ι] (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Module.length R (Π i, M i) = ∑ i, Module.length R (M i) := by
  classical
  revert M
  refine Fintype.induction_empty_option (P := fun (α : Type v) [Fintype α] =>
    ∀ (M : α → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      Module.length R (Π i, M i) = ∑ i, Module.length R (M i)) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := ih (fun a => M (e a))
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq, h1]
    exact Fintype.sum_equiv e _ _ (fun a => rfl)
  · intro M _ _
    rw [Finset.univ_eq_empty, Finset.sum_empty, Module.length_eq_zero_iff]
    infer_instance
  · intro α _ ih M _ _
    rw [(LinearEquiv.piOptionEquivProd R).length_eq, Module.length_prod, ih (fun a => M (some a)),
      Fintype.sum_option]

end PiLength

section DVR
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem length_quotient_uniformizer' (ϖ : W) (hϖ : Irreducible ϖ) :
    Module.length W (W ⧸ (Ideal.span {ϖ} : Ideal W)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  refine ⟨Ideal.span {ϖ}, ?_, ⟨LinearEquiv.refl W _⟩⟩
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact IsLocalRing.maximalIdeal.isMaximal W

noncomputable def mulQuotW (x y : W) : (W ⧸ (Ideal.span {y} : Ideal W)) →ₗ[W] (W ⧸ (Ideal.span {x * y} : Ideal W)) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft W x) (by
    intro z hz
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by simp [LinearMap.mulLeft_apply]; ring⟩)

theorem mulQuotW_mk (x y r : W) :
    mulQuotW x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl

noncomputable def projQuotW (x y : W) : (W ⧸ (Ideal.span {x * y} : Ideal W)) →ₗ[W] (W ⧸ (Ideal.span {x} : Ideal W)) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

theorem projQuotW_mk (x y r : W) : projQuotW x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

theorem length_quotient_span_pow_uniformizer (ϖ : W) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length W (W ⧸ (Ideal.span {ϖ ^ n} : Ideal W)) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Nat.cast_zero, Module.length_eq_zero_iff]
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact (Ideal.Quotient.eq).mpr (Submodule.mem_top)
  | succ n ih =>

    have hinj : Function.Injective (mulQuotW ϖ (ϖ ^ n)) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [mulQuotW_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact (mul_dvd_mul_iff_left hϖ.ne_zero).mp hz
    have hsurj : Function.Surjective (projQuotW ϖ (ϖ ^ n)) := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ r, rfl⟩
    have hex : Function.Exact (mulQuotW ϖ (ϖ ^ n)) (projQuotW ϖ (ϖ ^ n)) := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [projQuotW_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuotW_mk]⟩
      · rintro ⟨w, hw⟩
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
        rw [mulQuotW_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton] at hw
        obtain ⟨d, hd⟩ := hw
        exact ⟨c - ϖ ^ n * d, by linear_combination -hd⟩
    have h := Module.length_eq_add_of_exact (mulQuotW ϖ (ϖ ^ n)) (projQuotW ϖ (ϖ ^ n)) hinj hsurj hex
    rw [pow_succ', h, ih, length_quotient_uniformizer' ϖ hϖ, Nat.cast_succ]

theorem length_quotient_span_singleton (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (ha : a ≠ 0) :
    Module.length W (W ⧸ (Ideal.span {a} : Ideal W)) = IsDiscreteValuationRing.addVal W a := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hspan : (Ideal.span {(u : W) * ϖ ^ n} : Ideal W) = Ideal.span {ϖ ^ n} :=
    Ideal.span_singleton_eq_span_singleton.mpr ⟨u⁻¹, by rw [mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  rw [hspan, length_quotient_span_pow_uniformizer ϖ hϖ, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr u.isUnit, zero_add, nsmul_eq_mul, mul_one]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem addVal_prod' {ι : Type v} (s : Finset ι) (f : ι → W) [IsDomain W] [IsDiscreteValuationRing W] :
    IsDiscreteValuationRing.addVal W (∏ i ∈ s, f i) = ∑ i ∈ s, IsDiscreteValuationRing.addVal W (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]

theorem length_quotient_span_singleton_eq_addVal_norm (ϖ : W) (hϖ : Irreducible ϖ)
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O]
    (x : O) (hx : x ≠ 0) :
    Module.length W (O ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal W (Algebra.norm W x) := by
  classical
  letI := Module.Free.ChooseBasisIndex.fintype W O
  let b := Module.Free.chooseBasis W O
  have hI : (Ideal.span {x} : Ideal O) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hx
  obtain ⟨w, hw⟩ := associated_norm_prod_smith b hx
  have hv : IsDiscreteValuationRing.addVal W (Algebra.norm W x) =
      IsDiscreteValuationRing.addVal W (∏ i, Ideal.smithCoeffs b (Ideal.span {x}) hI i) := by
    rw [← hw, IsDiscreteValuationRing.addVal_mul, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr w.isUnit, add_zero]
  rw [(Ideal.quotientEquivPiSpan (Ideal.span {x}) b hI).length_eq, length_pi_fintype, hv, addVal_prod']
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton ϖ hϖ _ (Ideal.smithCoeffs_ne_zero b _ hI i)

end DVR

end P1Arch

namespace P1Arch
namespace EmbCount

open IsLocalRing IsDiscreteValuationRing Polynomial

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]

theorem card_algHom_le_finrank (T : Type*) [CommRing T] [Algebra Ô T] [Module.Free Ô T] [Module.Finite Ô T]
    (Φ : Finset (T →ₐ[Ô] C)) : Φ.card ≤ Module.finrank Ô T := by
  classical
  letI := Module.Free.ChooseBasisIndex.fintype Ô T
  let b := Module.Free.chooseBasis Ô T

  have hli : LinearIndependent C (fun φ : Φ => fun i => (φ : T →ₐ[Ô] C) (b i)) := by
    have h0 : LinearIndependent C (fun φ : Φ => ((φ : T →ₐ[Ô] C) : T → C)) := by
      have h := (linearIndependent_monoidHom T C).comp (fun φ : Φ => (φ : T →ₐ[Ô] C).toMonoidHom) (by
        intro φ ψ h
        apply Subtype.ext
        apply AlgHom.ext
        intro t
        exact DFunLike.congr_fun h t)
      exact h
    rw [linearIndependent_iff'] at h0 ⊢
    intro s g hg φ hφ
    apply h0 s g _ φ hφ
    ext t
    have hgi : ∀ i, ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) = 0 := fun i => by
      have := congr_fun hg i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have ht : ∀ ψ : T →ₐ[Ô] C, ψ t = ∑ i, algebraMap Ô C (b.repr t i) * ψ (b i) := by
      intro ψ
      conv_lhs => rw [← b.sum_repr t]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Algebra.smul_def]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∑ ψ ∈ s, g ψ * (algebraMap Ô C (b.repr t i) * (ψ : T →ₐ[Ô] C) (b i))
        = algebraMap Ô C (b.repr t i) * ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ψ _ => ?_; ring
    rw [this, hgi i, mul_zero]
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at hcard
  rw [Module.finrank_eq_card_chooseBasisIndex]
  exact hcard

section Kernel

variable {S : Type u} [CommRing S] [Algebra Ô S]

theorem algebraMap_eq_zero_imp {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0) {a : Ô}
    (ha : algebraMap Ô C a = 0) : a = 0 := by
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha0 hϖ
  rw [map_mul, map_pow, mul_eq_zero] at ha
  rcases ha with hu | hp
  · exact (u.isUnit.map (algebraMap Ô C)).ne_zero hu
  · exact hCϖ (pow_eq_zero_iff'.mp hp).1

theorem comap_ker_eq_bot {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0) (φ : S →ₐ[Ô] C) :
    (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at ha
  rw [Ideal.mem_bot]
  exact algebraMap_eq_zero_imp hϖ hCϖ ha

theorem algebraMap_quotient_ker_injective {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0)
    (φ : S →ₐ[Ô] C) : Function.Injective (algebraMap Ô (S ⧸ RingHom.ker φ.toRingHom)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [IsScalarTower.algebraMap_apply Ô S (S ⧸ RingHom.ker φ.toRingHom), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have : a ∈ (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) := ha
  rwa [comap_ker_eq_bot hϖ hCϖ φ, Ideal.mem_bot] at this

theorem ker_mem_minimalPrimes [Module.Finite Ô S] {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0)
    (φ : S →ₐ[Ô] C) : RingHom.ker φ.toRingHom ∈ minimalPrimes S := by
  set P := RingHom.ker φ.toRingHom with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hPp, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hqP
  haveI := hq

  have hPq : (P.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : (P.map (Ideal.Quotient.mk q)).comap (algebraMap Ô (S ⧸ q)) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq Ô S (S ⧸ q), Ideal.Quotient.algebraMap_eq, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hqP]
    exact comap_ker_eq_bot hϖ hCϖ φ
  have h0 : P.map (Ideal.Quotient.mk q) = ⊥ := Ideal.eq_bot_of_comap_eq_bot hcomap
  intro s hs
  have : Ideal.Quotient.mk q s ∈ P.map (Ideal.Quotient.mk q) := Ideal.mem_map_of_mem _ hs
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end Kernel

section Count

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)

theorem card_filter_ker_eq_le {S : Type u} [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
    (Φ : Finset (S →ₐ[Ô] C)) (𝔓 : Ideal S) [𝔓.IsPrime] (hinj : Function.Injective (algebraMap Ô (S ⧸ 𝔓))) :
    (Φ.filter (fun φ => RingHom.ker φ.toRingHom = 𝔓)).card ≤ Module.finrank Ô (S ⧸ 𝔓) := by
  classical
  haveI : Module.IsTorsionFree Ô (S ⧸ 𝔓) := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Module.Free Ô (S ⧸ 𝔓) := Module.free_of_finite_type_torsion_free'

  set F := Φ.filter (fun φ => RingHom.ker φ.toRingHom = 𝔓) with hF
  have hlift : ∀ φ ∈ F, ∀ a ∈ 𝔓, (φ : S →ₐ[Ô] C) a = 0 := by
    intro φ hφ a ha
    rw [hF, Finset.mem_filter] at hφ
    rw [← hφ.2] at ha
    exact ha
  let L : F → ((S ⧸ 𝔓) →ₐ[Ô] C) := fun φ => Ideal.Quotient.liftₐ 𝔓 (φ : S →ₐ[Ô] C) (hlift φ φ.2)
  have hL : Function.Injective L := by
    intro φ ψ h
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    have := DFunLike.congr_fun h (Ideal.Quotient.mk 𝔓 s)
    simpa [L, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] using this
  have h1 := card_algHom_le_finrank (Ô := Ô) (C := C) (S ⧸ 𝔓) (Finset.univ.image L)
  rw [Finset.card_image_of_injective _ hL, Finset.card_univ, Fintype.card_coe] at h1
  exact h1

theorem pow_injective_of_lt_one {θ : Γ₀} (h0 : θ ≠ 0) (h1 : θ < 1) {m n : ℕ} (h : θ ^ m = θ ^ n) : m = n :=
  pow_right_injective₀ (zero_lt_iff.mpr h0) h1.ne h

variable (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal Ô)
variable (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
include hv hv0

theorem depth_ker_eq [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô] {S : Type u} [CommRing S] [Algebra Ô S]
    [Module.Finite Ô S] {ϖ : Ô} (hϖ : Irreducible ϖ) (x : S) (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (φ : S →ₐ[Ô] C)
    (hφ : v (φ x) ^ r = v (algebraMap Ô C ϖ) ^ p) :
    (r : ℕ∞) * Module.length Ô ((S ⧸ RingHom.ker φ.toRingHom) ⧸
        Ideal.span {Ideal.Quotient.mk (RingHom.ker φ.toRingHom) x}) =
      ((p * Module.finrank Ô (S ⧸ RingHom.ker φ.toRingHom) : ℕ) : ℕ∞) := by
  have hθlt : v (algebraMap Ô C ϖ) < 1 := EmbSlope.v_algebraMap_irreducible_lt_one v hv hϖ
  have hθ0 : v (algebraMap Ô C ϖ) ≠ 0 := fun h => hϖ.ne_zero (hv0 _ h)
  have hCϖ : algebraMap Ô C ϖ ≠ 0 := fun h => hθ0 (by rw [h, Valuation.map_zero])
  set 𝔓 := RingHom.ker φ.toRingHom with h𝔓
  haveI : 𝔓.IsPrime := RingHom.ker_isPrime _
  have hinj := algebraMap_quotient_ker_injective hϖ hCϖ φ
  haveI : Module.IsTorsionFree Ô (S ⧸ 𝔓) := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Module.Free Ô (S ⧸ 𝔓) := Module.free_of_finite_type_torsion_free'
  set T := S ⧸ 𝔓
  set xb : T := Ideal.Quotient.mk 𝔓 x with hxb

  let φb : T →ₐ[Ô] C := Ideal.Quotient.liftₐ 𝔓 φ (fun a ha => ha)
  have hφb : φb xb = φ x := Ideal.Quotient.lift_mk 𝔓 (φ : S →+* C) _
  have hx0 : xb ≠ 0 := by
    intro h0
    have : v (φ x) = 0 := by rw [← hφb, h0, map_zero, Valuation.map_zero]
    rw [this, zero_pow (by omega)] at hφ
    exact pow_ne_zero p hθ0 hφ.symm

  have hcore := EmbSlope.v_algHom_pow_finrank_eq v hv hv0 T xb φb
  rw [hφb] at hcore
  have hN : Algebra.norm Ô xb ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx0
  obtain ⟨a, ha, hva⟩ := EmbSlope.v_algebraMap_eq_pow v hv hϖ hN
  rw [P1Arch.length_quotient_span_singleton_eq_addVal_norm ϖ hϖ T xb hx0, ha]

  set d := Module.finrank Ô T
  have hexp : a * r = p * d := by
    apply pow_injective_of_lt_one hθ0 hθlt
    calc v (algebraMap Ô C ϖ) ^ (a * r) = (v (algebraMap Ô C ϖ) ^ a) ^ r := pow_mul _ _ _
      _ = (v (φ x) ^ d) ^ r := by rw [← hva, ← hcore]
      _ = (v (φ x) ^ r) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = v (algebraMap Ô C ϖ) ^ (p * d) := by rw [hφ, ← pow_mul]
  have hexp' : r * a = p * d := by rw [mul_comm]; exact hexp
  exact_mod_cast hexp'

end Count

end P1Arch.EmbCount

open IsLocalRing in
open Algebra in

theorem solution
    {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [IsAdicComplete (maximalIdeal Ô) Ô]
    (ϖ : Ô) (hϖ : Irreducible ϖ)
    (S : Type u) [CommRing S] [Algebra Ô S] [Module.Finite Ô S] (x : S)
    (C : Type v) [Field C] [Algebra Ô C]
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
    (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ maximalIdeal Ô)
    (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ)
    (Φ : Finset (S →ₐ[Ô] C)) (hΦ : ∀ φ ∈ Φ, v (φ x) ^ r = v (algebraMap Ô C ϖ) ^ p) :
    (Φ.card : ℕ∞) ≤
      ∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal ∧
          (r : ℕ∞) * Module.length Ô ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal x}) =
            ((p * Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞) := by
  classical
  have hθlt := P1Arch.EmbSlope.v_algebraMap_irreducible_lt_one v hv hϖ
  have hθ0 : v (algebraMap Ô C ϖ) ≠ 0 := fun h => hϖ.ne_zero (hv0 _ h)
  have hCϖ : algebraMap Ô C ϖ ≠ 0 := fun h => hθ0 (by rw [h, Valuation.map_zero])
  haveI : IsNoetherianRing S := isNoetherian_of_tower Ô (inferInstance : IsNoetherian Ô S)

  set cond : PrimeSpectrum S → Prop := fun 𝔓 => 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal ∧
      (r : ℕ∞) * Module.length Ô ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal x}) =
        ((p * Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞) with hcond
  have hQfin : {𝔓 : PrimeSpectrum S | cond 𝔓}.Finite := by
    have hmin : {𝔓 : PrimeSpectrum S | 𝔓.asIdeal ∈ minimalPrimes S}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing S).preimage (fun a _ b _ h => PrimeSpectrum.ext h)
    exact hmin.subset fun 𝔓 h => h.1
  change (Φ.card : ℕ∞) ≤ ∑ᶠ 𝔓 ∈ {𝔓 : PrimeSpectrum S | cond 𝔓}, (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞)
  rw [finsum_mem_eq_finite_toFinset_sum _ hQfin, ← Nat.cast_sum, Nat.cast_le]

  let κ : (S →ₐ[Ô] C) → PrimeSpectrum S := fun φ => ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩
  have hκcond : ∀ φ ∈ Φ, cond (κ φ) := by
    intro φ hφ
    refine ⟨P1Arch.EmbCount.ker_mem_minimalPrimes hϖ hCϖ φ, ?_, ?_⟩
    · change algebraMap Ô S ϖ ∉ RingHom.ker φ.toRingHom
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
      exact hCϖ
    · exact P1Arch.EmbCount.depth_ker_eq v hv hv0 hϖ x r hr p φ (hΦ φ hφ)
  calc Φ.card = ∑ 𝔓 ∈ Φ.image κ, (Φ.filter (fun φ => κ φ = 𝔓)).card := Finset.card_eq_sum_card_image κ Φ
    _ ≤ ∑ 𝔓 ∈ Φ.image κ, Module.finrank Ô (S ⧸ 𝔓.asIdeal) := by
      refine Finset.sum_le_sum fun 𝔓 h𝔓 => ?_
      obtain ⟨φ₀, hφ₀, rfl⟩ := Finset.mem_image.mp h𝔓
      have hfilt : Φ.filter (fun φ => κ φ = κ φ₀) = Φ.filter (fun φ => RingHom.ker φ.toRingHom = (κ φ₀).asIdeal) :=
        Finset.filter_congr fun φ _ => PrimeSpectrum.ext_iff
      rw [hfilt]
      haveI : (κ φ₀).asIdeal.IsPrime := (κ φ₀).isPrime
      exact P1Arch.EmbCount.card_filter_ker_eq_le Φ (κ φ₀).asIdeal
        (P1Arch.EmbCount.algebraMap_quotient_ker_injective hϖ hCϖ φ₀)
    _ ≤ ∑ 𝔓 ∈ hQfin.toFinset, Module.finrank Ô (S ⧸ 𝔓.asIdeal) := by
      refine Finset.sum_le_sum_of_subset fun 𝔓 h𝔓 => ?_
      obtain ⟨φ₀, hφ₀, rfl⟩ := Finset.mem_image.mp h𝔓
      rw [Set.Finite.mem_toFinset]
      exact hκcond φ₀ hφ₀

end S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
end P2MW
export P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq (solution)
