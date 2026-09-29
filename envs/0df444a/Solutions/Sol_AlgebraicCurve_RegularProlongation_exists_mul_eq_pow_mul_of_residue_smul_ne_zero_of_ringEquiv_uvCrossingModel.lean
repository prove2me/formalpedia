-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fe660853-4b07-5aa6-bae1-4692c9f89e8d

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace CentreUniformiser

theorem crossingRelation_ne_zero (W : Type*) [CommRing W] [Nontrivial W] (ϖ : W) :
    ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C ϖ) ≠ 0 := by
  classical
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)) h
  have hne : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h0
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h0
    simp at this
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, map_sub,
    MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_C, if_pos rfl, if_neg hne, map_zero] at h1
  simp at h1

theorem ringKrullDim_uvCrossingModel_le_two (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (ϖ : W) :
    ringKrullDim (UVCrossingModel W ϖ) ≤ 2 := by
  have h3 : ringKrullDim (MvPowerSeries (Fin 2) W) = ((2 + 1 : ℕ) : WithBot ℕ∞) :=
    MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing W 2
  have hr : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C ϖ) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W) :=
    mem_nonZeroDivisors_of_ne_zero (crossingRelation_ne_zero W ϖ)
  have key := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [h3] at key
  change ringKrullDim (UVCrossingModel W ϖ) + 1 ≤ _ at key
  generalize hx : ringKrullDim (UVCrossingModel W ϖ) = x at key ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at key
      exact absurd (WithBot.coe_le_coe.mp key) (by simp)
    | coe n =>
      have key' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((2 + 1 : ℕ) : WithBot ℕ∞) := by
        simpa using key
      have : n + 1 ≤ 2 + 1 := by exact_mod_cast key'
      have hn : n ≤ 2 := by omega
      have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (by exact_mod_cast hn)
      simpa using hn'

theorem height_maximalIdeal_le_two
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W ϖ) :
    (IsLocalRing.maximalIdeal B).height ≤ 2 := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) W) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsNoetherianRing (UVCrossingModel W ϖ) := inferInstance
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    isNoetherianRing_of_ringEquiv _ ι.symm
  haveI : Module.FaithfullyFlat B (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal B
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat
    (B := AdicCompletion (IsLocalRing.maximalIdeal B) B) (IsLocalRing.maximalIdeal B)
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (IsLocalRing.maximalIdeal B) Q
  have h2 : (Q.height : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have h3 : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) ≤ 2 :=
    (ringKrullDim_eq_of_ringEquiv ι).trans_le (ringKrullDim_uvCrossingModel_le_two W ϖ)
  have h4 : (IsLocalRing.maximalIdeal B).height ≤ Q.height := h1 ▸ le_self_add
  have h5 : ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    (WithBot.coe_le_coe.mpr h4).trans (h2.trans h3)
  exact WithBot.coe_le_coe.mp h5

theorem height_eq_one_of_ne_bot_of_ne_maximalIdeal
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    (P : Ideal B) [P.IsPrime] (hP0 : P ≠ ⊥) (hPm : P ≠ IsLocalRing.maximalIdeal B)
    (hm : (IsLocalRing.maximalIdeal B).height ≤ 2) : P.height = 1 := by
  have hlt1 : (⊥ : Ideal B) < P := bot_lt_iff_ne_bot.mpr hP0
  have hlt2 : P < IsLocalRing.maximalIdeal B :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hPm
  have h1 : (⊥ : Ideal B).height < P.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1
  have h2 : P.height < (IsLocalRing.maximalIdeal B).height :=
    Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2
  rw [Ideal.height_bot] at h1
  have h3 : P.height < 2 := h2.trans_le hm
  have hfin : P.height ≠ ⊤ := by
    intro h; rw [h] at h3; exact absurd h3 (by simp)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at h1 h3 ⊢
  have h1' : 0 < n := by exact_mod_cast h1
  have h3' : n < 2 := by exact_mod_cast h3
  have : n = 1 := by omega
  exact_mod_cast this

section Axes

variable {σ : Type*} {k : Type*} [CommRing k] [NoZeroDivisors k]

theorem eq_single_of_add_eq_single [DecidableEq σ] {p q : σ →₀ ℕ} {i : σ} {N : ℕ}
    (h : p + q = Finsupp.single i N) : p = Finsupp.single i (p i) := by
  ext s
  by_cases hs : s = i
  · subst hs; simp
  · have := congrArg (fun f : σ →₀ ℕ => f s) h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg (Ne.symm hs)] at this
    rw [Finsupp.single_apply, if_neg (Ne.symm hs)]
    omega

theorem coeff_single_eq_zero_of_sq [DecidableEq σ] (F : MvPowerSeries σ k) (i : σ)
    (hsq : ∀ n : ℕ, MvPowerSeries.coeff (Finsupp.single i n) (F * F) = 0) :
    ∀ n : ℕ, MvPowerSeries.coeff (Finsupp.single i n) F = 0 := by
  by_contra hcon
  push Not at hcon
  classical
  let n₀ := Nat.find hcon
  have hn₀ : MvPowerSeries.coeff (Finsupp.single i n₀) F ≠ 0 := Nat.find_spec hcon
  have hmin : ∀ n, n < n₀ → MvPowerSeries.coeff (Finsupp.single i n) F = 0 := fun n hn => by
    have := Nat.find_min hcon hn
    simpa using this
  have key : MvPowerSeries.coeff (Finsupp.single i (n₀ + n₀)) (F * F) =
      MvPowerSeries.coeff (Finsupp.single i n₀) F * MvPowerSeries.coeff (Finsupp.single i n₀) F := by
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_single (Finsupp.single i n₀, Finsupp.single i n₀)
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      simp only at hpq hne ⊢
      have hp : p = Finsupp.single i (p i) :=
        eq_single_of_add_eq_single (N := n₀ + n₀) (by rw [hpq, Finsupp.single_add])
      have hq : q = Finsupp.single i (q i) :=
        eq_single_of_add_eq_single (N := n₀ + n₀) (by rw [add_comm, hpq, Finsupp.single_add])
      have hsum : p i + q i = n₀ + n₀ := by
        have := congrArg (fun f : σ →₀ ℕ => f i) hpq
        simpa using this
      rcases lt_trichotomy (p i) n₀ with hlt | heq | hgt
      · rw [hp, hmin _ hlt, zero_mul]
      · exfalso
        apply hne
        have hqi : q i = n₀ := by omega
        rw [hp, hq, heq, hqi]
      · have hlt : q i < n₀ := by omega
        rw [hq, hmin _ hlt, mul_zero]
    · intro h
      exfalso; apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal, ← Finsupp.single_add]
  have := hsq (n₀ + n₀)
  rw [key] at this
  exact hn₀ ((mul_self_eq_zero).mp this)

theorem X_mul_X_dvd_iff (F : MvPowerSeries (Fin 2) k) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) ∣ F ↔
      ∀ m : Fin 2 →₀ ℕ, (m 0 = 0 ∨ m 1 = 0) → MvPowerSeries.coeff m F = 0 := by
  classical
  set s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hs
  have hXX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = MvPowerSeries.monomial s 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]
  have hs0 : s 0 = 1 := by simp [hs]
  have hs1 : s 1 = 1 := by simp [hs]
  have hle : ∀ m : Fin 2 →₀ ℕ, s ≤ m ↔ ¬ (m 0 = 0 ∨ m 1 = 0) := by
    intro m
    constructor
    · intro h
      have h0 := h 0; have h1 := h 1
      rw [hs0] at h0; rw [hs1] at h1
      omega
    · intro h i
      fin_cases i
      · change s 0 ≤ m 0; rw [hs0]; omega
      · change s 1 ≤ m 1; rw [hs1]; omega
  rw [hXX]
  constructor
  · rintro ⟨G, rfl⟩ m hm
    rw [MvPowerSeries.coeff_monomial_mul, if_neg ((hle m).not.mpr (not_not.mpr hm))]
  · intro h
    refine ⟨fun m => MvPowerSeries.coeff (m + s) F, ?_⟩
    ext m
    rw [MvPowerSeries.coeff_monomial_mul]
    split_ifs with hsm
    · rw [one_mul]
      change MvPowerSeries.coeff m F = MvPowerSeries.coeff (m - s + s) F
      rw [tsub_add_cancel_of_le hsm]
    · exact h m (not_not.mp ((hle m).not.mp hsm))

theorem X_mul_X_dvd_of_dvd_sq (F : MvPowerSeries (Fin 2) k)
    (h : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) ∣ F * F) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) ∣ F := by
  classical
  rw [X_mul_X_dvd_iff] at h ⊢
  have h0 : ∀ n : ℕ, MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n) F = 0 :=
    coeff_single_eq_zero_of_sq F 0 (fun n => h _ (Or.inr (by simp)))
  have h1 : ∀ n : ℕ, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) F = 0 :=
    coeff_single_eq_zero_of_sq F 1 (fun n => h _ (Or.inl (by simp)))
  intro m hm
  rcases hm with hm | hm
  · have : m = Finsupp.single 1 (m 1) := by
      ext i; fin_cases i
      · simpa using hm
      · simp
    rw [this]; exact h1 _
  · have : m = Finsupp.single 0 (m 0) := by
      ext i; fin_cases i
      · simp
      · simpa using hm
    rw [this]; exact h0 _

end Axes

section SpecialFibre

variable {W : Type*} [CommRing W]

theorem mem_span_C_X_mul_X_iff (π : W) (f : MvPowerSeries (Fin 2) W) :
    f ∈ Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W), MvPowerSeries.X 0 * MvPowerSeries.X 1} ↔
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (W ⧸ Ideal.span {π})) ∣
        MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})) f := by
  classical
  set red := MvPowerSeries.map (σ := Fin 2) (Ideal.Quotient.mk (Ideal.span {π})) with hred
  have hredC : red (MvPowerSeries.C π) = 0 := by
    rw [hred, MvPowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero]
  have hredXX : red (MvPowerSeries.X 0 * MvPowerSeries.X 1) = MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
    rw [map_mul, hred, MvPowerSeries.map_X, MvPowerSeries.map_X]
  constructor
  · intro hf
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hf
    refine ⟨red d, ?_⟩
    rw [map_add, map_mul, map_mul, hredC, hredXX, mul_zero, zero_add, mul_comm]
  · rintro ⟨Hbar, hH⟩

    let H : MvPowerSeries (Fin 2) W := fun m => (Ideal.Quotient.mk_surjective (Hbar m)).choose
    have hHlift : red H = Hbar := by
      ext m
      rw [hred, MvPowerSeries.coeff_map, MvPowerSeries.coeff_apply]
      exact (Ideal.Quotient.mk_surjective (Hbar m)).choose_spec

    have hdiff : red (f - MvPowerSeries.X 0 * MvPowerSeries.X 1 * H) = 0 := by
      rw [map_sub, map_mul, hredXX, hHlift, hH, sub_self]
    have hcoef : ∀ m, ∃ g : W, g * π = MvPowerSeries.coeff m (f - MvPowerSeries.X 0 * MvPowerSeries.X 1 * H) := by
      intro m
      have := congrArg (MvPowerSeries.coeff m) hdiff
      rw [hred, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this
      exact Ideal.mem_span_singleton'.mp this
    let G : MvPowerSeries (Fin 2) W := fun m => (hcoef m).choose
    have hG : MvPowerSeries.C π * G = f - MvPowerSeries.X 0 * MvPowerSeries.X 1 * H := by
      ext m
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply G, mul_comm]
      exact (hcoef m).choose_spec
    have : f = G * MvPowerSeries.C π + H * (MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
      rw [mul_comm G, hG]; ring
    rw [this]
    exact Ideal.mem_span_pair.mpr ⟨G, H, rfl⟩

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem mem_span_C_X_mul_X_of_sq_mem (π : W) (hπ : Irreducible π) (f : MvPowerSeries (Fin 2) W)
    (hf : f * f ∈ Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W), MvPowerSeries.X 0 * MvPowerSeries.X 1}) :
    f ∈ Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W), MvPowerSeries.X 0 * MvPowerSeries.X 1} := by
  haveI : (Ideal.span {π}).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr (Irreducible.prime hπ)
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  rw [mem_span_C_X_mul_X_iff] at hf ⊢
  rw [map_mul] at hf
  exact X_mul_X_dvd_of_dvd_sq _ hf

theorem isRadical_span_const (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π} : Ideal (UVCrossingModel W (π ^ E))).IsRadical := by
  rw [Ideal.isRadical_iff_pow_one_lt 2 one_lt_two]
  intro z hz
  obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) z
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨g, rfl⟩ := mk_surjective (π ^ E) c

  set J : Ideal (MvPowerSeries (Fin 2) W) :=
    Ideal.span {(MvPowerSeries.C π : MvPowerSeries (Fin 2) W), MvPowerSeries.X 0 * MvPowerSeries.X 1} with hJ
  have hrelJ : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E)) ∈ J := by
    have hC : (MvPowerSeries.C (π ^ E) : MvPowerSeries (Fin 2) W) =
        MvPowerSeries.C (π ^ (E - 1)) * MvPowerSeries.C π := by
      rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hE]
    have : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E)) =
        (-MvPowerSeries.C (π ^ (E - 1))) * MvPowerSeries.C π + 1 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
      rw [hC]; ring
    rw [this]; exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩
  have hker : f * f - g * MvPowerSeries.C π ∈ uvCrossingIdeal W (π ^ E) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change mk (π ^ E) (f * f - g * MvPowerSeries.C π) = 0
    rw [map_sub, map_mul, map_mul, sub_eq_zero]
    change mk (π ^ E) f * mk (π ^ E) f = mk (π ^ E) g * const (π ^ E) π
    rw [hc, pow_two]
  have hker' : f * f - g * MvPowerSeries.C π ∈ J := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hker
    rw [← hr]; exact J.mul_mem_left r hrelJ
  have hff : f * f ∈ J := by
    have : f * f = (f * f - g * MvPowerSeries.C π) + g * MvPowerSeries.C π := by ring
    rw [this]
    exact J.add_mem hker' (J.mul_mem_left g (Ideal.subset_span (by simp)))
  have hfJ : f ∈ J := mem_span_C_X_mul_X_of_sq_mem π hπ f hff
  obtain ⟨G, H, hGH⟩ := Ideal.mem_span_pair.mp hfJ

  have hXX : mk (π ^ E) (MvPowerSeries.X 0 * MvPowerSeries.X 1) = const (π ^ E) π * const (π ^ E) (π ^ (E - 1)) := by
    have h1 : mk (π ^ E) (MvPowerSeries.X 0 * MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E)) := by
      rw [← sub_eq_zero, ← map_sub]
      change Ideal.Quotient.mk (uvCrossingIdeal W (π ^ E)) _ = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [h1]
    change mk (π ^ E) (MvPowerSeries.C (π ^ E)) = mk (π ^ E) (MvPowerSeries.C π) * mk (π ^ E) (MvPowerSeries.C (π ^ (E - 1)))
    rw [← map_mul, ← map_mul, ← pow_succ', Nat.sub_add_cancel hE]
  rw [← hGH, map_add, map_mul, map_mul, hXX]
  change mk (π ^ E) G * const (π ^ E) π + mk (π ^ E) H * (const (π ^ E) π * const (π ^ E) (π ^ (E - 1))) ∈ _
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end SpecialFibre

section Transfer

variable {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem mem_span_of_pow_mem_span (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    (ϖ : B) (hϖ : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) ϖ) = const (π ^ E) π)
    (b : B) (m : ℕ) (hb : b ^ m ∈ Ideal.span {ϖ}) : b ∈ Ideal.span {ϖ} := by
  haveI : Module.FaithfullyFlat B (AdicCompletion (maximalIdeal B) B) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal B
  set φ : B →+* UVCrossingModel W (π ^ E) :=
    (ι : AdicCompletion (maximalIdeal B) B →+* UVCrossingModel W (π ^ E)).comp
      (algebraMap B (AdicCompletion (maximalIdeal B) B)) with hφ
  have hφapp : ∀ x : B, φ x = ι (algebraMap B (AdicCompletion (maximalIdeal B) B) x) := fun x => rfl
  have hφϖ : φ ϖ = const (π ^ E) π := hϖ
  have h1 : (φ b) ^ m ∈ Ideal.span {const (π ^ E) π} := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
    rw [← map_pow, ← hc, map_mul, hφϖ]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h2 : φ b ∈ Ideal.span {const (π ^ E) π} := (isRadical_span_const π hπ E hE) ⟨m, h1⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : algebraMap B (AdicCompletion (maximalIdeal B) B) b ∈
      (Ideal.span {ϖ}).map (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
    have : algebraMap B (AdicCompletion (maximalIdeal B) B) b =
        ι.symm c * algebraMap B (AdicCompletion (maximalIdeal B) B) ϖ := by
      apply ι.injective
      rw [map_mul, RingEquiv.apply_symm_apply, ← hφapp, ← hφapp, hφϖ, hc]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  have h4 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal B) B) (Ideal.span {ϖ})
  rw [← h4, Ideal.mem_comap]
  exact h3

end Transfer

theorem inv_mem_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {x : F} (hx : x ∈ O)
    (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hv' : x * (v : F) = 1 := by
    have := congrArg Subtype.val hv
    simpa using this
  have : x⁻¹ = (v : F) := (eq_inv_of_mul_eq_one_right hv').symm
  rw [this]; exact v.2

end CentreUniformiser

open CentreUniformiser in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R.integers)
    (ϖ : L) (hϖ0 : ϖ ≠ 0) (hϖA : ϖ ∈ A) (hϖm : IsLocalRing.residue ↥A ⟨ϖ, hϖA⟩ = 0)
    (hϖN : algebraMap L F ϖ ∈ 𝒩₀)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F ϖ, hϖN⟩) = const (π ^ E) π)
    (p s : ↥𝒩₀) (hp0 : p ≠ 0) (hp : R.residue ⟨(p : F), h𝒩₀R p p.2⟩ = 0)
    (hs : R.residue ⟨(s : F), h𝒩₀R s s.2⟩ ≠ 0) (hsu : ¬ IsUnit s)
    (a : ↥𝒩₀) (e : L) (h : e • (a : F) ∈ R.integers) (hne : R.residue ⟨e • (a : F), h⟩ ≠ 0) :
    ∃ (g : ℕ) (a₁ a₂ : ↥𝒩₀),
      R.residue ⟨(a₁ : F), h𝒩₀R a₁ a₁.2⟩ ≠ 0 ∧ R.residue ⟨(a₂ : F), h𝒩₀R a₂ a₂.2⟩ ≠ 0 ∧
      a * a₂ = ⟨algebraMap L F ϖ, hϖN⟩ ^ g * a₁ ∧
      ∃ hu : e * ϖ ^ g ∈ A, IsUnit (⟨e * ϖ ^ g, hu⟩ : ↥A) := by
  classical

  let incl : ↥𝒩₀ →+* ↥R.integers := (𝒩₀.subtype).codRestrict R.integers (fun f => h𝒩₀R f f.2)
  have hincl : ∀ f : ↥𝒩₀, incl f = ⟨(f : F), h𝒩₀R f f.2⟩ := fun f => rfl
  let P : Ideal ↥𝒩₀ := (maximalIdeal ↥R.integers).comap incl
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime incl _
  have hP : ∀ b : ↥𝒩₀, b ∈ P ↔ R.residue ⟨(b : F), h𝒩₀R b b.2⟩ = 0 := by
    intro b
    change incl b ∈ maximalIdeal ↥R.integers ↔ _
    rw [← R.ker_residue, RingHom.mem_ker, hincl]
  have hPres : ∀ b : ↥𝒩₀, b ∉ P → R.residue ⟨(b : F), h𝒩₀R b b.2⟩ ≠ 0 := fun b hb h0 => hb ((hP b).mpr h0)
  have hP0 : P ≠ ⊥ := by
    intro h0
    have : p ∈ P := (hP p).mpr hp
    rw [h0, Ideal.mem_bot] at this
    exact hp0 this
  have hPm : P ≠ maximalIdeal ↥𝒩₀ := by
    intro hm
    have : s ∉ P := fun h' => hs ((hP s).mp h')
    rw [hm] at this
    exact this ((IsLocalRing.mem_maximalIdeal s).mpr hsu)

  haveI : IsIntegrallyClosed ↥𝒩₀ :=
    IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel π hπ E hE ι
  have hm2 : (maximalIdeal ↥𝒩₀).height ≤ 2 := height_maximalIdeal_le_two (π ^ E) ι
  have hht : P.height = 1 := height_eq_one_of_ne_bot_of_ne_maximalIdeal P hP0 hPm hm2
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one P hht
  set D := Localization.AtPrime P with hD
  have hinj : Function.Injective (algebraMap ↥𝒩₀ D) :=
    IsLocalization.injective D P.primeCompl_le_nonZeroDivisors

  set ϖB : ↥𝒩₀ := ⟨algebraMap L F ϖ, hϖN⟩ with hϖB
  have hϖB0 : ϖB ≠ 0 := by
    intro h0
    have : algebraMap L F ϖ = 0 := by simpa [hϖB] using congrArg Subtype.val h0
    exact hϖ0 ((map_eq_zero _).mp this)
  have hϖP : ϖB ∈ P := by
    rw [hP]
    have := R.residue_algebraMap ⟨ϖ, hϖA⟩
    rw [hϖm, map_zero] at this
    exact this
  have hred : ∀ (b : ↥𝒩₀) (m : ℕ), b ^ m ∈ Ideal.span {ϖB} → b ∈ Ideal.span {ϖB} :=
    fun b m hb => mem_span_of_pow_mem_span π hπ E hE ι ϖB hιϖ b m hb
  set ϖD : D := algebraMap ↥𝒩₀ D ϖB with hϖD
  have hϖD0 : ϖD ≠ 0 := fun h0 => hϖB0 (hinj (by rw [map_zero]; exact h0))
  have hϖDm : ϖD ∈ maximalIdeal D := (IsLocalization.AtPrime.to_map_mem_maximal_iff D P ϖB).mpr hϖP

  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖD0 ht
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hk
      exact (IsLocalRing.mem_maximalIdeal _).mp hϖDm (hk ▸ u.isUnit)
    by_contra hk1
    have hk2 : 2 ≤ k := by omega
    obtain ⟨⟨p₁, s₁⟩, ht'⟩ := IsLocalization.mk'_surjective P.primeCompl t
    obtain ⟨⟨r₀, s₀⟩, hu'⟩ := IsLocalization.mk'_surjective P.primeCompl (u : D)
    simp only at ht' hu'
    have hr₀ : r₀ ∉ P := by
      have hu0 : IsUnit (IsLocalization.mk' D r₀ s₀) := by rw [hu']; exact u.isUnit
      exact (IsLocalization.AtPrime.isUnit_mk'_iff D P r₀ s₀).mp hu0

    have hrelD : IsLocalization.mk' D (r₀ * p₁ ^ k) (s₀ * s₁ ^ k) = ϖD := by
      rw [IsLocalization.mk'_mul, IsLocalization.mk'_pow, ht', hu', ← hk]
    have hrelB : r₀ * p₁ ^ k = ϖB * ((s₀ * s₁ ^ k : P.primeCompl) : ↥𝒩₀) := by
      have := IsLocalization.mk'_eq_iff_eq_mul.mp hrelD
      apply hinj
      rw [this, hϖD, ← map_mul]
    have hpow : (r₀ * p₁) ^ k ∈ Ideal.span {ϖB} := by
      have : (r₀ * p₁) ^ k = r₀ ^ (k - 1) * (r₀ * p₁ ^ k) := by
        rw [mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [this, hrelB]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hred _ _ hpow)

    have hp₁ : algebraMap ↥𝒩₀ D p₁ = t * algebraMap ↥𝒩₀ D s₁ := by
      rw [← ht']; exact (IsLocalization.mk'_spec D p₁ s₁).symm
    have hkk : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
    have hDrel : algebraMap ↥𝒩₀ D r₀ * algebraMap ↥𝒩₀ D s₁ * t =
        algebraMap ↥𝒩₀ D c * (u : D) * t ^ (k - 1) * t := by
      calc algebraMap ↥𝒩₀ D r₀ * algebraMap ↥𝒩₀ D s₁ * t
          = algebraMap ↥𝒩₀ D r₀ * algebraMap ↥𝒩₀ D p₁ := by rw [hp₁]; ring
        _ = algebraMap ↥𝒩₀ D (c * ϖB) := by rw [← map_mul, hc]
        _ = algebraMap ↥𝒩₀ D c * (u * t ^ k) := by rw [map_mul, ← hϖD, hk]
        _ = algebraMap ↥𝒩₀ D c * (u : D) * t ^ (k - 1) * t := by
            conv_lhs => rw [hkk, pow_succ]
            ring
    have hDrel' := mul_right_cancel₀ ht.ne_zero hDrel
    have hunitL : IsUnit (algebraMap ↥𝒩₀ D r₀ * algebraMap ↥𝒩₀ D s₁) :=
      ((IsLocalization.AtPrime.isUnit_to_map_iff D P r₀).mpr hr₀).mul
        ((IsLocalization.AtPrime.isUnit_to_map_iff D P (s₁ : ↥𝒩₀)).mpr s₁.2)
    have hmemR : algebraMap ↥𝒩₀ D c * (u : D) * t ^ (k - 1) ∈ maximalIdeal D :=
      Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal t).mpr ht.not_isUnit) _ (by omega))
    rw [← hDrel'] at hmemR
    exact (IsLocalRing.mem_maximalIdeal _).mp hmemR hunitL
  have hϖDirr : Irreducible ϖD := by
    have hassoc : Associated t ϖD := ⟨u, by rw [hk, hk1, pow_one, mul_comm]⟩
    exact hassoc.irreducible ht

  have ha0 : a ≠ 0 := by
    intro h0; apply hne
    have : (⟨e • (a : F), h⟩ : R.integers) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero]
  have haD0 : algebraMap ↥𝒩₀ D a ≠ 0 := fun h0 => ha0 (hinj (by rw [map_zero]; exact h0))
  obtain ⟨g, u', hg⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible haD0 hϖDirr
  obtain ⟨⟨r, s'⟩, hrs⟩ := IsLocalization.mk'_surjective P.primeCompl (u' : D)
  simp only at hrs
  have hr : r ∉ P := by
    have hu0 : IsUnit (IsLocalization.mk' D r s') := by rw [hrs]; exact u'.isUnit
    exact (IsLocalization.AtPrime.isUnit_mk'_iff D P r s').mp hu0
  have hfac : a * (s' : ↥𝒩₀) = ϖB ^ g * r := by
    apply hinj
    rw [map_mul, map_mul, map_pow, ← hϖD, hg, ← hrs, mul_right_comm, IsLocalization.mk'_spec, mul_comm]

  have hres_r : R.residue ⟨(r : F), h𝒩₀R r r.2⟩ ≠ 0 := hPres r hr
  have hres_s : R.residue ⟨((s' : ↥𝒩₀) : F), h𝒩₀R (s' : ↥𝒩₀) (s' : ↥𝒩₀).2⟩ ≠ 0 := hPres _ s'.2
  refine ⟨g, r, (s' : ↥𝒩₀), hres_r, hres_s, hfac, ?_⟩
  have he0 : e ≠ 0 := R.smul_const_ne_zero h hne
  have hw0 : e * ϖ ^ g ≠ 0 := mul_ne_zero he0 (pow_ne_zero _ hϖ0)
  have hrF0 : ((r : ↥𝒩₀) : F) ≠ 0 := by
    intro h0; apply hres_r
    have : (⟨(r : F), h𝒩₀R r r.2⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hfacF : ((a : ↥𝒩₀) : F) * ((s' : ↥𝒩₀) : F) = algebraMap L F ϖ ^ g * ((r : ↥𝒩₀) : F) := by
    have := congrArg Subtype.val hfac
    simpa [hϖB] using this

  have hw : algebraMap L F (e * ϖ ^ g) = (e • (a : F)) * ((s' : ↥𝒩₀) : F) * ((r : ↥𝒩₀) : F)⁻¹ := by
    rw [Algebra.smul_def, mul_assoc (algebraMap L F e), hfacF, map_mul, map_pow]
    field_simp
  have hwinv : (algebraMap L F (e * ϖ ^ g))⁻¹ = ((r : ↥𝒩₀) : F) * (e • (a : F))⁻¹ * (((s' : ↥𝒩₀) : F))⁻¹ := by
    rw [hw, mul_inv, mul_inv, inv_inv]; ring

  have hu_ea : IsUnit (⟨e • (a : F), h⟩ : R.integers) := R.isUnit_of_residue_ne_zero hne
  have hu_r : IsUnit (⟨(r : F), h𝒩₀R r r.2⟩ : R.integers) := R.isUnit_of_residue_ne_zero hres_r
  have hu_s : IsUnit (⟨((s' : ↥𝒩₀) : F), h𝒩₀R (s' : ↥𝒩₀) (s' : ↥𝒩₀).2⟩ : R.integers) :=
    R.isUnit_of_residue_ne_zero hres_s
  have hmemw : algebraMap L F (e * ϖ ^ g) ∈ R.integers := by
    rw [hw]
    exact mul_mem (mul_mem h (h𝒩₀R _ (s' : ↥𝒩₀).2))
      (inv_mem_of_isUnit R.integers _ hu_r)
  have hmemwinv : algebraMap L F (e * ϖ ^ g)⁻¹ ∈ R.integers := by
    rw [map_inv₀, hwinv]
    exact mul_mem (mul_mem (h𝒩₀R _ r.2) (inv_mem_of_isUnit R.integers _ hu_ea))
      (inv_mem_of_isUnit R.integers _ hu_s)
  have hA : e * ϖ ^ g ∈ A := (R.algebraMap_mem_iff _).mp hmemw
  have hAinv : (e * ϖ ^ g)⁻¹ ∈ A := (R.algebraMap_mem_iff _).mp hmemwinv
  refine ⟨hA, isUnit_iff_exists_inv.mpr ⟨⟨(e * ϖ ^ g)⁻¹, hAinv⟩, ?_⟩⟩
  apply Subtype.ext
  change (e * ϖ ^ g) * (e * ϖ ^ g)⁻¹ = 1
  exact mul_inv_cancel₀ hw0

end S_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel (solution)
