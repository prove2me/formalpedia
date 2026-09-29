-- Prove2me | solution 1 for AlgHom.bijective_and_exists_presentation_of_length_cotangent_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3bd8b03c-27ff-5e31-bae8-2174dc32da44

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Theorems.Thm_MvPowerSeries_quotient_mk_det_mem_of_ne_bot
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_surjective_of_apply_X_eq
import Theorems.Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient
import Theorems.Thm_Algebra_exists_presentation_of_residueField
import Theorems.Thm_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_bijective_and_exists_presentation_of_length_cotangent_le

universe u v w x

namespace FrobDictROWF

open MvPowerSeries

variable {k : Type u} [Field k] {n : ℕ}

noncomputable def xmon (𝔞 : Ideal (MvPowerSeries (Fin n) k)) (β : Fin n →₀ ℕ) :
    MvPowerSeries (Fin n) k ⧸ 𝔞 :=
  Ideal.Quotient.mk 𝔞 (monomial β (1 : k))

noncomputable def Sdeg (𝔞 : Ideal (MvPowerSeries (Fin n) k)) (D : ℕ) :
    Submodule k (MvPowerSeries (Fin n) k ⧸ 𝔞) :=
  Submodule.span k (xmon 𝔞 '' {β | (∀ i, β i ≤ 2) ∧ β.degree ≤ D})

noncomputable def S (𝔞 : Ideal (MvPowerSeries (Fin n) k)) :
    Submodule k (MvPowerSeries (Fin n) k ⧸ 𝔞) :=
  Submodule.span k (xmon 𝔞 '' {β | ∀ i, β i ≤ 2})

noncomputable def nn (𝔞 : Ideal (MvPowerSeries (Fin n) k)) :
    Ideal (MvPowerSeries (Fin n) k ⧸ 𝔞) :=
  Ideal.map (Ideal.Quotient.mk 𝔞)
    (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)))

section basic

variable (𝔞 : Ideal (MvPowerSeries (Fin n) k))

theorem xmon_add (β γ : Fin n →₀ ℕ) : xmon 𝔞 (β + γ) = xmon 𝔞 β * xmon 𝔞 γ := by
  simp only [xmon, ← map_mul, monomial_mul_monomial, mul_one]

theorem mk_X_pow (i : Fin n) (b : ℕ) :
    Ideal.Quotient.mk 𝔞 (X i) ^ b = xmon 𝔞 (Finsupp.single i b) := by
  rw [← map_pow, X_pow_eq]; rfl

theorem mk_X (i : Fin n) : Ideal.Quotient.mk 𝔞 (X i) = xmon 𝔞 (Finsupp.single i 1) := by
  rw [← mk_X_pow, pow_one]

theorem mk_smul (c : k) (p : MvPowerSeries (Fin n) k) :
    Ideal.Quotient.mk 𝔞 (c • p) = c • Ideal.Quotient.mk 𝔞 p :=
  map_smul (Ideal.Quotient.mkₐ k 𝔞) c p

theorem mk_monomial (β : Fin n →₀ ℕ) (c : k) :
    Ideal.Quotient.mk 𝔞 (monomial β c) = c • xmon 𝔞 β := by
  rw [xmon, ← mk_smul, ← map_smul, smul_eq_mul, mul_one]

theorem Sdeg_mono {D E : ℕ} (h : D ≤ E) : Sdeg 𝔞 D ≤ Sdeg 𝔞 E :=
  Submodule.span_mono (Set.image_mono fun _ hβ => ⟨hβ.1, hβ.2.trans h⟩)

theorem Sdeg_le_S (D : ℕ) : Sdeg 𝔞 D ≤ S 𝔞 :=
  Submodule.span_mono (Set.image_mono fun _ hβ => hβ.1)

theorem xmon_mem_Sdeg {β : Fin n →₀ ℕ} (h2 : ∀ i, β i ≤ 2) {D : ℕ} (hD : β.degree ≤ D) :
    xmon 𝔞 β ∈ Sdeg 𝔞 D :=
  Submodule.subset_span ⟨β, ⟨h2, hD⟩, rfl⟩

theorem finite_B2 : {β : Fin n →₀ ℕ | ∀ i, β i ≤ 2}.Finite := by
  refine (Finsupp.finite_of_degree_le (σ := Fin n) (2 * n)).subset fun β hβ => ?_
  simp only [Set.mem_setOf_eq] at hβ ⊢
  rw [Finsupp.degree_eq_sum]
  calc ∑ i, β i ≤ ∑ _i : Fin n, (2 : ℕ) := Finset.sum_le_sum fun i _ => hβ i
    _ = 2 * n := by simp [mul_comm]

theorem S_fg : (S 𝔞).FG :=
  Submodule.fg_def.mpr ⟨_, (finite_B2 (n := n)).image _, rfl⟩

end basic

section closure

variable (𝔞 : Ideal (MvPowerSeries (Fin n) k)) {r : Fin n → MvPowerSeries (Fin n) k}
  (hr : ∀ i, r i ∈ Submodule.span k
    (Set.range (fun j : Fin n => (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) ∪
      Set.range (fun jl : Fin n × Fin n =>
        (MvPowerSeries.X jl.1 * MvPowerSeries.X jl.2 : MvPowerSeries (Fin n) k))))
  (hcube : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ 3 - r i ∈ 𝔞)
include hr hcube

theorem X_mul_mem_Sdeg (D : ℕ) :
    ∀ i, ∀ s ∈ Sdeg 𝔞 D, Ideal.Quotient.mk 𝔞 (X i) * s ∈ Sdeg 𝔞 (D + 1) := by
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro i
  suffices H : Sdeg 𝔞 D ≤ (Sdeg 𝔞 (D + 1)).comap (LinearMap.mulLeft k (Ideal.Quotient.mk 𝔞 (X i)))
    from fun s hs => H hs
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨β, ⟨hβ2, hβD⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
  rcases Nat.lt_or_ge (β i) 2 with hlt | hge
  ·
    rw [mk_X, ← xmon_add]
    refine xmon_mem_Sdeg 𝔞 (fun j => ?_) ?_
    · rw [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with hij
      · subst hij; omega
      · simpa using hβ2 j
    · rw [map_add, Finsupp.degree_single]; omega
  ·
    have hβi : β i = 2 := le_antisymm (hβ2 i) hge
    set γ : Fin n →₀ ℕ := Finsupp.erase i β with hγ
    have hβγ : β = Finsupp.single i 2 + γ := by rw [← hβi, hγ, Finsupp.single_add_erase]
    have hγ2 : ∀ j, γ j ≤ 2 := by
      intro j
      classical
      rw [hγ, Finsupp.erase_apply]
      split_ifs
      · exact Nat.zero_le _
      · exact hβ2 j
    have hdeg : γ.degree + 2 ≤ D := by
      have : β.degree = 2 + γ.degree := by rw [hβγ, map_add, Finsupp.degree_single]
      omega
    have e1 : Ideal.Quotient.mk 𝔞 (X i) * xmon 𝔞 β = Ideal.Quotient.mk 𝔞 (r i) * xmon 𝔞 γ := by
      have h3 : Ideal.Quotient.mk 𝔞 (X i ^ 3) = Ideal.Quotient.mk 𝔞 (r i) :=
        Ideal.Quotient.eq.mpr (hcube i)
      rw [hβγ, xmon_add, ← mul_assoc, ← mk_X_pow, ← pow_succ', ← map_pow, h3]
    rw [e1]
    have hD1 : γ.degree < D := by omega
    have hD2 : γ.degree + 1 < D := by omega
    let f : MvPowerSeries (Fin n) k →ₗ[k] MvPowerSeries (Fin n) k ⧸ 𝔞 :=
      (LinearMap.mulRight k (xmon 𝔞 γ)).comp (Ideal.Quotient.mkₐ k 𝔞).toLinearMap
    have hf : ∀ p, f p = Ideal.Quotient.mk 𝔞 p * xmon 𝔞 γ := fun p => rfl
    have hle : Submodule.span k
        (Set.range (fun j : Fin n => (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) ∪
          Set.range (fun jl : Fin n × Fin n =>
            (MvPowerSeries.X jl.1 * MvPowerSeries.X jl.2 : MvPowerSeries (Fin n) k))) ≤
        (Sdeg 𝔞 (D + 1)).comap f := by
      refine Submodule.span_le.mpr ?_
      rintro _ (⟨j, rfl⟩ | ⟨jl, rfl⟩)
      · simp only [SetLike.mem_coe, Submodule.mem_comap, hf]
        exact Sdeg_mono 𝔞 (by omega) (ih _ hD1 j _ (xmon_mem_Sdeg 𝔞 hγ2 le_rfl))
      · simp only [SetLike.mem_coe, Submodule.mem_comap, hf, map_mul, mul_assoc]
        exact Sdeg_mono 𝔞 (by omega)
          (ih _ hD2 jl.1 _ (ih _ hD1 jl.2 _ (xmon_mem_Sdeg 𝔞 hγ2 le_rfl)))
    simpa only [Submodule.mem_comap, hf] using hle (hr i)

theorem X_mul_mem_S (i : Fin n) {s : MvPowerSeries (Fin n) k ⧸ 𝔞} (hs : s ∈ S 𝔞) :
    Ideal.Quotient.mk 𝔞 (X i) * s ∈ S 𝔞 := by
  have H : S 𝔞 ≤ (S 𝔞).comap (LinearMap.mulLeft k (Ideal.Quotient.mk 𝔞 (X i))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨β, hβ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact Sdeg_le_S 𝔞 _ (X_mul_mem_Sdeg 𝔞 hr hcube _ i _ (xmon_mem_Sdeg 𝔞 hβ le_rfl))
  exact H hs

theorem X_pow_mul_mem_S (i : Fin n) (b : ℕ) {s : MvPowerSeries (Fin n) k ⧸ 𝔞} (hs : s ∈ S 𝔞) :
    Ideal.Quotient.mk 𝔞 (X i) ^ b * s ∈ S 𝔞 := by
  induction b with
  | zero => simpa using hs
  | succ b ih =>
    rw [pow_succ', mul_assoc]
    exact X_mul_mem_S 𝔞 hr hcube i ih

theorem xmon_mem_S (m : Fin n →₀ ℕ) : xmon 𝔞 m ∈ S 𝔞 := by
  induction m using Finsupp.induction with
  | zero => exact Submodule.subset_span ⟨0, fun _ => Nat.zero_le _, rfl⟩
  | single_add a b f _ _ ih =>
    rw [xmon_add, ← mk_X_pow]
    exact X_pow_mul_mem_S 𝔞 hr hcube a b ih

theorem approx (h : MvPowerSeries (Fin n) k) (N : ℕ) :
    ∃ s ∈ S 𝔞, Ideal.Quotient.mk 𝔞 h - s ∈ nn 𝔞 ^ N := by
  classical
  set B := (Finsupp.finite_of_degree_lt (σ := Fin n) N).toFinset with hB
  have hmemB : ∀ m : Fin n →₀ ℕ, m ∈ B ↔ m.degree < N := fun m => by
    simp [hB]
  set t : MvPowerSeries (Fin n) k := ∑ m ∈ B, monomial m (coeff m h) with ht
  refine ⟨Ideal.Quotient.mk 𝔞 t, ?_, ?_⟩
  · rw [ht, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [mk_monomial]
    exact Submodule.smul_mem _ _ (xmon_mem_S 𝔞 hr hcube m)
  · rw [← map_sub]
    have hmem : h - t ∈
        Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)) ^ N := by
      apply MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero
      intro m hm
      rw [map_sub, ht, map_sum]
      simp_rw [coeff_monomial]
      rw [Finset.sum_ite_eq, if_pos ((hmemB m).mpr hm), sub_self]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk 𝔞) hmem
    rwa [Ideal.map_pow] at this

end closure

theorem nn_ne_top (𝔞 : Ideal (MvPowerSeries (Fin n) k)) (h𝔞 : 𝔞 ≠ ⊤) : nn 𝔞 ≠ ⊤ := by
  intro H
  have h1 : (1 : MvPowerSeries (Fin n) k ⧸ 𝔞) ∈ nn 𝔞 := H ▸ Submodule.mem_top
  obtain ⟨p, hp, hp1⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective).mp h1
  have hcc : constantCoeff p = 0 := by
    have hle : Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)) ≤
        RingHom.ker (constantCoeff : MvPowerSeries (Fin n) k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    exact hle hp
  apply h𝔞
  have hp1' : p - 1 ∈ 𝔞 := Ideal.Quotient.eq.mp (by rw [hp1, map_one])
  refine Ideal.eq_top_of_isUnit_mem 𝔞 hp1' ?_
  rw [isUnit_iff_constantCoeff, map_sub, map_one, hcc, zero_sub]
  exact isUnit_one.neg

theorem finite_quotient_of_cubes {k : Type u} [Field k] {n : ℕ} (𝔞 : Ideal (MvPowerSeries (Fin n) k))
    (r : Fin n → MvPowerSeries (Fin n) k)
    (hr : ∀ i, r i ∈ Submodule.span k
      (Set.range (fun j : Fin n => (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) ∪
        Set.range (fun jl : Fin n × Fin n => (MvPowerSeries.X jl.1 * MvPowerSeries.X jl.2 : MvPowerSeries (Fin n) k))))
    (hcube : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ 3 - r i ∈ 𝔞) :
    Module.Finite k (MvPowerSeries (Fin n) k ⧸ 𝔞) := by
  classical
  by_cases htop : 𝔞 = ⊤
  · haveI : Subsingleton (MvPowerSeries (Fin n) k ⧸ 𝔞) := Ideal.Quotient.subsingleton_iff.mpr htop
    infer_instance
  haveI : Nontrivial (MvPowerSeries (Fin n) k ⧸ 𝔞) := Ideal.Quotient.nontrivial_iff.mpr htop
  haveI : IsLocalRing (MvPowerSeries (Fin n) k ⧸ 𝔞) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (MvPowerSeries (Fin n) k) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsNoetherianRing (MvPowerSeries (Fin n) k ⧸ 𝔞) := inferInstance

  have hKrull : ⨅ N : ℕ, nn 𝔞 ^ N = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (nn 𝔞) (nn_ne_top 𝔞 htop)

  haveI : IsArtinian k (S 𝔞) := isArtinian_of_fg_of_artinian _ (S_fg 𝔞)
  let c : ℕ → Submodule k (S 𝔞) := fun N =>
    Submodule.comap (S 𝔞).subtype ((nn 𝔞 ^ N).restrictScalars k)
  have hc : ∀ {a b : ℕ}, a ≤ b → c b ≤ c a := fun hab =>
    Submodule.comap_mono fun x hx => Ideal.pow_le_pow_right hab hx
  obtain ⟨N₀, hN₀⟩ := IsArtinian.monotone_stabilizes
    (⟨fun N => OrderDual.toDual (c N), fun a b hab => OrderDual.toDual_le_toDual.mpr (hc hab)⟩ :
      ℕ →o (Submodule k (S 𝔞))ᵒᵈ)
  have key : ∀ N, N₀ ≤ N → ∀ s ∈ S 𝔞, s ∈ nn 𝔞 ^ N₀ → s ∈ nn 𝔞 ^ N := by
    intro N hN s hs hs0
    have e : c N₀ = c N := congrArg OrderDual.ofDual (hN₀ N hN)
    have hmem : (⟨s, hs⟩ : S 𝔞) ∈ c N₀ := hs0
    rw [e] at hmem
    exact hmem

  have hS : S 𝔞 = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s₀, hs₀S, hs₀⟩ := approx 𝔞 hr hcube h N₀
    suffices hz : Ideal.Quotient.mk 𝔞 h - s₀ = 0 by
      rw [sub_eq_zero] at hz; rw [hz]; exact hs₀S
    rw [← Ideal.mem_bot, ← hKrull, Submodule.mem_iInf]
    intro N
    obtain ⟨s₁, hs₁S, hs₁⟩ := approx 𝔞 hr hcube h (N₀ + N)
    have h10 : s₁ - s₀ ∈ nn 𝔞 ^ N₀ := by
      have : s₁ - s₀ = (Ideal.Quotient.mk 𝔞 h - s₀) - (Ideal.Quotient.mk 𝔞 h - s₁) := by ring
      rw [this]
      exact sub_mem hs₀ (Ideal.pow_le_pow_right (Nat.le_add_right N₀ N) hs₁)
    have h11 : s₁ - s₀ ∈ nn 𝔞 ^ (N₀ + N) :=
      key _ (Nat.le_add_right N₀ N) _ (sub_mem hs₁S hs₀S) h10
    have : Ideal.Quotient.mk 𝔞 h - s₀ = (Ideal.Quotient.mk 𝔞 h - s₁) + (s₁ - s₀) := by ring
    rw [this]
    exact Ideal.pow_le_pow_right (Nat.le_add_left N N₀) (add_mem hs₁ h11)
  exact Module.finite_def.mpr (hS ▸ S_fg 𝔞)

end FrobDictROWF

open IsLocalRing MvPowerSeries

namespace FrobDictROWF

section PS

variable {k : Type u} [Field k] {n : ℕ}

local notation "P" => MvPowerSeries (Fin n) k
local notation "IX" => Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k))

theorem sub_C_constantCoeff_mem_span_X (p : P) :
    p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈ IX := by
  have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p))
    (fun m hm => by
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
      subst hm0
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  rwa [pow_one] at h

theorem X_mem_maximalIdeal (i : Fin n) : (MvPowerSeries.X i : P) ∈ maximalIdeal P := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem span_X_le_maximalIdeal : IX ≤ maximalIdeal P :=
  Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact X_mem_maximalIdeal i)

theorem C_eq_algebraMap (c : k) : (MvPowerSeries.C c : P) = algebraMap k P c := by
  rw [MvPowerSeries.algebraMap_apply]; rfl

end PS

section Main

variable {k : Type u} {R : Type v} {T : Type w} [Field k]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  [CommRing T] [Algebra k T] [Module.Finite k T]

omit [Module.Finite k T] in
theorem main' (φ : R →ₐ[k] T) (hφ : Function.Surjective φ) (πR : R →ₐ[k] k) (πT : T →ₐ[k] k)
    (hπ : πT.comp φ = πR) {n : ℕ} (a : Fin n → R) (ha : Ideal.span (Set.range a) = RingHom.ker πR)
    (hspan : (RingHom.ker πT).restrictScalars k ≤ Submodule.span k (Set.range (φ ∘ a)))
    (V : Matrix (Fin n) (Fin n) R) (hV : V.mulVec a = 0) (hdet : φ V.det ≠ 0) :
    Function.Bijective φ ∧
      ∃ f : Fin n → MvPowerSeries (Fin n) k,
        Nonempty ((MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T) := by
  classical
  haveI : Nontrivial T := nontrivial_of_ne _ _ hdet

  have hπ' : ∀ r, πT (φ r) = πR r := fun r => congr($hπ r)
  have hkerR : RingHom.ker πR ≠ ⊤ := fun h => by
    have : (1 : R) ∈ RingHom.ker πR := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have ha_mem : ∀ i, a i ∈ maximalIdeal R := fun i =>
    IsLocalRing.le_maximalIdeal hkerR (ha ▸ Ideal.subset_span ⟨i, rfl⟩)
  have ha_ker : ∀ i, πR (a i) = 0 := fun i => by
    have : a i ∈ RingHom.ker πR := ha ▸ Ideal.subset_span ⟨i, rfl⟩
    exact this

  obtain ⟨Ψ, hΨ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin n) (𝒪 := k) (maximalIdeal R) a ha_mem
  have h𝒪 : Function.Surjective
      (⇑(Ideal.Quotient.mk (Ideal.span (Set.range a))) ∘ ⇑(algebraMap k R)) := fun q => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨πR r, ?_⟩
    change Ideal.Quotient.mk _ (algebraMap k R (πR r)) = Ideal.Quotient.mk _ r
    rw [Ideal.Quotient.eq, ha, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
    rfl
  have hΨsurj : Function.Surjective Ψ := MvPowerSeries.algHom_surjective_of_apply_X_eq Ψ a hΨ ha_mem h𝒪

  set Θ : MvPowerSeries (Fin n) k →ₐ[k] T := φ.comp Ψ with hΘdef
  have hΘ : ∀ h, Θ h = φ (Ψ h) := fun h => rfl
  have hΘsurj : Function.Surjective Θ := hφ.comp hΨsurj
  have hΘX : ∀ i, Θ (MvPowerSeries.X i) = φ (a i) := fun i => by rw [hΘ, hΨ]
  set JR : Ideal (MvPowerSeries (Fin n) k) := RingHom.ker Ψ with hJRdef
  set JT : Ideal (MvPowerSeries (Fin n) k) := RingHom.ker Θ with hJTdef
  have hJRT : JR ≤ JT := fun h hh => by
    change Θ h = 0
    rw [hΘ, show Ψ h = 0 from hh, map_zero]
  set I : Ideal (MvPowerSeries (Fin n) k) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)) with hIdef
  have hΘC : ∀ c : k, Θ (MvPowerSeries.C c) = algebraMap k T c := fun c => by
    rw [C_eq_algebraMap, AlgHom.commutes]
  have hImap : I.map Θ ≤ RingHom.ker πT := by
    rw [hIdef, Ideal.map_span, ← Set.range_comp]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change πT (Θ (MvPowerSeries.X i)) = 0
    rw [hΘX, hπ', ha_ker]
  have hJTI : JT ≤ I := fun h hh => by
    have hh' : Θ h = 0 := hh
    have hsplit := sub_C_constantCoeff_mem_span_X h
    have h0 : MvPowerSeries.constantCoeff h = 0 := by
      have h1 : πT (Θ (h - MvPowerSeries.C (MvPowerSeries.constantCoeff h))) = 0 :=
        hImap (Ideal.mem_map_of_mem _ hsplit)
      rwa [map_sub, hh', zero_sub, map_neg, hΘC, AlgHom.commutes, neg_eq_zero] at h1
    rw [h0, map_zero, sub_zero] at hsplit
    exact hsplit

  choose Gt hGt using fun i j => hΨsurj (V i j)
  have hrow : ∀ i, ∑ j, Gt i j * MvPowerSeries.X j ∈ JR := fun i => by
    change Ψ (∑ j, Gt i j * MvPowerSeries.X j) = 0
    simp only [map_sum, map_mul, hGt, hΨ]
    exact congr_fun hV i
  have hdetT : Θ (Matrix.det (Matrix.of Gt)) ≠ 0 := by
    have : ((Matrix.of Gt).map Ψ) = V := by
      ext i j; exact hGt i j
    rw [hΘ, AlgHom.map_det, AlgHom.mapMatrix_apply, this]
    exact hdet

  let V12 : Submodule k (MvPowerSeries (Fin n) k) := Submodule.span k
      (Set.range (fun j : Fin n => (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) ∪
        Set.range (fun jl : Fin n × Fin n =>
          (MvPowerSeries.X jl.1 * MvPowerSeries.X jl.2 : MvPowerSeries (Fin n) k)))
  have hCsmul : ∀ (c : k) (m : MvPowerSeries (Fin n) k), MvPowerSeries.C c * m = c • m := fun c m => by
    rw [C_eq_algebraMap, Algebra.smul_def]
  have hIV : ∀ h ∈ I, ∃ c : Fin n → k, h - ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i ∈ JT := by
    intro h hh
    have h1 : Θ h ∈ (RingHom.ker πT).restrictScalars k := hImap (Ideal.mem_map_of_mem _ hh)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (hspan h1)
    refine ⟨c, ?_⟩
    change Θ (h - ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = 0
    rw [map_sub, map_sum, sub_eq_zero, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hΘC, hΘX, ← Algebra.smul_def]
    rfl
  have hXI : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hKEY : ∀ h ∈ I, ∃ r ∈ V12, h - r ∈ I * JT := by
    intro h hh
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries (Fin n) k)).mp hh
    have hsplit : ∀ i, ∃ (c0 : k) (c : Fin n → k) (j : MvPowerSeries (Fin n) k), j ∈ JT ∧
        u i = MvPowerSeries.C c0 + ∑ l, MvPowerSeries.C (c l) * MvPowerSeries.X l + j := by
      intro i
      obtain ⟨c, hc⟩ := hIV _ (sub_C_constantCoeff_mem_span_X (u i))
      exact ⟨_, c, _, hc, by ring⟩
    choose c0 c j hj hu_eq using hsplit
    refine ⟨∑ i, (MvPowerSeries.C (c0 i) * MvPowerSeries.X i +
      (∑ l, MvPowerSeries.C (c i l) * MvPowerSeries.X l) * MvPowerSeries.X i), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_
      · rw [hCsmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      · rw [Finset.sum_mul]
        refine Submodule.sum_mem _ fun l _ => ?_
        rw [mul_assoc, hCsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨(l, i), rfl⟩))
    · have hcalc : h - ∑ i, (MvPowerSeries.C (c0 i) * MvPowerSeries.X i +
          (∑ l, MvPowerSeries.C (c i l) * MvPowerSeries.X l) * MvPowerSeries.X i) =
            ∑ i, j i * MvPowerSeries.X i := by
        rw [← hu, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_eq_mul, hu_eq i]
        ring
      rw [hcalc, mul_comm]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hj i) (hXI i)

  have hGX_I : ∀ i, ∑ j, Gt i j * MvPowerSeries.X j ∈ I := fun i =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hXI j)
  have hX3_I : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ 3 ∈ I := fun i => by
    rw [pow_succ]; exact Ideal.mul_mem_left _ _ (hXI i)
  choose p hpV hp using fun i => hKEY _ (hGX_I i)
  choose q hqV hq using fun i => hKEY _ (hX3_I i)
  let f : Fin n → MvPowerSeries (Fin n) k := fun i => MvPowerSeries.X i ^ 3 - q i + p i
  have hf_def : ∀ i, f i = MvPowerSeries.X i ^ 3 - q i + p i := fun i => rfl
  have hIJT_le : I * JT ≤ JT := Ideal.mul_le_right
  have hf_JT : ∀ i, f i ∈ JT := fun i => by
    have h1 : MvPowerSeries.X i ^ 3 - q i ∈ JT := hIJT_le (hq i)
    have h2 : p i ∈ JT := by
      have : p i = ∑ j, Gt i j * MvPowerSeries.X j - (∑ j, Gt i j * MvPowerSeries.X j - p i) := by ring
      rw [this]; exact JT.sub_mem (hJRT (hrow i)) (hIJT_le (hp i))
    rw [hf_def]; exact JT.add_mem h1 h2
  have h𝔞JT : Ideal.span (Set.range f) ≤ JT := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf_JT i)
  haveI hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    finite_quotient_of_cubes _ (fun i => q i - p i) (fun i => V12.sub_mem (hqV i) (hpV i))
      (fun i => by
        have : MvPowerSeries.X i ^ 3 - (q i - p i) = f i := by rw [hf_def]; ring
        rw [this]; exact Ideal.subset_span ⟨i, rfl⟩)

  have hdiff : ∀ i, f i - ∑ j, Gt i j * MvPowerSeries.X j ∈ JT • I := fun i => by
    have : f i - ∑ j, Gt i j * MvPowerSeries.X j =
        (MvPowerSeries.X i ^ 3 - q i) + -(∑ j, Gt i j * MvPowerSeries.X j - p i) := by rw [hf_def]; ring
    rw [Ideal.smul_eq_mul, mul_comm, this]
    exact (I * JT).add_mem (hq i) ((I * JT).neg_mem (hp i))
  choose e he he' using fun i =>
    (Submodule.mem_ideal_smul_span_iff_exists_sum JT (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)
      _).mp (hdiff i)
  let G : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k) := Matrix.of fun i j => Gt i j + e i j
  have hfG : ∀ i, f i = ∑ j, G i j * MvPowerSeries.X j := fun i => by
    have h1 : ((e i).sum fun j c => c • MvPowerSeries.X j) = ∑ j, e i j * MvPowerSeries.X j := by
      rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
      simp only [smul_eq_mul]
    have h2 := he' i
    rw [h1] at h2
    simp only [G, Matrix.of_apply, add_mul, Finset.sum_add_distrib]
    rw [h2]; ring
  have hGmod : ∀ i j, G i j - Gt i j ∈ JT := fun i j => by
    simp only [G, Matrix.of_apply, add_sub_cancel_left]; exact he i j

  obtain ⟨-, hsoc⟩ := MvPowerSeries.quotient_mk_det_mem_of_ne_bot G f hfG
  have hdetG : G.det - (Matrix.of Gt).det ∈ JT := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    exact Ideal.Quotient.eq.mpr (hGmod i j)
  have hJT𝔞 : JT ≤ Ideal.span (Set.range f) := by
    rw [← Ideal.mk_ker (I := Ideal.span (Set.range f)), ← Ideal.map_eq_bot_iff_le_ker]
    by_contra hne
    have hmem := hsoc _ hne
    obtain ⟨y, hy, hy'⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (Ideal.span (Set.range f)))
      Ideal.Quotient.mk_surjective).mp hmem
    have h1 : y - G.det ∈ Ideal.span (Set.range f) := by rw [← Ideal.Quotient.eq, hy']
    have h2 : G.det ∈ JT := by
      have := JT.sub_mem hy (h𝔞JT h1); rwa [sub_sub_cancel] at this
    have h3 : (Matrix.of Gt).det ∈ JT := by
      have := JT.sub_mem h2 hdetG; rwa [sub_sub_cancel] at this
    exact hdetT h3
  have hJTeq : JT = Ideal.span (Set.range f) := le_antisymm hJT𝔞 h𝔞JT

  haveI : IsNoetherianRing (MvPowerSeries (Fin n) k) := MvPowerSeries.isNoetherianRing_of_finite
  have hJTfg : JT.FG := IsNoetherian.noetherian JT
  have hIjac : I ≤ (⊥ : Ideal (MvPowerSeries (Fin n) k)).jacobson :=
    span_X_le_maximalIdeal.trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have h𝔞le : Ideal.span (Set.range f) ≤ JR ⊔ I • JT := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, Gt i j * MvPowerSeries.X j +
        ((MvPowerSeries.X i ^ 3 - q i) + -(∑ j, Gt i j * MvPowerSeries.X j - p i)) := by rw [hf_def]; ring
    rw [SetLike.mem_coe, this]
    refine Submodule.add_mem_sup (hrow i) ?_
    rw [Ideal.smul_eq_mul]
    exact (I * JT).add_mem (hq i) ((I * JT).neg_mem (hp i))
  have hNN : JT ≤ JR ⊔ I • JT := fun y hy => h𝔞le (hJT𝔞 hy)
  have hJTR : JT ≤ JR := Submodule.le_of_le_smul_of_le_jacobson_bot hJTfg hIjac hNN
  have hJeq : JT = JR := le_antisymm hJTR hJRT

  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨h, rfl⟩ := hΨsurj r
    have : h ∈ JT := by change Θ h = 0; rw [hΘ, hr]
    rw [hJeq] at this
    exact this
  refine ⟨⟨hinj, hφ⟩, f, ⟨?_⟩⟩
  have hker : RingHom.ker Θ = Ideal.span (Set.range f) := hJTeq
  exact (Ideal.quotientEquivAlgOfEq k hker).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hΘsurj)

end Main

section Final

variable {k : Type u} {R : Type v} {T : Type w} [Field k]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  [CommRing T] [Algebra k T] [Module.Finite k T]

theorem final (φ : R →ₐ[k] T) (hφ : Function.Surjective φ) (πR : R →ₐ[k] k) (πT : T →ₐ[k] k)
    (hπ : πT.comp φ = πR) {n : ℕ} (a : Fin n → R) (ha : Ideal.span (Set.range a) = RingHom.ker πR)
    (V : Matrix (Fin n) (Fin n) R) (hV : V.mulVec a = 0) (hdet : φ V.det ≠ 0) :
    Function.Bijective φ ∧
      ∃ (m : ℕ) (f : Fin m → MvPowerSeries (Fin m) k),
        Nonempty ((MvPowerSeries (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T) := by
  classical
  have hπ' : ∀ r, πT (φ r) = πR r := fun r => congr($hπ r)

  obtain ⟨s, b, hb⟩ := Module.Finite.exists_fin (R := k) (M := T)
  let ub : Fin s → T := fun l => b l - algebraMap k T (πT (b l))
  have hub_ker : ∀ l, πT (ub l) = 0 := fun l => by
    simp only [ub, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hub_span : (RingHom.ker πT).restrictScalars k ≤ Submodule.span k (Set.range ub) := by
    intro t ht
    have ht0 : πT t = 0 := ht
    have htb : t ∈ Submodule.span k (Set.range b) := hb ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp htb
    have hsum : ∑ l, c l • ub l = t := by
      have h1 : ∀ l, c l • ub l = c l • b l - algebraMap k T (c l * πT (b l)) := fun l => by
        simp only [ub, map_mul, Algebra.smul_def, mul_sub]
      have h2 : ∑ l, c l * πT (b l) = πT t := by
        rw [← hc, map_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
      simp only [h1, Finset.sum_sub_distrib, ← map_sum, h2, ht0, map_zero, sub_zero, hc]
    rw [← hsum]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

  choose w hw using fun l => hφ (ub l)
  have hw_ker : ∀ l, w l ∈ Ideal.span (Set.range a) := fun l => by
    rw [ha]; change πR (w l) = 0; rw [← hπ', hw, hub_ker]
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun R).mp (hw_ker l)

  let aS : Fin n ⊕ Fin s → R := Sum.elim a w
  let CS : Matrix (Fin s) (Fin n) R := Matrix.of fun l j => c l j
  let VS : Matrix (Fin n ⊕ Fin s) (Fin n ⊕ Fin s) R := Matrix.fromBlocks V 0 (-CS) 1
  have hVS : VS.mulVec aS = 0 := by
    rw [Matrix.fromBlocks_mulVec]
    have h1 : aS ∘ Sum.inl = a := rfl
    have h2 : aS ∘ Sum.inr = w := rfl
    rw [h1, h2, hV, Matrix.zero_mulVec, add_zero, Matrix.one_mulVec, Matrix.neg_mulVec]
    have h3 : CS.mulVec a = w := by
      funext l
      simp only [Matrix.mulVec, dotProduct, CS, Matrix.of_apply]
      rw [← hc l]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]
    rw [h3, neg_add_cancel]
    funext x; cases x <;> rfl
  have hVSdet : VS.det = V.det := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  let eq : Fin n ⊕ Fin s ≃ Fin (n + s) := finSumFinEquiv
  let a' : Fin (n + s) → R := aS ∘ eq.symm
  let V' : Matrix (Fin (n + s)) (Fin (n + s)) R := Matrix.reindex eq eq VS
  have hV' : V'.mulVec a' = 0 := by
    change (VS.submatrix eq.symm eq.symm).mulVec (aS ∘ eq.symm) = 0
    rw [Matrix.submatrix_mulVec_equiv]
    have : (aS ∘ ⇑eq.symm) ∘ ⇑eq.symm.symm = aS := by
      funext i; simp
    rw [this, hVS]
    rfl
  have hdet' : φ V'.det ≠ 0 := by
    change φ (Matrix.reindex eq eq VS).det ≠ 0
    rwa [Matrix.det_reindex_self, hVSdet]
  have hrange : Set.range a' = Set.range a ∪ Set.range w := by
    change Set.range (aS ∘ ⇑eq.symm) = _
    rw [eq.symm.surjective.range_comp]
    exact Set.Sum.elim_range a w
  have ha' : Ideal.span (Set.range a') = RingHom.ker πR := by
    rw [hrange, Ideal.span_union, ha, sup_eq_left]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    exact ha ▸ hw_ker l
  have hspan' : (RingHom.ker πT).restrictScalars k ≤ Submodule.span k (Set.range (φ ∘ a')) := by
    refine hub_span.trans (Submodule.span_mono ?_)
    rintro _ ⟨l, rfl⟩
    refine ⟨eq (Sum.inr l), ?_⟩
    simp only [Function.comp_apply, a', Equiv.symm_apply_apply, aS, Sum.elim_inr, hw]
  obtain ⟨hbij, f, hf⟩ := main' φ hφ πR πT hπ a' ha' hspan' V' hV' hdet'
  exact ⟨hbij, n + s, f, hf⟩

end Final

end FrobDictROWF

theorem ROWF.bijective_and_exists_presentation_of_apply_det_ne_zero
    {k : Type u} {R : Type v} {T : Type w} [Field k]
    [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing T] [Algebra k T] [Module.Finite k T]
    (φ : R →ₐ[k] T) (hφ : Function.Surjective φ) (πR : R →ₐ[k] k) (πT : T →ₐ[k] k)
    (hπ : πT.comp φ = πR) {n : ℕ} (a : Fin n → R) (ha : Ideal.span (Set.range a) = RingHom.ker πR)
    (V : Matrix (Fin n) (Fin n) R) (hV : V.mulVec a = 0) (hdet : φ V.det ≠ 0) :
    Function.Bijective φ ∧
      ∃ (m : ℕ) (f : Fin m → MvPowerSeries (Fin m) k),
        Nonempty ((MvPowerSeries (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T) :=
  FrobDictROWF.final φ hφ πR πT hπ a ha V hV hdet

open IsLocalRing Module
open scoped Matrix

namespace FrobDictCRIT

section LengthPID

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]

theorem length_quotient_span_mul (a b : 𝒪) (hb : b ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {a * b}) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {a}) + Module.length 𝒪 (𝒪 ⧸ Ideal.span {b}) := by

  let f : (𝒪 ⧸ Ideal.span {a}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {a * b}) :=
    Submodule.mapQ (Ideal.span {a}) (Ideal.span {a * b}) (LinearMap.lsmul 𝒪 𝒪 b) (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      change b • (c * a) ∈ Ideal.span {a * b}
      exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [smul_eq_mul]; ring⟩)
  let g : (𝒪 ⧸ Ideal.span {a * b}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {b}) :=
    Submodule.mapQ (Ideal.span {a * b}) (Ideal.span {b}) LinearMap.id (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton'.mpr ⟨c * a, by simp [mul_assoc]⟩)
  have hfx : ∀ x : 𝒪, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b * x) := fun x => rfl
  have hgx : ∀ x : 𝒪, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hfx, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    have : x = c * a := by
      have h1 : b * x = b * (c * a) := by rw [← hc]; ring
      exact mul_left_cancel₀ hb h1
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton'.mpr ⟨c, this.symm⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, hgx y⟩
  have hfg : Function.Exact f g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      rw [hgx, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨Submodule.Quotient.mk c, by rw [hfx]; exact congrArg _ (mul_comm b c)⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hfx] at hx
      rw [← hx, hgx, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_comm]⟩
  rw [Module.length_eq_add_of_exact f g hf hg hfg]

theorem length_quotient_span_prod {ι : Type x} (s : Finset ι) (a : ι → 𝒪) (ha : ∀ i ∈ s, a i ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i ∈ s, a i}) =
      ∑ i ∈ s, Module.length 𝒪 (𝒪 ⧸ Ideal.span {a i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Module.length_eq_zero_iff.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, Finset.prod_empty]
    exact Ideal.span_singleton_one
  | insert j s hj ih =>
    have e := Submodule.quotEquivOfEq (Ideal.span {∏ i ∈ insert j s, a i})
      (Ideal.span {(∏ i ∈ s, a i) * a j}) (by rw [Finset.prod_insert hj, mul_comm])
    rw [e.length_eq, Finset.sum_insert hj,
      length_quotient_span_mul _ _ (ha j (Finset.mem_insert_self j s)), add_comm,
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]

end LengthPID

section DVR

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem length_residue (ϖ : 𝒪) (hϖ : Irreducible ϖ) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) = 1 := by
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]; infer_instance
  haveI : IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨Ideal.span {ϖ}, hmax, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one 𝒪 _

theorem length_quotient_span_pow (ϖ : 𝒪) (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {ϖ ^ k}) = k := by
  have hk : ϖ ^ k = ∏ _i ∈ Finset.range k, ϖ := by rw [Finset.prod_const, Finset.card_range]
  rw [hk, length_quotient_span_prod _ _ (fun _ _ => hϖ.ne_zero)]
  simp [length_residue ϖ hϖ]

theorem le_of_length_le {J₁ J₂ : Ideal 𝒪} (h₁ : J₁ ≠ ⊥) (h₂ : J₂ ≠ ⊥)
    (hle : Module.length 𝒪 (𝒪 ⧸ J₁) ≤ Module.length 𝒪 (𝒪 ⧸ J₂)) : J₂ ≤ J₁ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  obtain ⟨k₁, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h₁ hϖ
  obtain ⟨k₂, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h₂ hϖ
  rw [length_quotient_span_pow ϖ hϖ, length_quotient_span_pow ϖ hϖ, Nat.cast_le] at hle
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hle)

theorem length_quotient_ne_top {J : Ideal 𝒪} (hJ : J ≠ ⊥) : Module.length 𝒪 (𝒪 ⧸ J) ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  obtain ⟨k, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  rw [length_quotient_span_pow ϖ hϖ]
  exact ENat.coe_ne_top k

theorem length_self_eq_top : Module.length 𝒪 𝒪 = ⊤ := by
  by_contra h
  have hfl := Module.length_ne_top_iff.mp h
  obtain ⟨-, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI : IsArtinianRing 𝒪 := hart
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  exact hϖ.not_isUnit (IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))

end DVR

section Cotangent

variable {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (π : R →ₐ[𝒪] 𝒪)

theorem smul_cotangent_eq (r : R) (m : (RingHom.ker π).Cotangent) : r • m = (π r) • m := by
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  rw [← IsScalarTower.algebraMap_smul R (π r), ← sub_eq_zero, ← sub_smul, ← map_smul,
    Ideal.toCotangent_eq_zero, sq]
  refine Ideal.mul_mem_mul ?_ x.2
  simp [RingHom.mem_ker]

variable {n : ℕ} (a : Fin n → R) (hI : Ideal.span (Set.range a) = RingHom.ker π)

def gen (i : Fin n) : RingHom.ker π := ⟨a i, hI ▸ Ideal.subset_span (Set.mem_range_self i)⟩

@[scoped simp] theorem coe_gen (i : Fin n) : (gen π a hI i : R) = a i := rfl

noncomputable def psi : (Fin n → 𝒪) →ₗ[𝒪] (RingHom.ker π).Cotangent :=
  Fintype.linearCombination 𝒪 (fun i => (RingHom.ker π).toCotangent (gen π a hI i))

theorem psi_apply (w : Fin n → 𝒪) :
    psi π a hI w = (RingHom.ker π).toCotangent (∑ i, algebraMap 𝒪 R (w i) • gen π a hI i) := by
  simp only [psi, Fintype.linearCombination_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IsScalarTower.algebraMap_smul]

include hI in
theorem psi_surjective : Function.Surjective (psi π a hI) := by
  intro m
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  have hx : (x : R) ∈ Ideal.span (Set.range a) := by rw [hI]; exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  refine ⟨fun i => π (c i), ?_⟩
  rw [psi_apply]
  have hx' : x = ∑ i, c i • gen π a hI i := by
    apply Subtype.ext
    simp [← hc]
  rw [hx', map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, IsScalarTower.algebraMap_smul, ← smul_cotangent_eq]

theorem exists_syzygy_of_psi_eq_zero (w : Fin n → 𝒪) (hw : psi π a hI w = 0) :
    ∃ c : Fin n → R, (∀ i, c i ∈ RingHom.ker π) ∧
      ∑ i, (algebraMap 𝒪 R (w i) - c i) * a i = 0 := by
  classical
  rw [psi_apply, Ideal.toCotangent_eq_zero] at hw
  have h2 : (RingHom.ker π) ^ 2 = (RingHom.ker π) • Ideal.span (Set.range a) := by
    rw [sq, hI]; rfl
  rw [h2] at hw
  have hw' : (∑ i, algebraMap 𝒪 R (w i) * a i) ∈ (RingHom.ker π) • Submodule.span R (Set.range a) := by
    convert hw using 1
    simp [Algebra.smul_def]
  obtain ⟨cf, hcf, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hw'
  refine ⟨fun i => cf i, hcf, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)] at hsum
  simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
  rw [← hsum]
  simp [smul_eq_mul]

theorem det_mem_eta (v : Fin n → (Fin n → 𝒪)) (hv : ∀ j, psi π a hI (v j) = 0) :
    (Matrix.of fun i j => v j i).det ∈ (RingHom.ker π).annihilator.map π := by
  classical
  choose C hC hCsum using fun j => exists_syzygy_of_psi_eq_zero π a hI (v j) (hv j)
  let V : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => algebraMap 𝒪 R (v j i) - C j i
  have hVa : V *ᵥ a = 0 := by
    ext j
    simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact hCsum j
  have hdet : ∀ i, V.det * a i = 0 := by
    intro i
    have h := congrArg (fun u => (V.adjugate *ᵥ u) i) hVa
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Pi.zero_apply] at h
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simpa using h
  have hann : V.det ∈ (RingHom.ker π).annihilator := by
    rw [← hI, show Ideal.span (Set.range a) = Submodule.span R (Set.range a) from rfl,
      Submodule.mem_annihilator_span]
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hdet i
  have hmap : π V.det = (Matrix.of fun i j => v j i).det := by
    rw [AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext i j
    have : π (C j i) = 0 := hC j i
    simp [V, Matrix.transpose_apply, AlgHom.mapMatrix_apply, this]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hann

end Cotangent

section Syzygy

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
  {R : Type v} [CommRing R] [Algebra 𝒪 R]

omit [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] in
theorem basisFun_det_eq {n : ℕ} (v : Fin n → (Fin n → 𝒪)) :
    (Pi.basisFun 𝒪 (Fin n)).det v = (Matrix.of fun i j => v j i).det := by
  rw [Basis.det_apply]
  congr 1

theorem exists_syzygy_matrix (π : R →ₐ[𝒪] 𝒪) {n : ℕ} (a : Fin n → R)
    (hI : Ideal.span (Set.range a) = RingHom.ker π)
    (hfin : Module.length 𝒪 (RingHom.ker π).Cotangent ≠ ⊤) (h𝒪 : Module.length 𝒪 𝒪 = ⊤) :
    ∃ V : Matrix (Fin n) (Fin n) R, V.mulVec a = 0 ∧ V.det ∈ (RingHom.ker π).annihilator ∧
      π V.det ≠ 0 ∧
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {π V.det}) = Module.length 𝒪 (RingHom.ker π).Cotangent := by
  classical
  set ψ := psi π a hI
  have hψ := psi_surjective π a hI
  set N := LinearMap.ker ψ
  have hΦ : Module.length 𝒪 (RingHom.ker π).Cotangent = Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) :=
    ((ψ.quotKerEquivOfSurjective hψ).length_eq).symm
  set e := Pi.basisFun 𝒪 (Fin n)
  obtain ⟨m, snf⟩ := N.smithNormalForm e

  have hmn : m = n := by
    by_contra hmn
    have hns : ∃ i, i ∉ Set.range snf.f := by
      by_contra hcon
      have hsurj : Function.Surjective snf.f := fun i => by
        by_contra h'
        exact hcon ⟨i, fun ⟨j, hj⟩ => h' ⟨j, hj⟩⟩
      have := Fintype.card_le_of_surjective _ hsurj
      have := Fintype.card_le_of_embedding snf.f
      simp only [Fintype.card_fin] at *
      omega
    obtain ⟨i, hi⟩ := hns
    have hle := snf.le_ker_coord_of_notMem_range hi
    let lam : ((Fin n → 𝒪) ⧸ N) →ₗ[𝒪] 𝒪 := N.liftQ (snf.bM.coord i) hle
    have hlam : Function.Surjective lam := by
      intro o
      refine ⟨Submodule.Quotient.mk (o • snf.bM i), ?_⟩
      simp [lam]
    have := Module.length_le_of_surjective lam hlam
    rw [← hΦ, h𝒪, top_le_iff] at this
    exact hfin this
  have h : Module.finrank 𝒪 N = Module.finrank 𝒪 (Fin n → 𝒪) := by
    rw [Module.finrank_eq_card_basis snf.bN, Module.finrank_fin_fun, Fintype.card_fin, hmn]
  set c := Submodule.smithNormalFormCoeffs e h
  have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero e h
  have hlen : Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i, c i}) := by
    rw [(Submodule.quotientEquivPiSpan N e h).length_eq, Module.length_pi_of_fintype,
      length_quotient_span_prod _ _ (fun i _ => hc i)]

  let v : Fin n → (Fin n → 𝒪) := fun j => (Submodule.smithNormalFormBotBasis e h j : (Fin n → 𝒪))
  have hv : ∀ j, ψ (v j) = 0 := fun j =>
    LinearMap.mem_ker.mp (Submodule.smithNormalFormBotBasis e h j).2
  choose C hC hCsum using fun j => exists_syzygy_of_psi_eq_zero π a hI (v j) (hv j)
  let V : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => algebraMap 𝒪 R (v j i) - C j i
  have hVa : V.mulVec a = 0 := by
    ext j
    simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact hCsum j
  have hdet : ∀ i, V.det * a i = 0 := by
    intro i
    have h := congrArg (fun u => (V.adjugate.mulVec u) i) hVa
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Pi.zero_apply] at h
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simpa using h
  have hann : V.det ∈ (RingHom.ker π).annihilator := by
    rw [← hI, show Ideal.span (Set.range a) = Submodule.span R (Set.range a) from rfl,
      Submodule.mem_annihilator_span]
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hdet i
  have hmap : π V.det = (Matrix.of fun i j => v j i).det := by
    rw [AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext i j
    have : π (C j i) = 0 := hC j i
    simp [V, Matrix.transpose_apply, AlgHom.mapMatrix_apply, this]

  obtain ⟨u, hu⟩ := e.isUnit_det (Submodule.smithNormalFormTopBasis e h)
  have hπdet : π V.det = (∏ i, c i) * ↑u := by
    rw [hmap, ← basisFun_det_eq]
    have hv' : v = fun j => c j • Submodule.smithNormalFormTopBasis e h j := by
      funext j; exact Submodule.smithNormalFormBotBasis_def e h j
    rw [hv', AlternatingMap.map_smul_univ, ← hu, smul_eq_mul]
  have hprod_ne : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc i
  refine ⟨V, hVa, hann, ?_, ?_⟩
  · rw [hπdet]; exact mul_ne_zero hprod_ne (Units.ne_zero u)
  · rw [hΦ, hlen, hπdet, Ideal.span_singleton_mul_right_unit u.isUnit]

end Syzygy

section Main

variable {𝒪 : Type u} {R : Type v} {T : Type w}
  [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra 𝒪 R]
  [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [IsLocalRing R]
  [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in

theorem isLocalHom_of_augmentation (π : R →ₐ[𝒪] 𝒪) : IsLocalHom (algebraMap 𝒪 R) := by
  refine ⟨fun o ho => ?_⟩
  have := ho.map π
  rwa [AlgHom.commutes, Algebra.algebraMap_self_apply] at this

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  [Module.Finite 𝒪 T] in

theorem main_stepA (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hle : Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT))
    {n : ℕ} (a : Fin n → R) (ha : Ideal.span (Set.range a) = RingHom.ker πR) :
    ∃ V : Matrix (Fin n) (Fin n) R, V.mulVec a = 0 ∧
      φ V.det ∉ (maximalIdeal 𝒪).map (algebraMap 𝒪 T) := by
  classical
  have hπ' : ∀ r, πT (φ r) = πR r := fun r => congr($hπ r)
  haveI : IsLocalHom (algebraMap 𝒪 T) := isLocalHom_of_augmentation πT
  set IR : Ideal R := RingHom.ker πR with hIR
  set IT : Ideal T := RingHom.ker πT with hIT
  have hfinΦ : Module.length 𝒪 IR.Cotangent ≠ ⊤ :=
    ne_top_of_le_ne_top (length_quotient_ne_top hη) hle
  obtain ⟨V, hVa, hVann, hδ, hVlen⟩ := exists_syzygy_matrix πR a ha hfinΦ length_self_eq_top
  refine ⟨V, hVa, ?_⟩
  set d : T := φ V.det with hd
  set δ : 𝒪 := πR V.det with hδdef
  have hπd : πT d = δ := hπ' _

  have hIT_eq : ∀ y ∈ IT, ∃ r ∈ IR, φ r = y := fun y hy => by
    obtain ⟨r, rfl⟩ := hφ y
    exact ⟨r, by change πR r = 0; rw [← hπ']; exact hy, rfl⟩
  have hd_ann : ∀ y ∈ IT, d * y = 0 := fun y hy => by
    obtain ⟨r, hr, rfl⟩ := hIT_eq y hy
    rw [hd, ← map_mul, show V.det * r = 0 from Submodule.mem_annihilator.mp hVann r hr, map_zero]
  have hd_ann' : d ∈ IT.annihilator := Submodule.mem_annihilator.mpr fun y hy => hd_ann y hy
  have hη_le : IT.annihilator.map πT ≤ Ideal.span {δ} := by
    refine le_of_length_le (fun h => hδ (Ideal.span_singleton_eq_bot.mp h)) hη ?_
    rw [hVlen]; exact hle

  have hC1 : ∀ x ∈ IT, x ∈ IT.annihilator → x = 0 := fun x hxI hxA => by
    have h1 : d * x = 0 := hd_ann x hxI
    have h2 : x * (d - algebraMap 𝒪 T δ) = 0 := by
      refine Submodule.mem_annihilator.mp hxA _ ?_
      change πT (d - algebraMap 𝒪 T δ) = 0
      rw [map_sub, hπd, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have h3 : δ • x = 0 := by
      rw [Algebra.smul_def]
      linear_combination (-1 : T) * h2 + h1
    exact (smul_eq_zero.mp h3).resolve_left hδ

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have h𝔪ϖ : maximalIdeal 𝒪 = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  intro hdm
  rw [h𝔪ϖ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hdm
  obtain ⟨t, ht⟩ := hdm
  have htA : t ∈ IT.annihilator := Submodule.mem_annihilator.mpr fun y hy => by
    have : ϖ • (t * y) = 0 := by
      rw [Algebra.smul_def, ← mul_assoc, mul_comm _ t, ht]; exact hd_ann y hy
    exact (smul_eq_zero.mp this).resolve_left hϖ.ne_zero
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hη_le (Ideal.mem_map_of_mem _ htA))
  have ht' : t - algebraMap 𝒪 T c * d = 0 := by
    refine hC1 _ ?_ (IT.annihilator.sub_mem htA (IT.annihilator.mul_mem_left _ hd_ann'))
    change πT (t - algebraMap 𝒪 T c * d) = 0
    rw [map_sub, map_mul, hπd, AlgHom.commutes, Algebra.algebraMap_self_apply, hc, sub_self]
  rw [sub_eq_zero] at ht'
  have hmem : algebraMap 𝒪 T (c * ϖ) ∈ maximalIdeal T :=
    IsLocalRing.map_maximalIdeal_le _
      (Ideal.mem_map_of_mem _ (h𝔪ϖ ▸ Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  have hunit : IsUnit (1 - algebraMap 𝒪 T (c * ϖ)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hmem
  have hzero : (1 - algebraMap 𝒪 T (c * ϖ)) * d = 0 := by
    have : algebraMap 𝒪 T (c * ϖ) * d = d := by
      conv_rhs => rw [← ht, ht']
      rw [map_mul]; ring
    rw [sub_mul, one_mul, this, sub_self]
  have hd0 : d = 0 := (hunit.mul_right_eq_zero).mp hzero
  exact hδ (by rw [← hπd, hd0, map_zero])

end Main

section StepB

variable {𝒪 : Type u} {R : Type v} {T : Type w}
  [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra 𝒪 R]
  [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

local notation "k" => 𝒪 ⧸ maximalIdeal 𝒪
local notation "𝔪R" => Ideal.map (algebraMap 𝒪 R) (maximalIdeal 𝒪)
local notation "𝔪T" => Ideal.map (algebraMap 𝒪 T) (maximalIdeal 𝒪)

theorem main (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hle : Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT)) :
    Function.Bijective φ ∧
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  classical
  have hπ' : ∀ r, πT (φ r) = πR r := fun r => congr($hπ r)
  haveI : IsLocalHom (algebraMap 𝒪 R) := isLocalHom_of_augmentation πR
  haveI : IsLocalHom (algebraMap 𝒪 T) := isLocalHom_of_augmentation πT

  obtain ⟨n, a, ha⟩ : ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = RingHom.ker πR :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian _)
  obtain ⟨V, hVa, hdV⟩ := main_stepA φ hφ πR πT hπ hη hle a ha

  have h𝔪R_ne : (𝔪R) ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap 𝒪 R)).ne
  have h𝔪T_ne : (𝔪T) ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap 𝒪 T)).ne
  haveI : Nontrivial (R ⧸ 𝔪R) := Ideal.Quotient.nontrivial_iff.mpr h𝔪R_ne
  haveI hlocRq : IsLocalRing (R ⧸ 𝔪R) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (𝔪R)) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmaxq : (maximalIdeal R).map (Ideal.Quotient.mk (𝔪R)) = maximalIdeal (R ⧸ 𝔪R) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal h𝔪R_ne)]
  haveI : IsAdicComplete (maximalIdeal (R ⧸ 𝔪R)) (R ⧸ 𝔪R) := by
    have h := IsLocalRing.isAdicComplete_map_maximalIdeal_quotient (R := R) (𝔪R)
    rwa [hmaxq] at h
  haveI : Module.Finite 𝒪 (T ⧸ 𝔪T) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 (𝔪T)).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (T ⧸ 𝔪T) := Module.Finite.of_restrictScalars_finite 𝒪 k (T ⧸ 𝔪T)

  have hφm : (𝔪R) ≤ (𝔪T).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    simp only [Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ho
  have hπRm : (𝔪R) ≤ (maximalIdeal 𝒪).comap πR := by
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    simpa [Ideal.mem_comap] using ho
  have hπTm : (𝔪T) ≤ (maximalIdeal 𝒪).comap πT := by
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    simpa [Ideal.mem_comap] using ho
  have hks : Function.Surjective (algebraMap 𝒪 k) := Ideal.Quotient.mk_surjective
  let φq : (R ⧸ 𝔪R) →ₐ[k] (T ⧸ 𝔪T) := (Ideal.quotientMapₐ (𝔪T) φ hφm).extendScalarsOfSurjective hks
  let πRq : (R ⧸ 𝔪R) →ₐ[k] k :=
    (Ideal.quotientMapₐ (maximalIdeal 𝒪) πR hπRm).extendScalarsOfSurjective hks
  let πTq : (T ⧸ 𝔪T) →ₐ[k] k :=
    (Ideal.quotientMapₐ (maximalIdeal 𝒪) πT hπTm).extendScalarsOfSurjective hks
  have hφq : ∀ r, φq (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (φ r) := fun r => rfl
  have hπRq : ∀ r, πRq (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (πR r) := fun r => rfl
  have hπTq : ∀ t, πTq (Ideal.Quotient.mk _ t) = Ideal.Quotient.mk _ (πT t) := fun t => rfl
  have hφq_surj : Function.Surjective φq := fun y => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, rfl⟩ := hφ t
    exact ⟨Ideal.Quotient.mk _ r, hφq r⟩
  have hπq : πTq.comp φq = πRq := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgHom.comp_apply, hφq, hπTq, hπRq, hπ']

  have hkerq : RingHom.ker πRq = (RingHom.ker πR).map (Ideal.Quotient.mk (𝔪R)) := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.mem_quotient_iff_mem_sup]
    change πRq (Ideal.Quotient.mk _ r) = 0 ↔ _
    rw [hπRq, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hr
      have hsplit : r = (r - algebraMap 𝒪 R (πR r)) + algebraMap 𝒪 R (πR r) := by ring
      rw [hsplit]
      refine Submodule.add_mem_sup ?_ (Ideal.mem_map_of_mem _ hr)
      change πR (r - algebraMap 𝒪 R (πR r)) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    · intro hr
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hr
      rw [map_add, show πR y = 0 from hy, zero_add]
      have hz' : πR z ∈ (Ideal.map (algebraMap 𝒪 R) (maximalIdeal 𝒪)).map (πR : R →+* 𝒪) :=
        Ideal.mem_map_of_mem _ hz
      rwa [Ideal.map_map, AlgHom.comp_algebraMap, Algebra.algebraMap_self, Ideal.map_id] at hz'
  have haq : Ideal.span (Set.range (fun i => Ideal.Quotient.mk (𝔪R) (a i))) = RingHom.ker πRq := by
    rw [hkerq, ← ha, Ideal.map_span, ← Set.range_comp]
    rfl

  have hVq : (V.map (Ideal.Quotient.mk (𝔪R))).mulVec (fun i => Ideal.Quotient.mk (𝔪R) (a i)) = 0 := by
    funext i
    have h := RingHom.map_mulVec (Ideal.Quotient.mk (𝔪R)) V a i
    rw [hVa, Pi.zero_apply, map_zero] at h
    rw [Pi.zero_apply]
    exact h.symm
  have hdetq : φq (V.map (Ideal.Quotient.mk (𝔪R))).det ≠ 0 := by
    have : (V.map (Ideal.Quotient.mk (𝔪R))).det = Ideal.Quotient.mk _ V.det :=
      (RingHom.map_det (Ideal.Quotient.mk (𝔪R)) V).symm
    rw [this, hφq, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hdV

  letI : Field k := Ideal.Quotient.field (maximalIdeal 𝒪)
  obtain ⟨hbij, m, g, ⟨e⟩⟩ :=
    ROWF.bijective_and_exists_presentation_of_apply_det_ne_zero φq hφq_surj πRq πTq hπq
      (fun i => Ideal.Quotient.mk (𝔪R) (a i)) haq (V.map (Ideal.Quotient.mk (𝔪R))) hVq hdetq

  have hker : RingHom.ker φ ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 R) := fun r hr => by
    have h0 : φq (Ideal.Quotient.mk _ r) = 0 := by
      rw [hφq, show φ r = 0 from hr, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((injective_iff_map_eq_zero φq).mp hbij.1 _ h0)
  have hinj : Function.Injective φ :=
    AlgHom.injective_of_surjective_of_ker_le_map_maximalIdeal φ hφ hker
  refine ⟨⟨hinj, hφ⟩, ?_⟩

  exact Algebra.exists_presentation_of_residueField (𝒪 := 𝒪) (T := T) ⟨m, g, ⟨e.restrictScalars 𝒪⟩⟩

end StepB

end FrobDictCRIT
p2m_reactivate "P2MW.S_AlgHom_bijective_and_exists_presentation_of_length_cotangent_le.FrobDictCRIT"

theorem solution
    {𝒪 : Type u} {R : Type v} {T : Type w}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra 𝒪 R]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hle : Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT)) :
    Function.Bijective φ ∧
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) :=
  FrobDictCRIT.main φ hφ πR πT hπ hη hle

end S_AlgHom_bijective_and_exists_presentation_of_length_cotangent_le
end P2MW
export P2MW.S_AlgHom_bijective_and_exists_presentation_of_length_cotangent_le (solution)
