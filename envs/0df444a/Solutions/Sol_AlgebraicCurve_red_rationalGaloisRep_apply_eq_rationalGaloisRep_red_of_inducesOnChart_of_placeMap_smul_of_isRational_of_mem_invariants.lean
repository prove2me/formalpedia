-- Prove2me | solution 1 for AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9e63bf8d-82c9-5bba-87df-b578b44933e8

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

noncomputable section

namespace P2mRedChartNaturalityR

section Tate

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M]

theorem eq_zero_of_pow_smul_eq_zero (v : ℕ) (z : TateModule ℓ M)
    (h : ((ℓ : ℤ_[ℓ]) ^ v) • z = 0) : z = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h1 : ((((ℓ ^ v : ℕ) : ℤ_[ℓ]) • z : TateModule ℓ M) : ℕ → M) (n + v) = 0 := by
    rw [Nat.cast_pow, h]; rfl
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat_pow] at h1
  rw [TateModule.coe_zero, Pi.zero_apply]
  exact h1

theorem eq_zero_of_smul_eq_zero {c : ℤ_[ℓ]} (hc : c ≠ 0) (z : TateModule ℓ M)
    (h : c • z = 0) : z = 0 := by
  obtain ⟨u, m, hcu⟩ : ∃ (u : ℤ_[ℓ]ˣ) (m : ℕ), c = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ m :=
    ⟨PadicInt.unitCoeff hc, c.valuation, PadicInt.unitCoeff_spec hc⟩
  rw [hcu, mul_smul] at h
  have h2 : ((ℓ : ℤ_[ℓ]) ^ m) • z = 0 := by
    have := congrArg (fun w => ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • w) h
    simpa only [smul_smul, Units.inv_mul_cancel_left, smul_zero] using this
  exact eq_zero_of_pow_smul_eq_zero m z h2

theorem one_tmul_injective {y y' : TateModule ℓ M}
    (h : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y : ℚ_[ℓ] ⊗[ℤ_[ℓ]] TateModule ℓ M) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y') :
    y = y' := by
  have h2 : TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ M) 1 y =
      TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ M) 1 y' := h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ_[ℓ]) _).mp h2
  have hc0 : (c : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  rw [← sub_eq_zero]
  refine eq_zero_of_smul_eq_zero hc0 _ ?_
  rw [smul_sub, sub_eq_zero]
  simpa only [Submonoid.smul_def] using hc

theorem exists_eq_smul_one_tmul (w : ℚ_[ℓ] ⊗[ℤ_[ℓ]] TateModule ℓ M) :
    ∃ (c : ℚ_[ℓ]) (x : TateModule ℓ M), w = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) := by
  obtain ⟨⟨x, s⟩, hs⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ_[ℓ]) (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ M) 1) w
  have hs0 : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  refine ⟨(algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹, x, ?_⟩
  have hs' : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) • w = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x := by
    rw [algebraMap_smul]
    simp only [Submonoid.smul_def] at hs
    exact hs
  rw [← hs', smul_smul, inv_mul_cancel₀ hs0, one_smul]

end Tate

theorem exists_level_coeffs (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (k : ℕ) (d : ℕ → ℤ) :
    ∃ (Mx : ℕ) (c₁ c₂ N : ℤ), c₁ * d k + c₂ * d (k + Mx) = 0 ∧
      c₁ * (ℓ : ℤ) ^ Mx + c₂ = (ℓ : ℤ) ^ Mx + N * (ℓ : ℤ) ^ (k + Mx) := by
  by_cases hk : d k = 0
  · exact ⟨0, 1, 0, 0, by rw [hk]; ring, by ring⟩
  obtain ⟨v, u', hu', hvu⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hk) ℓ hℓ.out.ne_one
  obtain ⟨u, hdk, hℓu⟩ : ∃ u : ℤ, d k = (ℓ : ℤ) ^ v * u ∧ ¬ (ℓ : ℤ) ∣ u := by
    rcases Int.natAbs_eq (d k) with h | h
    · refine ⟨u', ?_, fun hd => hu' (Int.natCast_dvd_natCast.mp hd)⟩
      rw [h, hvu]; push_cast; ring
    · refine ⟨-(u' : ℤ), ?_, fun hd => hu' (Int.natCast_dvd_natCast.mp (dvd_neg.mp hd))⟩
      rw [h, hvu]; push_cast; ring
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = d (k + (v + 1)) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = u - ℓ * q := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = (ℓ : ℤ) ^ (k + 1) * q := ⟨_, rfl⟩
  have hua : u = a + ℓ * q := by rw [ha]; ring
  have hℓa : ¬ (ℓ : ℤ) ∣ a := by
    intro h
    apply hℓu
    rw [hua]
    exact dvd_add h (dvd_mul_right _ _)
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
  have hcop : IsCoprime ((ℓ : ℤ) ^ (k + 1)) a :=
    IsCoprime.pow_left (hprime.irreducible.coprime_iff_not_dvd.mpr hℓa)
  have hga : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left ..
  have hgb : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right ..
  obtain ⟨r, hr⟩ := hga
  have hcop' : IsCoprime (Int.gcd a b : ℤ) ((ℓ : ℤ) ^ (k + 1)) := by
    rw [hr] at hcop
    exact hcop.of_mul_right_left.symm
  have hgq : (Int.gcd a b : ℤ) ∣ q := hcop'.dvd_of_dvd_mul_left (by rw [← hb]; exact hgb)
  have hgu : (Int.gcd a b : ℤ) ∣ u := by
    rw [hua]
    exact dvd_add ⟨r, hr⟩ (dvd_mul_of_dvd_right hgq _)
  obtain ⟨w, hw⟩ := hgu
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = w * Int.gcdA a b := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = w * Int.gcdB a b := ⟨_, rfl⟩
  have key : u = a * e + b * t := by
    rw [hw, he, ht]
    have hbez := Int.gcd_eq_gcd_ab a b
    calc (Int.gcd a b : ℤ) * w = (a * Int.gcdA a b + b * Int.gcdB a b) * w := by rw [← hbez]
      _ = a * (w * Int.gcdA a b) + b * (w * Int.gcdB a b) := by ring
  refine ⟨v + 1, 1 - e, e * (ℓ : ℤ) ^ (v + 1) - t * (ℓ : ℤ) ^ (k + (v + 1)), -t, ?_, ?_⟩
  · rw [hdk, ← hq]
    rw [ha, hb] at key
    linear_combination (ℓ : ℤ) ^ v * key
  · ring

section PlaceCompat

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ofAlgAut_smul_place (σ : F ≃ₐ[K] F) (Q : Place K F) :
    SemilinearAut.ofAlgAut σ • Q = σ • Q := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [SemilinearAut.ofAlgAut_smul, AlgEquiv.smul_def]

end PlaceCompat

section Decomp

variable {L : Type} [Field L] {F : Type} [Field F] [Algebra L F]
variable {n : ℕ}

def rebin (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F) : Fin n → Divisor L F :=
  fun j => if j = i then ∑ j' ∈ Finset.univ.filter (fun j' => j' = i ∨ σ j' = i), Di j'
    else if σ j = i then 0 else Di j

theorem rebin_self (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F) :
    rebin i σ Di i = ∑ j' ∈ Finset.univ.filter (fun j' => j' = i ∨ σ j' = i), Di j' := by
  simp [rebin]

theorem rebin_eq_zero (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F)
    {j : Fin n} (hj : j ≠ i) (hσ : σ j = i) : rebin i σ Di j = 0 := by
  simp [rebin, hj, hσ]

theorem rebin_of_not (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F)
    {j : Fin n} (hj : j ≠ i) (hσ : σ j ≠ i) : rebin i σ Di j = Di j := by
  simp [rebin, hj, hσ]

theorem sum_rebin (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F) :
    ∑ j, rebin i σ Di j = ∑ j, Di j := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j' => j' = i ∨ σ j' = i),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j' => j' = i ∨ σ j' = i) (fun j => Di j)]
  congr 1
  · have hc : ∀ j ∈ Finset.univ.filter (fun j' => j' = i ∨ σ j' = i), rebin i σ Di j =
        if j = i then ∑ j' ∈ Finset.univ.filter (fun j' => j' = i ∨ σ j' = i), Di j' else 0 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      by_cases hji : j = i
      · rw [if_pos hji, hji, rebin_self]
      · rw [if_neg hji]
        exact rebin_eq_zero i σ Di hji (hj.2.resolve_left hji)
    rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq']
    rw [if_pos (by simp)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter] at hj
    have h' := hj.2
    rw [not_or] at h'
    exact rebin_of_not i σ Di h'.1 h'.2

theorem support_rebin (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F)
    (dom : Fin n → Set (Place L F)) (g : SemilinearAut L F)
    (hdom : ∀ P, P ∈ dom i ↔ g • P ∈ dom i) (hσ : ∀ j P, P ∈ dom j → g • P ∈ dom (σ j))
    (hsupp : ∀ j, ∀ P ∈ (Di j).support, P ∈ dom j) :
    ∀ j, ∀ P ∈ (rebin i σ Di j).support, P ∈ dom j := by
  classical
  intro j P hP
  by_cases hji : j = i
  · subst hji
    rw [rebin_self] at hP
    have h1 := Finsupp.mem_support_iff.mp hP
    rw [Finsupp.finsetSum_apply] at h1
    obtain ⟨j', hj', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have hPj' : P ∈ dom j' := hsupp j' P (Finsupp.mem_support_iff.mpr hne)
    rcases (Finset.mem_filter.mp hj').2 with h | h
    · rwa [h] at hPj'
    · have := hσ j' P hPj'
      rw [h] at this
      exact (hdom P).mpr this
  · by_cases hσj : σ j = i
    · rw [rebin_eq_zero i σ Di hji hσj] at hP
      simp at hP
    · rw [rebin_of_not i σ Di hji hσj] at hP
      exact hsupp j P hP

theorem degree_rebin (i : Fin n) (σ : Fin n → Fin n) (Di : Fin n → Divisor L F)
    (hdeg : ∀ j, Divisor.degree (Di j) = 0) : ∀ j, Divisor.degree (rebin i σ Di j) = 0 := by
  classical
  intro j
  by_cases hji : j = i
  · subst hji
    rw [rebin_self, map_sum]
    exact Finset.sum_eq_zero fun j' _ => hdeg j'
  · by_cases hσj : σ j = i
    · rw [rebin_eq_zero i σ Di hji hσj, map_zero]
    · rw [rebin_of_not i σ Di hji hσj]
      exact hdeg j

def gdec (i : Fin n) (σ : Fin n → Fin n) (g : SemilinearAut L F) (E : Fin n → Divisor L F) :
    Fin n → Divisor L F :=
  fun j' => (if j' = i then g • E i else 0) +
    ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i ∨ σ j = i) ∧ σ j = j'), g • E j

theorem gdec_self (i : Fin n) (σ : Fin n → Fin n) (g : SemilinearAut L F)
    (E : Fin n → Divisor L F) : gdec i σ g E i = g • E i := by
  classical
  unfold gdec
  rw [if_pos rfl]
  have : Finset.univ.filter (fun j => ¬ (j = i ∨ σ j = i) ∧ σ j = i) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and, not_or]
    intro h
    exact h.2
  rw [this, Finset.sum_empty, add_zero]

theorem sum_gdec (i : Fin n) (σ : Fin n → Fin n) (g : SemilinearAut L F)
    (E : Fin n → Divisor L F) (hE0 : ∀ j, j ≠ i → σ j = i → E j = 0) :
    ∑ j', gdec i σ g E j' = g • ∑ j, E j := by
  classical
  simp only [gdec]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
  have h2 : ∑ j' : Fin n, ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i ∨ σ j = i) ∧ σ j = j'),
      g • E j = ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i ∨ σ j = i)), g • E j := by
    have := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun j => ¬ (j = i ∨ σ j = i))) (t := Finset.univ) (g := σ)
      (fun j _ => Finset.mem_univ _) (fun j => g • E j)
    rw [← this]
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.filter_filter]
  rw [h2, Finset.smul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i ∨ σ j = i)]
  congr 1
  rw [Finset.sum_eq_single_of_mem i (by simp) ?_]
  intro j hj hji
  rw [hE0 j hji ((Finset.mem_filter.mp hj).2.resolve_left hji), smul_zero]

theorem exists_of_mem_support_smul (g : SemilinearAut L F) (D : Divisor L F) (Q : Place L F)
    (hQ : Q ∈ (g • D).support) : ∃ Q₀ ∈ D.support, Q = g • Q₀ := by
  classical
  rw [SemilinearAut.divisor_smul_def] at hQ
  obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hQ)
  exact ⟨Q₀, hQ₀, rfl⟩

theorem support_gdec (i : Fin n) (σ : Fin n → Fin n) (g : SemilinearAut L F)
    (E : Fin n → Divisor L F) (dom : Fin n → Set (Place L F))
    (hdom : ∀ P, P ∈ dom i ↔ g • P ∈ dom i) (hσ : ∀ j P, P ∈ dom j → g • P ∈ dom (σ j))
    (hsupp : ∀ j, ∀ P ∈ (E j).support, P ∈ dom j) :
    ∀ j', ∀ P ∈ (gdec i σ g E j').support, P ∈ dom j' := by
  classical
  intro j' P hP
  unfold gdec at hP
  rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
  · by_cases hj' : j' = i
    · subst hj'
      rw [if_pos rfl] at h
      obtain ⟨Q₀, hQ₀, rfl⟩ := exists_of_mem_support_smul g (E j') P h
      exact (hdom Q₀).mp (hsupp j' Q₀ hQ₀)
    · rw [if_neg hj'] at h
      simp at h
  · have h1 := Finsupp.mem_support_iff.mp h
    rw [Finsupp.finsetSum_apply] at h1
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    obtain ⟨-, hσj⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨Q₀, hQ₀, rfl⟩ := exists_of_mem_support_smul g (E j) P (Finsupp.mem_support_iff.mpr hne)
    have := hσ j Q₀ (hsupp j Q₀ hQ₀)
    rwa [hσj] at this

theorem degree_gdec (i : Fin n) (σ : Fin n → Fin n) (g : SemilinearAut L F)
    (E : Fin n → Divisor L F) (hdeg : ∀ j, Divisor.degree (E j) = 0) :
    ∀ j', Divisor.degree (gdec i σ g E j') = 0 := by
  classical
  intro j'
  unfold gdec
  rw [map_add, map_sum]
  have h1 : Divisor.degree (if j' = i then g • E i else 0) = 0 := by
    split_ifs
    · rw [SemilinearAut.degree_smul, hdeg]
    · exact map_zero _
  rw [h1, zero_add]
  exact Finset.sum_eq_zero fun j _ => by rw [SemilinearAut.degree_smul, hdeg]

end Decomp

theorem mapDomain_placeMap_smul {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    {Fb : Type} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb] (C : ComponentChart A F Fb)
    (g : SemilinearAut L F) (φ : Fb ≃ₐ[IsLocalRing.ResidueField A] Fb)
    (hplace : ∀ P ∈ C.dom, C.placeMap (g • P) = SemilinearAut.ofAlgAut φ • C.placeMap P)
    (E : Divisor L F) (hE : ∀ P ∈ E.support, P ∈ C.dom) :
    Finsupp.mapDomain C.placeMap (g • E) = φ • Finsupp.mapDomain C.placeMap E := by
  rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, Divisor.smul_def,
    ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro P hP
  simp only [Function.comp_apply]
  rw [hplace P (hE P hP), ofAlgAut_smul_place]

theorem core
    {L : Type} [Field L] (A : ValuationSubring L)
    (F : Type) [Field F] [Algebra L F]
    (n : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Vinv : Submodule ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F)))
    (red : ↥Vinv →ₗ[ℚ_[ℓ]] ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)
    (hrep : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0)
    (g : SemilinearAut L F)
    (hgV : ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v ∈ Vinv)
    (i : Fin n) (φ : Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i)
    (hdom : ∀ P : Place L F, P ∈ (C i).dom ↔ g • P ∈ (C i).dom)
    (hplace : ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (C i).placeMap P)
    (hperm : ∀ j, ∃ j', ∀ P : Place L F, P ∈ (C j).dom → g • P ∈ (C j').dom)
    (x : TateModule ℓ (Pic0 L F))
    (hx : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Vinv) :
    red ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x), hgV _ hx⟩ i =
      ModularCurve.rationalGaloisRep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
        (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ
        (red ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ i) := by
  classical

  have hgv : ((⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x), hgV _ hx⟩ : ↥Vinv) : ModularCurve.RationalTateModule ℓ (Pic0 L F)) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) g x :=
    ModularCurve.rationalGaloisRep_tmul ℓ (Pic0 L F) (SemilinearAut L F) g 1 x
  have hv : ((⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ : ↥Vinv) : ModularCurve.RationalTateModule ℓ (Pic0 L F)) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x := rfl

  have hzero_deg : (0 : Divisor L F) ∈ Divisor.degZero (K := L) (F := F) := zero_mem _
  have hzcls : ∀ z : TateModule ℓ (Pic0 L F),
      Pic0.mk ⟨0, hzero_deg⟩ = TateModule.proj ℓ (Pic0 L F) 0 z := by
    intro z
    rw [TateModule.proj_apply, TateModule.apply_zero]
    rfl
  have hzsum : (0 : Divisor L F) = ∑ _j : Fin n, (0 : Divisor L F) := by simp
  have hzsupp : ∀ j : Fin n, ∀ P ∈ (0 : Divisor L F).support, P ∈ (C j).dom := by
    intro j P hP
    simp at hP
  have hzdeg : ∀ _j : Fin n, Divisor.degree (0 : Divisor L F) = 0 := fun _ => map_zero _
  obtain ⟨y, hy, -⟩ := hred ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ x hv 0 0 hzero_deg (hzcls x)
    (fun _ => 0) hzsum hzsupp hzdeg i
  obtain ⟨y', hy', -⟩ := hred ⟨_, hgV _ hx⟩ (TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) g x)
    hgv 0 0 hzero_deg (hzcls _) (fun _ => 0) hzsum hzsupp hzdeg i

  suffices hlev : ∀ k, (y' : ℕ → Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k =
      φ • (y : ℕ → Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k by
    have hyy : y' = TateModule.rep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
        (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ y :=
      Subtype.ext (funext fun k => by rw [TateModule.rep_apply]; exact hlev k)
    rw [hy', hy, ModularCurve.rationalGaloisRep_tmul, hyy]
  intro k

  choose Dr hDr Dir hcls hsum hsupp hdeg using hrep ⟨_, hx⟩ x rfl
  choose σ hσ using hperm

  have hEsum : ∀ j, Dr j = ∑ j', rebin i σ (Dir j) j' := fun j => by
    rw [hsum j]; exact (sum_rebin i σ (Dir j)).symm
  have hEsupp : ∀ j j', ∀ P ∈ (rebin i σ (Dir j) j').support, P ∈ (C j').dom := fun j =>
    support_rebin i σ (Dir j) (fun j' => (C j').dom) g hdom (fun j' P hP => hσ j' P hP) (hsupp j)
  have hEdeg : ∀ j j', Divisor.degree (rebin i σ (Dir j) j') = 0 := fun j =>
    degree_rebin i σ (Dir j) (hdeg j)
  have hE0 : ∀ j j', j' ≠ i → σ j' = i → rebin i σ (Dir j) j' = 0 := fun j _ h1 h2 =>
    rebin_eq_zero i σ (Dir j) h1 h2

  obtain ⟨Mx, c₁, c₂, N, hdegc, hcls_c⟩ := exists_level_coeffs ℓ k
    (fun j => Divisor.degree (Finsupp.mapDomain (C i).placeMap (rebin i σ (Dir j) i)))

  obtain ⟨Dt, hDt⟩ : ∃ Dt : Divisor L F, Dt = c₁ • Dr k + c₂ • Dr (k + Mx) := ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ Et : Fin n → Divisor L F,
      Et = fun j' => c₁ • rebin i σ (Dir k) j' + c₂ • rebin i σ (Dir (k + Mx)) j' := ⟨_, rfl⟩
  have hDt_deg : Dt ∈ Divisor.degZero (K := L) (F := F) := by
    rw [Divisor.mem_degZero, hDt, map_add, map_zsmul, map_zsmul,
      (Divisor.mem_degZero).mp (hDr k), (Divisor.mem_degZero).mp (hDr (k + Mx)), smul_zero,
      smul_zero, add_zero]
  have hDt_cls : Pic0.mk ⟨Dt, hDt_deg⟩ = TateModule.proj ℓ (Pic0 L F) k x := by
    have h1 : (⟨Dt, hDt_deg⟩ : Divisor.degZero (K := L) (F := F)) =
        c₁ • ⟨Dr k, hDr k⟩ + c₂ • ⟨Dr (k + Mx), hDr (k + Mx)⟩ := Subtype.ext (by
      simp only [AddSubgroup.coe_add, AddSubgroupClass.coe_zsmul, hDt])
    show QuotientAddGroup.mk' _ (⟨Dt, hDt_deg⟩ : Divisor.degZero (K := L) (F := F)) = _
    rw [h1, map_add, map_zsmul, map_zsmul]
    change c₁ • Pic0.mk ⟨Dr k, hDr k⟩ + c₂ • Pic0.mk ⟨Dr (k + Mx), hDr (k + Mx)⟩ = _
    rw [hcls k, hcls (k + Mx)]
    have hkm : TateModule.proj ℓ (Pic0 L F) k x =
        ((ℓ : ℤ) ^ Mx) • TateModule.proj ℓ (Pic0 L F) (k + Mx) x := by
      rw [TateModule.proj_apply, TateModule.proj_apply]
      have := TateModule.compat_pow x k Mx
      rw [Nat.cast_pow] at this
      exact this.symm
    have htor : ((ℓ : ℤ) ^ (k + Mx)) • TateModule.proj ℓ (Pic0 L F) (k + Mx) x = 0 := by
      rw [TateModule.proj_apply, ← Nat.cast_pow]
      exact TateModule.torsion x (k + Mx)
    rw [hkm]
    have e1 : c₁ • ((ℓ : ℤ) ^ Mx • TateModule.proj ℓ (Pic0 L F) (k + Mx) x) +
        c₂ • TateModule.proj ℓ (Pic0 L F) (k + Mx) x =
        ((ℓ : ℤ) ^ Mx + N * (ℓ : ℤ) ^ (k + Mx)) • TateModule.proj ℓ (Pic0 L F) (k + Mx) x := by
      rw [← hcls_c, add_zsmul, mul_zsmul]
    rw [e1, add_zsmul, mul_zsmul, htor, zsmul_zero, add_zero]
  have hEt_sum : Dt = ∑ j', Et j' := by
    rw [hEt, hDt]
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← hEsum]
  have hEt_supp : ∀ j', ∀ P ∈ (Et j').support, P ∈ (C j').dom := by
    intro j' P hP
    rw [hEt] at hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
    · exact hEsupp k j' P (Finsupp.support_smul h)
    · exact hEsupp (k + Mx) j' P (Finsupp.support_smul h)
  have hEt_deg : ∀ j', Divisor.degree (Et j') = 0 := by
    intro j'
    simp only [hEt, map_add, map_zsmul, hEdeg, smul_zero, add_zero]
  have hEt0 : ∀ j', j' ≠ i → σ j' = i → Et j' = 0 := by
    intro j' h1 h2
    simp only [hEt, hE0 k j' h1 h2, hE0 (k + Mx) j' h1 h2, smul_zero, add_zero]

  have hpf : Finsupp.mapDomain (C i).placeMap (Et i) =
      c₁ • Finsupp.mapDomain (C i).placeMap (rebin i σ (Dir k) i) +
        c₂ • Finsupp.mapDomain (C i).placeMap (rebin i σ (Dir (k + Mx)) i) := by
    have hz : ∀ (c : ℤ) (D : Divisor L F), Finsupp.mapDomain (C i).placeMap (c • D) =
        c • Finsupp.mapDomain (C i).placeMap D :=
      fun c D => map_zsmul (Finsupp.mapDomain.addMonoidHom (C i).placeMap) c D
    rw [hEt]
    simp only []
    rw [Finsupp.mapDomain_add, hz, hz]
  have hpf_deg : Divisor.degree (Finsupp.mapDomain (C i).placeMap (Et i)) = 0 := by
    rw [hpf, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
    exact hdegc

  obtain ⟨yk, hyk, hyk2⟩ := hred ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ x hv k Dt hDt_deg hDt_cls Et
    hEt_sum hEt_supp hEt_deg i
  have hyk_eq : yk = y := one_tmul_injective (hyk.symm.trans hy)
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
      (E₀ : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
        Finsupp.mapDomain (C i).placeMap (Et i) :=
    ⟨⟨_, (Divisor.mem_degZero).mpr hpf_deg⟩, rfl⟩
  have hlevk : TateModule.proj ℓ _ k y = Pic0.mk E₀ := by
    rw [← hyk_eq]; exact hyk2 E₀ hE₀

  have hgDt_deg : g • Dt ∈ Divisor.degZero (K := L) (F := F) :=
    SemilinearAut.smul_mem_degZero g hDt_deg
  have hgDt_cls : Pic0.mk ⟨g • Dt, hgDt_deg⟩ =
      TateModule.proj ℓ (Pic0 L F) k (TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) g x) := by
    have h1 : (⟨g • Dt, hgDt_deg⟩ : Divisor.degZero (K := L) (F := F)) =
        SemilinearAut.degZeroSMulHom g ⟨Dt, hDt_deg⟩ := Subtype.ext rfl
    rw [h1, ← SemilinearAut.pic0_smul_mk, hDt_cls, TateModule.proj_apply, TateModule.proj_apply,
      TateModule.rep_apply]
  have hEg_sum : g • Dt = ∑ j', gdec i σ g Et j' := by
    rw [sum_gdec i σ g Et hEt0, ← hEt_sum]
  have hEg_supp : ∀ j', ∀ P ∈ (gdec i σ g Et j').support, P ∈ (C j').dom :=
    support_gdec i σ g Et (fun j' => (C j').dom) hdom (fun j' P hP => hσ j' P hP) hEt_supp
  have hEg_deg : ∀ j', Divisor.degree (gdec i σ g Et j') = 0 := degree_gdec i σ g Et hEt_deg
  obtain ⟨yk', hyk', hyk2'⟩ := hred ⟨_, hgV _ hx⟩
    (TateModule.rep ℓ (Pic0 L F) (SemilinearAut L F) g x) hgv k (g • Dt) hgDt_deg hgDt_cls
    (gdec i σ g Et) hEg_sum hEg_supp hEg_deg i
  have hyk'_eq : yk' = y' := one_tmul_injective (hyk'.symm.trans hy')

  have hpf' : Finsupp.mapDomain (C i).placeMap (gdec i σ g Et i) =
      φ • Finsupp.mapDomain (C i).placeMap (Et i) := by
    rw [gdec_self]
    exact mapDomain_placeMap_smul A (C i) g φ hplace (Et i) (hEt_supp i)
  have hpf'_deg : Finsupp.mapDomain (C i).placeMap (gdec i σ g Et i) ∈
      Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i) := by
    rw [Divisor.mem_degZero, hpf', Divisor.degree_smul, ← hE₀]
    exact (Divisor.mem_degZero).mp E₀.2
  have hlevk' : TateModule.proj ℓ _ k y' = Pic0.mk ⟨_, hpf'_deg⟩ := by
    rw [← hyk'_eq]; exact hyk2' ⟨_, hpf'_deg⟩ rfl
  have hE₀' : (⟨_, hpf'_deg⟩ : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i)) =
      Pic0.degZeroSMulHom φ E₀ :=
    Subtype.ext (by rw [Pic0.coe_degZeroSMulHom, hE₀]; exact hpf')

  rw [TateModule.proj_apply] at hlevk hlevk'
  rw [hlevk', hlevk, hE₀', ← Pic0.smul_mk]

end P2mRedChartNaturalityR

end

open P2mRedChartNaturalityR in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type) [Field F] [Algebra L F]
    (n : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))

    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Vinv : Submodule ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F)))
    (red : ↥Vinv →ₗ[ℚ_[ℓ]] ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)

    (hrep : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0)
    (g : SemilinearAut L F)
    (hgV : ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v ∈ Vinv)
    (i : Fin n) (φ : Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i)
    (hint : ∀ f : F, f ∈ (C i).integers ↔ g • f ∈ (C i).integers)
    (hres : ∀ (f : F) (hf : f ∈ (C i).integers), (C i).residue ⟨g • f, (hint f).mp hf⟩ = φ ((C i).residue ⟨f, hf⟩))
    (hdom : ∀ P : Place L F, P ∈ (C i).dom ↔ g • P ∈ (C i).dom)
    (hplace : ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (C i).placeMap P)
    (hperm : ∀ j, ∃ j', ∀ P : Place L F, P ∈ (C j).dom → g • P ∈ (C j').dom)
    (v : ↥Vinv) :
    red ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v, hgV v v.2⟩ i =
      ModularCurve.rationalGaloisRep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
        (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ (red v i) := by
  suffices H : ∀ (w : ↥Vinv)
      (hw : ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g w ∈ Vinv),
      red ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g w, hw⟩ i =
        ModularCurve.rationalGaloisRep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
          (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ (red w i) from H v (hgV v v.2)
  intro w hw
  obtain ⟨c, x, hcx⟩ := exists_eq_smul_one_tmul (w : ModularCurve.RationalTateModule ℓ (Pic0 L F))
  by_cases hc : c = 0
  · have hw0 : w = 0 := Subtype.ext (by rw [hcx, hc, zero_smul]; rfl)
    subst hw0
    have h1 : (⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g
        ((0 : ↥Vinv) : ModularCurve.RationalTateModule ℓ (Pic0 L F)), hw⟩ : ↥Vinv) = 0 :=
      Subtype.ext (by simp)
    rw [h1, map_zero, Pi.zero_apply, map_zero]
  · have hx : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Vinv := by
      have := Vinv.smul_mem c⁻¹ w.2
      rwa [hcx, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hw' : w = c • ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ := Subtype.ext (by rw [hcx]; rfl)
    have h1 : (⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g w, hw⟩ : ↥Vinv) =
        c • ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g
          ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x), hgV _ hx⟩ :=
      Subtype.ext (by simp [hcx, map_smul])
    rw [h1, map_smul, Pi.smul_apply, hw', map_smul, Pi.smul_apply, map_smul]
    congr 1
    exact core A F n Fbar C ℓ Vinv red hred hrep g hgV i φ hdom hplace hperm x hx

end S_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
end P2MW
export P2MW.S_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants (solution)
