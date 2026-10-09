-- Prove2me | solution 1 for ArtinPrimitiveRoots.weighted_family_distribution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:12:53.692292+00:00
-- url     : https://prove2.me/submissions/8a012aee-72d4-437a-9aca-13d2d1e796dd

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_single_r_remainders
import Theorems.Thm_ArtinPrimitiveRoots_mass_asymptotic

namespace ArtinPrimitiveRoots.WFDfin

section
open Real Finset Filter Topology

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply prod_nonneg
  intro i _
  apply div_nonneg (Nat.cast_nonneg _)
  unfold groupReciprocalSum
  exact sum_nonneg fun p _ => by positivity

end

section
open Real Finset Filter Topology

/-- Group primes are large but below `x^{0.9}`. -/
lemma group_facts {K : ℕ} (a : Fin K → ℝ) (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (M : ℕ) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ p ∈ groupPrimes x a,
      (M : ℝ) < p ∧ 2 < p ∧ (p : ℝ) ≤ x ^ (0.9 : ℝ) := by
  set T := log ((M : ℝ) + 2) + 1 with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ log ((M : ℝ) + 2) := log_nonneg (by have := M.cast_nonneg (α := ℝ); linarith)
    linarith
  refine ⟨exp (max (T ^ 10) 32), fun x hx p hp => ?_⟩
  have hL : max (T ^ 10) 32 ≤ log x := by
    rw [← log_exp (max _ _)]; exact log_le_log (exp_pos _) hx
  set L := log x
  have hL32 : 32 ≤ L := le_trans (le_max_right _ _) hL
  have hLT : T ^ 10 ≤ L := le_trans (le_max_left _ _) hL
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  unfold groupPrimes at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  unfold primeGroup at hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hple, -, hpge⟩ := hi
  have hple' : (p : ℝ) ≤ exp (2 * L ^ a i) :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hple)).trans (Nat.floor_le (exp_pos _).le)
  have hL1 : 1 ≤ L := by linarith
  have hLnn : 0 ≤ L := by linarith
  -- lower bound
  set t := L ^ (0.1 : ℝ) with ht
  have ht10 : t ^ 10 = L := by
    rw [ht, ← rpow_natCast, ← rpow_mul hLnn]; norm_num
  have htT : T ≤ t := by
    have ht0 : 0 ≤ t := rpow_nonneg hLnn _
    by_contra h
    push_neg at h
    have : t ^ 10 < T ^ 10 := pow_lt_pow_left₀ h ht0 (by norm_num)
    linarith
  have hta : t ≤ L ^ a i := rpow_le_rpow_of_exponent_le hL1 (hai i).1.le
  have hexp : (M : ℝ) + 2 < exp t := by
    have h1 : log ((M : ℝ) + 2) < t := by linarith
    have := exp_lt_exp.mpr h1
    rwa [exp_log (by positivity)] at this
  have hlow : (M : ℝ) + 2 < p :=
    lt_of_lt_of_le hexp ((exp_le_exp.mpr hta).trans hpge)
  -- upper bound
  set s := L ^ (0.2 : ℝ) with hs
  have hs5 : s ^ 5 = L := by
    rw [hs, ← rpow_natCast, ← rpow_mul hLnn]; norm_num
  have hs0 : 0 ≤ s := rpow_nonneg hLnn _
  have hs2 : 2 ≤ s := by
    by_contra h
    push_neg at h
    have : s ^ 5 < 2 ^ 5 := pow_lt_pow_left₀ h hs0 (by norm_num)
    linarith
  have has : L ^ a i ≤ s := rpow_le_rpow_of_exponent_le hL1 (hai i).2.le
  have h2s : 2 * s ≤ 0.9 * L := by
    rw [← hs5]
    have h16 : 16 ≤ s ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hs2 4; norm_num at this; linarith
    nlinarith
  have hup : (p : ℝ) ≤ x ^ (0.9 : ℝ) := by
    refine hple'.trans ?_
    rw [rpow_def_of_pos hx0]
    exact exp_le_exp.mpr (by linarith)
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  exact ⟨by linarith, by exact_mod_cast (by linarith : (2 : ℝ) < p), hup⟩

lemma coprime_of_large {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {M : ℕ} (hM : 0 < M)
    (hG : ∀ p ∈ groupPrimes x a, (M : ℝ) < p) {r : ℕ} (hr : IsGroupInteger x a r) :
    Nat.Coprime r M := by
  by_contra h
  obtain ⟨p, hp, hpr, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpr, hr.1.ne'⟩
  have := hG p (hr.2 p hmem)
  have : p ≤ M := Nat.le_of_dvd hM hpM
  have : (p : ℝ) ≤ M := by exact_mod_cast this
  linarith

lemma finite_le_J (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (F : Finset ℕ)
    (hF : ∀ r ∈ F, IsGroupInteger x a r) (hJ : 0 < harmonicMass x a) :
    ∑ r ∈ F, mark (1 / 2) x a r / r ≤ harmonicMass x a := by
  classical
  have hsum : Summable (fun r : {r : ℕ // IsGroupInteger x a r} => mark (1 / 2) x a r / r) := by
    by_contra h
    unfold harmonicMass at hJ
    rw [tsum_eq_zero_of_not_summable h] at hJ
    exact lt_irrefl _ hJ
  have h1 : ∑ r ∈ F, mark (1 / 2) x a r / r =
      ∑ r ∈ F.subtype (IsGroupInteger x a), mark (1 / 2) x a r / r := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun r : ℕ => mark (1 / 2) x a r / (r : ℝ)),
      filter_true_of_mem hF]
  rw [h1]
  exact hsum.sum_le_tsum _ (fun r _ => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _))

end

section
open Real Finset Filter Topology

lemma integral_one_two' {Ψ : ℝ → ℝ} (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) :
    ∫ y in (1 : ℝ)..2, Ψ y = ∫ y, Ψ y := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
  have := hΨs h
  exact ⟨this.1, this.2.le⟩

lemma harmonicMass_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : 0 ≤ harmonicMass x a :=
  tsum_nonneg fun r => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _)

end
open Real Classical in
theorem weighted_family_distribution_proof (M : ℕ) (hM : 0 < M) (h8 : 8 ∣ M)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    (∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      (∀ κ ε : ℝ, 0 < κ → κ < 0.01 → 0 < ε → ε < κ →
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
          ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
              mark (1 / 2) x a r *
                ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter
                    (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
                  |massRemainder M c u Ψ x r ℓ| ≤
            C * (x * harmonicMass x a * log x ^ (-A))) ∧
      (∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        |totalMass M c u Ψ x a -
            x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)| ≤
          η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)))) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        c₁ * (x * harmonicMass x a / log x) ≤ totalMass M c u Ψ x a ∧
          totalMass M c u Ψ x a ≤ c₂ * (x * harmonicMass x a / log x) := by
  have hasymp : ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
      IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        |totalMass M c u Ψ x a -
            x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)| ≤
          η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)) :=
    fun c u hc hu hcu hcop K hK a ha hai η hη =>
      mass_asymptotic M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK a ha hai η hη
  refine ⟨fun c u hc hu hcu hcop K hK a ha hai => ⟨?_, hasymp c u hc hu hcu hcop K hK a ha hai⟩,
    ?_⟩
  · -- the Bombieri–Vinogradov bound
    intro κ ε hκ hκ1 hε hεκ A hA
    obtain ⟨C, x₀, hC0, hC⟩ := single_r_remainders M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1
      κ ε A hκ hκ1 hε hεκ hA
    obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK
    obtain ⟨x₁, h₁⟩ := hCJ a ha hai ε hε
    obtain ⟨x₃, h₃⟩ := group_facts a hai M
    refine ⟨C, max (max x₀ x₁) (max x₃ 1), fun x hx => ?_⟩
    have hx0 : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx3 : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx4 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    obtain ⟨-, -, hJ1, -⟩ := h₁ x hx1
    set F := (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a) with hF
    have hmem : ∀ r ∈ F, IsGroupInteger x a r ∧ (r : ℝ) ≤ x ^ ε := by
      intro r hr
      rw [hF, Finset.mem_filter, Finset.mem_range] at hr
      exact ⟨hr.2, (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hr.1)).trans
        (Nat.floor_le (by positivity))⟩
    have hlogA : 0 ≤ log x ^ (-A) := rpow_nonneg (log_nonneg hx4) _
    calc ∑ r ∈ F, mark (1 / 2) x a r *
          ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            |massRemainder M c u Ψ x r ℓ|
        ≤ ∑ r ∈ F, mark (1 / 2) x a r * (C * (x / r * log x ^ (-A))) := by
          refine Finset.sum_le_sum fun r hr => ?_
          obtain ⟨hg, hrx⟩ := hmem r hr
          refine mul_le_mul_of_nonneg_left ?_ (mark_nonneg x a r)
          convert hC x hx0 r hg.1 hrx
            (coprime_of_large hM (fun p hp => (h₃ x hx3 p hp).1) hg) using 3
      _ = C * x * log x ^ (-A) * ∑ r ∈ F, mark (1 / 2) x a r / r := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ ≤ C * x * log x ^ (-A) * harmonicMass x a := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact finite_le_J x a F (fun r hr => (hmem r hr).1) (by linarith)
      _ = C * (x * harmonicMass x a * log x ^ (-A)) := by ring
  · -- the order of magnitude
    set AΨ := ∫ y in (1 : ℝ)..2, Ψ y with hAΨ_def
    have hAΨ : 0 < AΨ := by rw [hAΨ_def, integral_one_two' hΨs]; exact hΨi
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    refine ⟨AΨ / (8 * M), AΨ, by positivity, hAΨ, ?_⟩
    intro c u hc hu hcu hcop K hK a ha hai
    obtain ⟨x₀, h⟩ := hasymp c u hc hu hcu hcop K hK a ha hai (1 / 2) (by norm_num)
    refine ⟨max x₀ 3, fun x hx => ?_⟩
    have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
    have hab := abs_le.mp (h x (le_trans (le_max_left _ _) hx))
    set J := harmonicMass x a
    have hJ0 : 0 ≤ J := harmonicMass_nonneg x a
    have hL : 0 < log x := log_pos (by linarith)
    have hc2 : (2 : ℝ) ≤ c := by rcases hc with h | h <;> subst h <;> norm_num
    have hc4 : (c : ℝ) ≤ 4 := by rcases hc with h | h <;> subst h <;> norm_num
    have hφ1 : (1 : ℝ) ≤ Nat.totient (M / c) := by
      have hcM : c ∣ M := by
        rcases hc with h | h <;> subst h
        · exact (show 2 ∣ 8 by norm_num).trans h8
        · exact (show 4 ∣ 8 by norm_num).trans h8
      have hc0 : 0 < c := by rcases hc with h | h <;> omega
      exact_mod_cast Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hM hcM) hc0)
    have hφM : (Nat.totient (M / c) : ℝ) ≤ M := by
      exact_mod_cast (Nat.totient_le _).trans (Nat.div_le_self _ _)
    set Z := x * J / log x with hZ
    have hZ0 : 0 ≤ Z := by positivity
    set φ : ℝ := (Nat.totient (M / c) : ℝ) with hφdef
    have hB : x * J * AΨ / (c * φ * log x) = AΨ / (c * φ) * Z := by
      rw [hZ]; field_simp
    rw [hB] at hab
    have hcφ : 2 ≤ c * φ := by nlinarith
    have hcφ' : c * φ ≤ 4 * M := by nlinarith
    constructor
    · have h1 : AΨ / (8 * M) ≤ 1 / 2 * (AΨ / (c * φ)) := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 / 2 * (AΨ / (c * φ)) * (8 * M) = AΨ * (4 * M) / (c * φ) := by
          field_simp; ring
        rw [this, le_div_iff₀ (by positivity)]
        nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 hZ0
      nlinarith [hab.1]
    · have h1 : AΨ / (c * φ) ≤ AΨ / 2 := div_le_div_of_nonneg_left hAΨ.le (by norm_num) hcφ
      have h2 := mul_le_mul_of_nonneg_right h1 hZ0
      nlinarith [hab.2]

end ArtinPrimitiveRoots.WFDfin

open ArtinPrimitiveRoots ArtinPrimitiveRoots.WFDfin Real Classical in
theorem solution (M : ℕ) (hM : 0 < M) (h8 : 8 ∣ M)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    (∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      (∀ κ ε : ℝ, 0 < κ → κ < 0.01 → 0 < ε → ε < κ →
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
          ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
              mark (1 / 2) x a r *
                ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter
                    (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
                  |massRemainder M c u Ψ x r ℓ| ≤
            C * (x * harmonicMass x a * log x ^ (-A))) ∧
      (∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        |totalMass M c u Ψ x a -
            x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)| ≤
          η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)))) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        c₁ * (x * harmonicMass x a / log x) ≤ totalMass M c u Ψ x a ∧
          totalMass M c u Ψ x a ≤ c₂ * (x * harmonicMass x a / log x) := by
  apply ArtinPrimitiveRoots.WFDfin.weighted_family_distribution_proof <;> assumption
