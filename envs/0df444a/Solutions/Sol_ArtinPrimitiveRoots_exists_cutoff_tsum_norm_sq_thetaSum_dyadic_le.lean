-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T22:46:31.271883+00:00
-- url     : https://prove2.me/submissions/48ecf637-3516-4e4d-84e4-3a293a8aa905
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_powerful_le

section
namespace ArtinPrimitiveRoots

/-! L2D: abstract dyadic decomposition, used for (4.6) ⇐ (4.5). -/

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

lemma L2D_le_mono {s t : ℝ} (h : s ≤ t) : L2D_le F s ⊆ L2D_le F t := by
  intro I hI; rw [L2D_mem_le] at *; linarith

/-- `#{I : N I ≤ t} ≤ A t` for `t ≥ 1`. -/
lemma L2D_count : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 1 ≤ t → ((L2D_le F t).card : ℝ) ≤ A * t := by
  have hlim := NumberField.Ideal.tendsto_norm_le_div_atTop F
  set L := (2 ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
    Units.regulator F * classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|)
  have hev : ∀ᶠ s : ℝ in atTop,
      (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s < |L| + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith [le_abs_self L]))
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hev
  have hcard : ∀ t : ℝ, (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ t} : ℝ) =
      ((L2D_le F t).card : ℝ) := by
    intro t
    congr 1
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I => by simp)
  set s₁ := max s₀ 1
  have hs₁ : ((L2D_le F s₁).card : ℝ) ≤ (|L| + 1) * s₁ := by
    have h := hs₀ s₁ (le_max_left _ _)
    rw [hcard, div_lt_iff₀ (by positivity)] at h
    linarith
  have hL1 : 0 < |L| + 1 := by positivity
  refine ⟨(|L| + 1) * s₁, by positivity, fun t ht => ?_⟩
  by_cases hts : s₁ ≤ t
  · have h := hs₀ t (le_trans (le_max_left _ _) hts)
    rw [hcard, div_lt_iff₀ (by linarith)] at h
    have : (|L| + 1) * t ≤ (|L| + 1) * s₁ * t := by
      have : 1 ≤ s₁ := le_max_right _ _
      nlinarith
    linarith
  · push Not at hts
    have hsub := L2D_le_mono (F := F) hts.le
    have : ((L2D_le F t).card : ℝ) ≤ (L2D_le F s₁).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: candidate cuts beneath C1b (Proposition 4.1 (4.5)).

* `L2D_Cut64`: Lemma 6.4 (p. 38), the quadratic large sieve for `χ_𝔡(c)^3`
  (Goldmakher–Louvel, Thm 1.1).
* `L2D_Cut63`: Lemma 6.3 (p. 34) with (6.22) (p. 33), the reflected expansion of `B_m(Z)`, with
  the coefficients, row/column functions and profiles existentially quantified and only their
  stated bounds retained. -/

end ArtinPrimitiveRoots
end

section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

/-! ### `β_p` and the sum of `β_𝔣` -/

open Classical in
lemma L2D_simplePart_dvd (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ∣ 𝔟 := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  have hle : ((normalizedFactors 𝔟).toFinset.filter
      fun P => (normalizedFactors 𝔟).count P = 1).val ≤ normalizedFactors 𝔟 := by
    rw [Finset.filter_val, Multiset.toFinset_val]
    exact (Multiset.filter_le _ _).trans (Multiset.dedup_le _)
  have h1 := Multiset.prod_dvd_prod_of_le hle
  have h2 := prod_normalizedFactors h𝔟
  rw [associated_iff_eq] at h2
  rw [h2] at h1
  exact h1


lemma L2D_simplePart_ne_bot (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ≠ ⊥ := by
  intro h
  have hd := L2D_simplePart_dvd 𝔟 h𝔟
  rw [h] at hd
  exact h𝔟 (by simpa using zero_dvd_iff.1 (show (0 : Ideal (𝓞 F)) ∣ 𝔟 from hd))

open Classical in
lemma L2D_simplePart_nf (𝔟 : Ideal (𝓞 F)) :
    normalizedFactors (simplePart 𝔟) =
      ((normalizedFactors 𝔟).toFinset.filter fun P => (normalizedFactors 𝔟).count P = 1).val := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  apply normalizedFactors_prod_of_prime
  intro P hP
  rw [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset] at hP
  exact L2D_prime_of_mem hP.1

lemma L2D_simplePart_squarefree (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : Squarefree (simplePart 𝔟) := by
  classical
  rw [squarefree_iff_nodup_normalizedFactors (L2D_simplePart_ne_bot 𝔟 h𝔟), L2D_simplePart_nf]
  exact Finset.nodup _

/-- Powerful ideals: nonzero, every prime exponent `≥ 2`. -/
def L2D_Powerful (h : Ideal (𝓞 F)) : Prop :=
  h ≠ ⊥ ∧ ∀ P ∈ normalizedFactors h, 2 ≤ (normalizedFactors h).count P

lemma L2D_powerful_of_mul (𝔟 h : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) (hh : h * simplePart 𝔟 = 𝔟) :
    L2D_Powerful h := by
  classical
  have hh0 : h ≠ ⊥ := by
    rintro rfl; apply h𝔟; rw [← hh]; simp
  refine ⟨hh0, fun P hP => ?_⟩
  have hnf := normalizedFactors_mul hh0 (L2D_simplePart_ne_bot 𝔟 h𝔟)
  rw [hh, L2D_simplePart_nf] at hnf
  have hc := congr_arg (Multiset.count P) hnf
  rw [Multiset.count_add] at hc
  have hpos : 1 ≤ (normalizedFactors h).count P := Multiset.one_le_count_iff_mem.2 hP
  by_cases h1 : (normalizedFactors 𝔟).count P = 1
  · have hmem : P ∈ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨Multiset.one_le_count_iff_mem.1 (by omega), h1⟩
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 1 :=
      Multiset.count_eq_one_of_mem (Finset.nodup _) hmem
    omega
  · have hnm : P ∉ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter]; tauto
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 0 :=
      Multiset.count_eq_zero_of_notMem hnm
    omega

lemma L2D_exists_powerful (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ h, h * simplePart 𝔟 = 𝔟 := by
  obtain ⟨h, hh⟩ := L2D_simplePart_dvd 𝔟 h𝔟
  exact ⟨h, by rw [mul_comm]; exact hh.symm⟩

lemma L2D_powerful_decomp (h : Ideal (𝓞 F)) (hp : L2D_Powerful h) :
    ∃ r s : Ideal (𝓞 F), r ^ 2 * s ^ 3 = h := by
  classical
  set nf := normalizedFactors h
  let e : Ideal (𝓞 F) → ℕ := fun P => nf.count P
  refine ⟨∏ P ∈ nf.toFinset, P ^ ((e P - 3 * (e P % 2)) / 2),
    ∏ P ∈ nf.toFinset, P ^ (e P % 2), ?_⟩
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  have hprod : nf.prod = h := by
    have := prod_normalizedFactors hp.1
    rwa [associated_iff_eq] at this
  conv_rhs => rw [← hprod, Finset.prod_multiset_count]
  apply Finset.prod_congr rfl
  intro P hP
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  have h2 := hp.2 P (Multiset.mem_toFinset.1 hP)
  change 2 ≤ e P at h2
  change ((e P - 3 * (e P % 2)) / 2) * 2 + (e P % 2) * 3 = e P
  omega

open Classical in
/-- Powerful ideals of norm `≤ X` number `≪ X^{1/2}`. -/
lemma L2D_powerful_count : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    (((L2D_le F X).filter L2D_Powerful).card : ℝ) ≤ C * Real.sqrt X := by
  classical
  obtain ⟨A, hA, hcount⟩ := L2D_count (F := F)
  have hsum := T12B.summable_absNorm_rpow (F := F) (σ := 3 / 2) (by norm_num)
  set Zs := ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  have hZs : 0 ≤ Zs := tsum_nonneg fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨A * Zs + 1, by positivity, fun X hX => ?_⟩
  set Sset := (L2D_le F (X ^ ((1 : ℝ) / 3))).filter (· ≠ ⊥)
  let img : Ideal (𝓞 F) → Finset (Ideal (𝓞 F)) := fun s =>
    (L2D_le F (Real.sqrt (X / (Ideal.absNorm s : ℝ) ^ 3))).image fun r => r ^ 2 * s ^ 3
  have hsub : (L2D_le F X).filter L2D_Powerful ⊆ Sset.biUnion img := by
    intro h hh
    rw [Finset.mem_filter, L2D_mem_le] at hh
    obtain ⟨r, s, hrs⟩ := L2D_powerful_decomp h hh.2
    have hh0 := hh.2.1
    have hr0 : r ≠ ⊥ := by rintro rfl; apply hh0; rw [← hrs]; simp
    have hs0 : s ≠ ⊥ := by rintro rfl; apply hh0; rw [← hrs]; simp
    have hNr : (1 : ℝ) ≤ Ideal.absNorm r := by
      have : Ideal.absNorm r ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hNs : (1 : ℝ) ≤ Ideal.absNorm s := by
      have : Ideal.absNorm s ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hNh : (Ideal.absNorm h : ℝ) = (Ideal.absNorm r : ℝ) ^ 2 * (Ideal.absNorm s : ℝ) ^ 3 := by
      rw [← hrs, map_mul, map_pow, map_pow]; push_cast; ring
    have hs3 : (Ideal.absNorm s : ℝ) ^ 3 ≤ X := by
      have : (Ideal.absNorm s : ℝ) ^ 3 ≤ (Ideal.absNorm h : ℝ) := by
        rw [hNh]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hNr)
      linarith [hh.1]
    rw [Finset.mem_biUnion]
    refine ⟨s, ?_, ?_⟩
    · rw [Finset.mem_filter, L2D_mem_le]
      refine ⟨?_, hs0⟩
      have h3 : ((Ideal.absNorm s : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) ≤ X ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hs3
      rwa [← Real.rpow_mul (by positivity), show (3 : ℝ) * (1 / 3) = 1 by norm_num,
        Real.rpow_one] at h3
    · rw [Finset.mem_image]
      refine ⟨r, ?_, hrs⟩
      rw [L2D_mem_le]
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ (by positivity)]
      rw [← hNh]; exact hh.1
  have hcard : ((Sset.biUnion img).card : ℝ) ≤ ∑ s ∈ Sset, (A * Real.sqrt X) *
      ((Ideal.absNorm s : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc ((Sset.biUnion img).card : ℝ) ≤ ∑ s ∈ Sset, ((img s).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ s ∈ Sset, (A * Real.sqrt X) * ((Ideal.absNorm s : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_filter, L2D_mem_le] at hs
          have hNs : (1 : ℝ) ≤ Ideal.absNorm s := by
            have : Ideal.absNorm s ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hs.2
            exact_mod_cast Nat.one_le_iff_ne_zero.2 this
          have hs3 : (Ideal.absNorm s : ℝ) ^ 3 ≤ X := by
            have h1 := Real.rpow_le_rpow (by positivity) hs.1 (by norm_num : (0 : ℝ) ≤ 3)
            have e1 : (Ideal.absNorm s : ℝ) ^ (3 : ℝ) = (Ideal.absNorm s : ℝ) ^ 3 := by
              rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            have e2 : (X ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = X := by
              rw [← Real.rpow_mul (by linarith)]; norm_num
            rwa [e1, e2] at h1
          have ht : 1 ≤ Real.sqrt (X / (Ideal.absNorm s : ℝ) ^ 3) := by
            rw [Real.one_le_sqrt, le_div_iff₀ (by positivity)]; linarith
          calc ((img s).card : ℝ) ≤ (L2D_le F (Real.sqrt (X / (Ideal.absNorm s : ℝ) ^ 3))).card := by
                have := Finset.card_image_le
                  (s := L2D_le F (Real.sqrt (X / (Ideal.absNorm s : ℝ) ^ 3)))
                  (f := fun r => r ^ 2 * s ^ 3)
                exact Nat.cast_le.2 this
            _ ≤ A * Real.sqrt (X / (Ideal.absNorm s : ℝ) ^ 3) := hcount _ ht
            _ = (A * Real.sqrt X) * ((Ideal.absNorm s : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
                rw [Real.sqrt_div' _ (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
                  ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.rpow_neg (by positivity)]
                norm_num
                ring
  calc (((L2D_le F X).filter L2D_Powerful).card : ℝ) ≤ (Sset.biUnion img).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Sset, (A * Real.sqrt X) * ((Ideal.absNorm s : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := hcard
    _ = (A * Real.sqrt X) * ∑ s ∈ Sset, ((Ideal.absNorm s : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (A * Real.sqrt X) * Zs := by
        gcongr
        exact hsum.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (A * Zs + 1) * Real.sqrt X := by
        have := Real.sqrt_nonneg X
        nlinarith


end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: C1b ⇐ its dyadic conjunct (4.5). This is the last paragraph of the proof of
Proposition 4.1 (p. 41): (4.6) follows from (4.5) by summing over the `O((log Z)^2)` dyads. -/

/-- The candidate cut: Proposition 4.1 (4.5) alone, in class form (the first conjunct of C1b). -/
def L2D_Cut45 (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
      ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
        (∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
              P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
              (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))

variable {F : Type*} [Field F] [NumberField F]

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: row and column sets, the powerful part of a row. -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The retained columns: squarefree exterior ideals of norm `≤ R₀`. -/
noncomputable def L2D_cols (𝔪 : Ideal (𝓞 F)) (R0 : ℝ) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (L2D_le F R0).filter fun c => IsExterior 𝔪 c ∧ Squarefree c

lemma L2D_mem_cols {R0 : ℝ} {c : Ideal (𝓞 F)} :
    c ∈ L2D_cols 𝔪 R0 ↔ (Ideal.absNorm c : ℝ) ≤ R0 ∧ IsExterior 𝔪 c ∧ Squarefree c := by
  classical
  unfold L2D_cols; rw [Finset.mem_filter, L2D_mem_le]

/-- The powerful part of a row (a choice; unique). -/
noncomputable def L2D_hpart (𝔟 : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  if h : 𝔟 ≠ ⊥ then (L2D_exists_powerful 𝔟 h).choose else ⊥

lemma L2D_hpart_spec (𝔟 : Ideal (𝓞 F)) (h : 𝔟 ≠ ⊥) : L2D_hpart 𝔟 * simplePart 𝔟 = 𝔟 := by
  unfold L2D_hpart; rw [dif_pos h]; exact (L2D_exists_powerful 𝔟 h).choose_spec

/-- The powerful row ideals of norm `≤ 2P`. -/
noncomputable def L2D_Hset (F : Type*) [Field F] [NumberField F] (P : ℝ) :
    Finset (Ideal (𝓞 F)) := by
  classical
  exact (L2D_le F (2 * P)).filter L2D_Powerful

/-- The squarefree exterior rows of norm `≤ 2D`. -/
noncomputable def L2D_Rows (𝔪 : Ideal (𝓞 F)) (D : ℝ) : Finset (Ideal (𝓞 F)) := L2D_cols 𝔪 (2 * D)

lemma L2D_exterior_of_dvd {d 𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (hd : d ∣ 𝔟) :
    IsExterior 𝔪 d := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h𝔟.1 (zero_dvd_iff.1 hd)
  · have hle : 𝔟 ≤ d := Ideal.le_of_dvd hd
    rw [eq_top_iff, ← h𝔟.2]
    exact sup_le_sup_right hle _

lemma L2D_row_facts (r : RowClass 𝔪) {P D : ℝ} (hP : (Ideal.absNorm r.1.1 : ℝ) /
      Ideal.absNorm (simplePart r.1.1) < 2 * P)
    (hD : (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D) :
    L2D_hpart r.1.1 ∈ L2D_Hset F P ∧ simplePart r.1.1 ∈ L2D_Rows 𝔪 D ∧
      L2D_hpart r.1.1 * simplePart r.1.1 = r.1.1 := by
  classical
  have hb0 : r.1.1 ≠ ⊥ := r.1.2.1
  have hspec := L2D_hpart_spec r.1.1 hb0
  have hd0 := L2D_simplePart_ne_bot r.1.1 hb0
  have hpow := L2D_powerful_of_mul r.1.1 _ hb0 hspec
  refine ⟨?_, ?_, hspec⟩
  · unfold L2D_Hset
    rw [Finset.mem_filter, L2D_mem_le]
    refine ⟨?_, hpow⟩
    have hN : (Ideal.absNorm r.1.1 : ℝ) = Ideal.absNorm (L2D_hpart r.1.1) *
        Ideal.absNorm (simplePart r.1.1) := by
      conv_lhs => rw [← hspec]
      rw [map_mul]; push_cast; ring
    have hdpos : (0 : ℝ) < Ideal.absNorm (simplePart r.1.1) := by
      have : Ideal.absNorm (simplePart r.1.1) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      exact_mod_cast Nat.pos_of_ne_zero this
    rw [hN, mul_div_assoc, div_self hdpos.ne', mul_one] at hP
    linarith
  · unfold L2D_Rows
    rw [L2D_mem_cols]
    refine ⟨hD.le, L2D_exterior_of_dvd r.1.2 (L2D_simplePart_dvd r.1.1 hb0),
      L2D_simplePart_squarefree r.1.1 hb0⟩

/-- The per-powerful-part second moment (the statement `exists_cutoff_tsum_norm_sq_thetaSum_powerful_le`). -/
def L2D_CutH (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₂ ε : ℝ), 0 < ε →
      ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z → ∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
        ∀ (υ : SClass 𝔪) (𝔥 : Ideal (𝓞 F)), P ≤ (Ideal.absNorm 𝔥 : ℝ) →
          (Ideal.absNorm 𝔥 : ℝ) < 2 * P →
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 // r.2 = υ ∧
              𝔥 * simplePart r.1.1 = r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ ε * (D + D ^ 2 * P / Z)

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: `U_S / U_S^6` is finite (library 4956b3f7, the S-unit count). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_placesOf_finite (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  apply (Ideal.finite_factors h𝔪).subset
  intro v hv
  exact Ideal.dvd_iff_le.2 hv

lemma L2D_SClass_finite (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨_, (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have : Finite (placesOf 𝔪) := (L2D_placesOf_finite 𝔪 h𝔪).to_subtype
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  change Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: (4.5) from the per-powerful-part bound, by the count (6.39) of powerful ideals. -/

theorem L2D_cut45_of_cutH (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hH : L2D_CutH n F ι) : L2D_Cut45 n F ι := by
  classical
  obtain ⟨N₀, hN₀⟩ := hH
  refine ⟨N₀, fun 𝔪 h𝔪 hsp χ g c₁ c₂ ε hc₁ hε => ?_⟩
  obtain ⟨CH, hCH⟩ := hN₀ 𝔪 h𝔪 hsp χ g c₂ ε hε
  obtain ⟨Cpw, hCpw0, hCpw⟩ := L2D_powerful_count (F := F)
  have hSC := L2D_SClass_finite n hn0 hn 𝔪 h𝔪
  have hUfin : (Set.univ : Set (SClass 𝔪)).Finite := Set.finite_univ
  set U := hUfin.toFinset
  have hU : (U.card : ℝ) = Nat.card (SClass 𝔪) := by
    rw [← Nat.card_univ (α := SClass 𝔪), Nat.card_eq_card_finite_toFinset hUfin]
  refine ⟨Nat.card (SClass 𝔪) * Cpw * Real.sqrt 2 * max CH 0, fun Z hZ P D hP hD => ?_⟩
  have hZ0 : 0 < Z := by linarith
  set Y := Z ^ ε * (D + D ^ 2 * P / Z) with hYdef
  have hY : 0 ≤ Y := by
    have : 0 ≤ D + D ^ 2 * P / Z := by positivity
    positivity
  let Q : RowClass 𝔪 → Prop := fun r =>
    c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
    (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
    P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
    (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
    D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
    (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D
  have hfin : Finite {r : RowClass 𝔪 // Q r} := by
    let φ : {r : RowClass 𝔪 // Q r} →
        {x // x ∈ L2D_le F (c₂ * Z ^ ((1033 : ℝ) / 1000))} × SClass 𝔪 :=
      fun r => (⟨r.1.1.1, L2D_mem_le.2 r.2.2.1⟩, r.1.2)
    apply Finite.of_injective φ
    intro r r' hrr
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hrr
    exact Subtype.ext (Prod.ext (Subtype.ext hrr.1) hrr.2)
  have hSfin : Set.Finite {r : RowClass 𝔪 | Q r} := by
    have : Finite ({r : RowClass 𝔪 | Q r} : Set (RowClass 𝔪)) := hfin
    exact Set.toFinite _
  set S := hSfin.toFinset
  let f : RowClass 𝔪 → ℝ := fun r => ‖χ.thetaSum g (rowElt g r) Z‖ ^ 2
  refine ⟨∑ r ∈ S, f r, ?_, ?_⟩
  · have hind : HasSum ({r : RowClass 𝔪 | Q r}.indicator f) (∑ r ∈ S, f r) := by
      have h1 : ∑ r ∈ S, f r = ∑ r ∈ S, ({r : RowClass 𝔪 | Q r}.indicator f) r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Set.indicator_of_mem ((Set.Finite.mem_toFinset hSfin).1 hr)]
      rw [h1]
      apply hasSum_sum_of_ne_finset_zero
      intro r hr
      rw [Set.indicator_of_notMem]
      intro hm
      exact hr ((Set.Finite.mem_toFinset hSfin).2 hm)
    exact (hasSum_subtype_iff_indicator (f := f) (s := {r : RowClass 𝔪 | Q r})).2 hind
  -- the powerful parts of the dyad
  set H := (L2D_Hset F P).filter fun h => P ≤ (Ideal.absNorm h : ℝ) ∧ (Ideal.absNorm h : ℝ) < 2 * P
  let φ : RowClass 𝔪 → SClass 𝔪 × Ideal (𝓞 F) := fun r => (r.2, L2D_hpart r.1.1)
  have hmaps : ∀ r ∈ S, φ r ∈ U ×ˢ H := by
    intro r hr
    have hq := (Set.Finite.mem_toFinset hSfin).1 hr
    have hb0 : r.1.1 ≠ ⊥ := r.1.2.1
    have hspec := L2D_hpart_spec r.1.1 hb0
    obtain ⟨h1, _, _⟩ := L2D_row_facts r hq.2.2.2.1 hq.2.2.2.2.2
    have hd0 := L2D_simplePart_ne_bot r.1.1 hb0
    have hN : (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) =
        Ideal.absNorm (L2D_hpart r.1.1) := by
      have hdpos : (0 : ℝ) < Ideal.absNorm (simplePart r.1.1) := by
        have : Ideal.absNorm (simplePart r.1.1) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        exact_mod_cast Nat.pos_of_ne_zero this
      have e := congrArg (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ)) hspec
      simp only [map_mul, Nat.cast_mul] at e
      rw [← e, mul_div_assoc, div_self hdpos.ne', mul_one]
    rw [Finset.mem_product]
    refine ⟨(Set.Finite.mem_toFinset hUfin).2 (Set.mem_univ _), Finset.mem_filter.2 ⟨h1, ?_, ?_⟩⟩
    · show P ≤ (Ideal.absNorm (L2D_hpart r.1.1) : ℝ)
      rw [← hN]; exact hq.2.2.1
    · show (Ideal.absNorm (L2D_hpart r.1.1) : ℝ) < 2 * P
      rw [← hN]; exact hq.2.2.2.1
  have hfib : ∀ x ∈ U ×ˢ H, ∑ r ∈ S with φ r = x, f r ≤ max CH 0 * Y := by
    intro x hx
    rw [Finset.mem_product, Finset.mem_filter] at hx
    obtain ⟨σ, hσ, hσle⟩ := hCH Z hZ P D hP hD x.1 x.2 hx.2.2.1 hx.2.2.2
    let Qx : RowClass 𝔪 → Prop := fun r => r.2 = x.1 ∧ x.2 * simplePart r.1.1 = r.1.1 ∧
      (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
      D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧ (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D
    have hin : ∀ r ∈ S.filter (fun r => φ r = x), Qx r := by
      intro r hr
      rw [Finset.mem_filter] at hr
      have hq := (Set.Finite.mem_toFinset hSfin).1 hr.1
      have hφ := hr.2
      simp only [φ, Prod.ext_iff] at hφ
      refine ⟨hφ.1, ?_, hq.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩
      rw [← hφ.2]; exact L2D_hpart_spec r.1.1 r.1.2.1
    calc ∑ r ∈ S with φ r = x, f r
        = ∑ y ∈ (S.filter (fun r => φ r = x)).subtype Qx, f y.1 :=
          (Finset.sum_subtype_of_mem f hin).symm
      _ ≤ σ := sum_le_hasSum _ (fun _ _ => by positivity) hσ
      _ ≤ CH * Y := by rw [hYdef]; linarith [hσle]
      _ ≤ max CH 0 * Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
  have hHc : (H.card : ℝ) ≤ Cpw * (Real.sqrt 2 * P ^ ((1 : ℝ) / 2)) := by
    have h1 := hCpw (2 * P) (by linarith)
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow P] at h1
    have h2 : (H.card : ℝ) ≤ (L2D_Hset F P).card := by
      exact_mod_cast Finset.card_filter_le _ _
    refine h2.trans ?_
    unfold L2D_Hset
    convert h1 using 3
  have hm0 : 0 ≤ max CH 0 * Y := mul_nonneg (le_max_right _ _) hY
  calc ∑ r ∈ S, f r = ∑ x ∈ U ×ˢ H, ∑ r ∈ S with φ r = x, f r :=
        (Finset.sum_fiberwise_of_maps_to hmaps f).symm
    _ ≤ ∑ _x ∈ U ×ˢ H, max CH 0 * Y := Finset.sum_le_sum hfib
    _ = (U.card : ℝ) * H.card * (max CH 0 * Y) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
    _ ≤ (U.card : ℝ) * (Cpw * (Real.sqrt 2 * P ^ ((1 : ℝ) / 2))) * (max CH 0 * Y) := by
        gcongr
    _ = Nat.card (SClass 𝔪) * Cpw * Real.sqrt 2 * max CH 0 * Z ^ ε * P ^ ((1 : ℝ) / 2) *
          (D + D ^ 2 * P / Z) := by rw [hU, hYdef]; ring

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: (4.5) from the per-powerful-part bound. -/

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z → ∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
              P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
              (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) :=
  L2D_cut45_of_cutH n hn0 hn F ι (exists_cutoff_tsum_norm_sq_thetaSum_powerful_le n hn0 hn F ι)
end
