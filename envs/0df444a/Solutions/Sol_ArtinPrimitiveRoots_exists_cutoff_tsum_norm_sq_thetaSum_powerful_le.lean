-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_powerful_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T22:46:31.52099+00:00
-- url     : https://prove2.me/submissions/c2263e13-a188-4442-a050-3fb442790694
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_thetaSum_rowElt_eq_tsum
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le

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

/-- Dyadic harmonic bound: `∑_{N I ≤ X} 1/N I ≤ B (1 + log X)` for `X ≥ 1` (`1/0 = 0`). -/
lemma L2D_harmonic : ∃ B : ℝ, 0 < B ∧ ∀ X : ℝ, 1 ≤ X →
    ∑ I ∈ L2D_le F X, (1 / (Ideal.absNorm I : ℝ)) ≤ B * (1 + Real.log X) := by
  obtain ⟨A, hA, hcount⟩ := L2D_count (F := F)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * A * (1 + 1 / Real.log 2), by positivity, fun X hX => ?_⟩
  set K := Nat.log 2 ⌊X⌋₊
  -- fibre by the dyadic index of the norm
  have hmaps : ∀ I ∈ L2D_le F X, Nat.log 2 (Ideal.absNorm I) ∈ Finset.range (K + 1) := by
    intro I hI
    rw [L2D_mem_le] at hI
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.le_floor hI))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i ∈ Finset.range (K + 1),
      ∑ I ∈ L2D_le F X with Nat.log 2 (Ideal.absNorm I) = i, (1 / (Ideal.absNorm I : ℝ)) ≤
        2 * A := by
    intro i _
    have hterm : ∀ I ∈ {I ∈ L2D_le F X | Nat.log 2 (Ideal.absNorm I) = i},
        (1 / (Ideal.absNorm I : ℝ)) ≤ 1 / (2 : ℝ) ^ i := by
      intro I hI
      rw [Finset.mem_filter] at hI
      by_cases h0 : Ideal.absNorm I = 0
      · rw [h0]; simp
      · have := Nat.pow_log_le_self 2 h0
        rw [hI.2] at this
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast this
    have hsub : {I ∈ L2D_le F X | Nat.log 2 (Ideal.absNorm I) = i} ⊆ L2D_le F ((2 : ℝ) ^ (i + 1)) := by
      intro I hI
      rw [Finset.mem_filter] at hI
      rw [L2D_mem_le]
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ideal.absNorm I)
      rw [hI.2] at this
      have : (Ideal.absNorm I : ℝ) < ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hc : (({I ∈ L2D_le F X | Nat.log 2 (Ideal.absNorm I) = i}).card : ℝ) ≤
        A * (2 : ℝ) ^ (i + 1) := by
      calc (({I ∈ L2D_le F X | Nat.log 2 (Ideal.absNorm I) = i}).card : ℝ)
          ≤ (L2D_le F ((2 : ℝ) ^ (i + 1))).card := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ A * (2 : ℝ) ^ (i + 1) := hcount _ (one_le_pow₀ (by norm_num))
    calc ∑ I ∈ L2D_le F X with Nat.log 2 (Ideal.absNorm I) = i, (1 / (Ideal.absNorm I : ℝ))
        ≤ ∑ I ∈ L2D_le F X with Nat.log 2 (Ideal.absNorm I) = i, 1 / (2 : ℝ) ^ i :=
          Finset.sum_le_sum hterm
      _ = (({I ∈ L2D_le F X | Nat.log 2 (Ideal.absNorm I) = i}).card : ℝ) * (1 / (2 : ℝ) ^ i) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A * (2 : ℝ) ^ (i + 1) * (1 / (2 : ℝ) ^ i) := by gcongr
      _ = 2 * A := by rw [pow_succ]; field_simp
  calc ∑ i ∈ Finset.range (K + 1),
        ∑ I ∈ L2D_le F X with Nat.log 2 (Ideal.absNorm I) = i, (1 / (Ideal.absNorm I : ℝ))
      ≤ ∑ _i ∈ Finset.range (K + 1), 2 * A := Finset.sum_le_sum hfib
    _ = (K + 1) * (2 * A) := by simp
    _ ≤ (1 + Real.log X / Real.log 2) * (2 * A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hK : (K : ℝ) * Real.log 2 ≤ Real.log X := by
          by_cases h0 : ⌊X⌋₊ = 0
          · have : K = 0 := by simp [K, h0]
            rw [this]; simp; exact Real.log_nonneg hX
          · have h1 : (2 : ℝ) ^ K ≤ X := by
              calc (2 : ℝ) ^ K = ((2 ^ K : ℕ) : ℝ) := by push_cast; ring
                _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 h0
                _ ≤ X := Nat.floor_le (by linarith)
            have := Real.log_le_log (by positivity) h1
            rwa [Real.log_pow] at this
        have : (K : ℝ) ≤ Real.log X / Real.log 2 := by rw [le_div_iff₀ hl2]; exact hK
        linarith
    _ ≤ 2 * A * (1 + 1 / Real.log 2) * (1 + Real.log X) := by
        have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
        have : Real.log X / Real.log 2 = Real.log X * (1 / Real.log 2) := by ring
        rw [this]
        have h1 : 0 ≤ 1 / Real.log 2 := by positivity
        nlinarith [mul_nonneg hlX h1]

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

/-- `β_p(e)` of (6.20) (p. 33), at a prime of norm `q`. -/
noncomputable def L2D_betaP (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

open Classical in
/-- `β_𝔣(𝔞')` of (6.20): the product of `β_p(v_p(𝔞'))` over the primes `p ∣ 𝔣`, and `0` when
`𝔞'` has a prime factor outside `𝔣` (so it vanishes off `A(𝔣)`). -/
noncomputable def L2D_beta {F : Type*} [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)) : ℝ :=
  if ∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣 then
    ∏ P ∈ (normalizedFactors 𝔣).toFinset,
      L2D_betaP (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)
  else 0

/-- Lemma 6.4 (p. 38): for `C, D ≥ 1` and coefficients `z_𝔠` on squarefree exterior `𝔠` with
`q_𝔠 ≤ C`, `∑_{𝔡 sqfree, q_𝔡 ≤ D} |∑_𝔠 z_𝔠 χ_𝔡(c)^3|^2 ≪_ε (C + D)(CD)^ε ∑ |z_𝔠|^2`. -/
def L2D_Cut64 (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
        ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
            ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
          K * (C + D) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2

/-- Lemma 6.3 (p. 34) with (6.22): there are a finite slice set `T` (the classes `u, s_𝔡, s_𝔠`)
and, for each row-unit class `υ`, powerful part `𝔥`, active product `𝔣`, frozen ideals `𝔞', 𝔫'`
and slice `s`, a coefficient `ω` with `|ω| ≤ β_𝔣(𝔞')`, a row function `ρ` and a column function
`λ` of modulus `≤ 1`, and a profile `Φ` obeying (6.22) for `j ≤ 2` uniformly, such that for every
row class `m = (𝔟, ε)` with `𝔟 = 𝔥 𝔡`, `𝔡 = simplePart 𝔟`, and every `Z > 0`,
`B_m(Z) = ∑_{𝔣, 𝔞', 𝔫', s} ω/q_𝔫' · ρ(𝔡) ∑_{𝔠' sqfree} λ(𝔠') χ_𝔡(c')^3 q_𝔠'^{-1/2}
Φ(Z q_𝔞' q_𝔠' q_𝔫'^3/(q_𝔡^2 q_𝔣^2))`, where `𝔣` ranges over squarefree ideals with `𝔣^2 ∣ 𝔥`
(the coefficients vanish off `F(𝔥)`, off `A(𝔣)` and off `(𝔫', 𝔣) = 1`). -/
def L2D_Cut63 (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤ L2D_beta 𝔣 𝔞) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ Z : ℝ, 0 < Z →
        χ.thetaSum g (rowElt g r) Z =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2)))

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

/-- The number of distinct prime factors. -/
noncomputable def L2D_omega (I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).toFinset.card

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

lemma L2D_two_le_absNorm {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) :
    2 ≤ Ideal.absNorm P := by
  have hp := L2D_prime_of_mem hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro h; exact hp.not_isUnit (Ideal.isUnit_iff.2 h)
  omega

lemma L2D_eq_of_nf_eq {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : normalizedFactors a = normalizedFactors b) : a = b := by
  have h1 := prod_normalizedFactors ha
  have h2 := prod_normalizedFactors hb
  rw [associated_iff_eq] at h1 h2
  rw [← h1, ← h2, h]

lemma L2D_mem_nf_of_dvd {f Q : Ideal (𝓞 F)} (hf : f ≠ ⊥) (hQ : Prime Q) (hQf : Q ∣ f) :
    Q ∈ normalizedFactors f := by
  obtain ⟨Q', hQ', hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hQ.irreducible hQf
  rw [associated_iff_eq] at hassoc
  rwa [hassoc]

/-! ### `β_p` and the sum of `β_𝔣` -/

/-- The geometric constant bounding `∑_e β_p(e)`. -/
noncomputable def L2D_E0 : ℝ := 2 / (1 - (2 : ℝ) ^ (-(1 / 3 : ℝ)))

lemma L2D_r_lt_one : (2 : ℝ) ^ (-(1 / 3 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma L2D_r_pos : 0 < (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity

lemma L2D_E0_pos : 0 < L2D_E0 := by
  unfold L2D_E0
  have := L2D_r_lt_one
  apply div_pos (by norm_num); linarith

lemma L2D_betaP_nonneg (q : ℝ) (hq : 0 ≤ q) (e : ℕ) : 0 ≤ L2D_betaP q e := by
  unfold L2D_betaP
  split_ifs <;> first | exact Real.rpow_nonneg hq _ | norm_num

lemma L2D_betaP_le (q : ℝ) (hq : 2 ≤ q) (e : ℕ) :
    L2D_betaP q e ≤ 2 * ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e := by
  have hr : ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e = (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [hr]
  -- write e = 3k + j
  set k := e / 3 with hk
  have he : (e : ℝ) = 3 * k + (e % 3 : ℕ) := by
    have := Nat.div_add_mod e 3
    exact_mod_cast this.symm
  have hmod : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  -- `q^x ≤ 2^x` for `x ≤ 0`
  have hq2 : ∀ x : ℝ, x ≤ 0 → q ^ x ≤ (2 : ℝ) ^ x := fun x hx =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq hx
  unfold L2D_betaP
  split_ifs with h0 h1 h2
  · subst h0; norm_num
  · -- e = 3k + 1
    have hk' : (e : ℝ) = 3 * k + 1 := by rw [he, h1]; push_cast; ring
    calc q ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(k : ℝ)) := hq2 _ (by simp)
      _ ≤ 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk']
        have : (2 : ℝ) ^ (-(k : ℝ)) = 2 * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_one]; field_simp
        rw [this]
        gcongr
        · norm_num
        · linarith
  · -- e = 3k, k ≥ 1
    have hk' : (e : ℝ) = 3 * k := by rw [he, h2]; push_cast; ring
    have hk1 : (1 : ℝ) ≤ k := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    calc q ^ ((1 : ℝ) / 2 - k) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - k) := hq2 _ (by linarith)
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) - k) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk', Real.rpow_sub (by norm_num), Real.rpow_one]
        rw [show -(3 * (k : ℝ) / 3) = -(k : ℝ) by ring, Real.rpow_neg (by norm_num)]
        ring
  · positivity

lemma L2D_sum_betaP_le (q : ℝ) (hq : 2 ≤ q) (M : ℕ) :
    ∑ e ∈ Finset.range M, L2D_betaP q e ≤ L2D_E0 := by
  set r := (2 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr0 : 0 ≤ r := L2D_r_pos.le
  have hr1 : r < 1 := L2D_r_lt_one
  calc ∑ e ∈ Finset.range M, L2D_betaP q e ≤ ∑ e ∈ Finset.range M, 2 * r ^ e :=
        Finset.sum_le_sum fun e _ => L2D_betaP_le q hq e
    _ = 2 * ∑ e ∈ Finset.range M, r ^ e := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑' e : ℕ, r ^ e := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one hr0 hr1)
    _ = L2D_E0 := by rw [tsum_geometric_of_lt_one hr0 hr1]; unfold L2D_E0; ring

open Classical in
lemma L2D_beta_nonneg (𝔣 𝔞 : Ideal (𝓞 F)) : 0 ≤ L2D_beta 𝔣 𝔞 := by
  unfold L2D_beta
  split_ifs
  · exact Finset.prod_nonneg fun P _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  · exact le_rfl

open Classical in
/-- `∑_{𝔞 ∈ s} β_𝔣(𝔞) ≤ E₀^{ω(𝔣)}` for every finite set `s` of nonzero ideals. -/
lemma L2D_sum_beta_le (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ a ∈ s, a ≠ ⊥) :
    ∑ a ∈ s, L2D_beta 𝔣 a ≤ L2D_E0 ^ L2D_omega 𝔣 := by
  let Pf := (normalizedFactors 𝔣).toFinset
  let ι := {P // P ∈ Pf}
  let φ : Ideal (𝓞 F) → ι → ℕ := fun a P => (normalizedFactors a).count P.1
  let supp : Ideal (𝓞 F) → Prop := fun a => ∀ P ∈ normalizedFactors a, P ∣ 𝔣
  let s' := s.filter supp
  let M := ∑ a ∈ s', Multiset.card (normalizedFactors a) + 1
  let g : (ι → ℕ) → ℝ := fun e => ∏ i : ι, L2D_betaP (Ideal.absNorm i.1) (e i)
  have hβ : ∀ a ∈ s', L2D_beta 𝔣 a = g (φ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    unfold L2D_beta
    rw [if_pos ha.2]
    exact (Finset.prod_coe_sort Pf (fun P => L2D_betaP (Ideal.absNorm P)
      ((normalizedFactors a).count P))).symm
  have hzero : ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := by
    rw [Finset.sum_filter_of_ne]
    intro a _ hne
    by_contra hns
    apply hne
    unfold L2D_beta
    rw [if_neg hns]
  have hinj : Set.InjOn φ s' := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s'] at ha hb
    apply L2D_eq_of_nf_eq (hs a ha.1) (hs b hb.1)
    ext Q
    by_cases hQ : Q ∈ Pf
    · exact congr_fun hab ⟨Q, hQ⟩
    · have hQa : Q ∉ normalizedFactors a := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (ha.2 Q hm)))
      have hQb : Q ∉ normalizedFactors b := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (hb.2 Q hm)))
      rw [Multiset.count_eq_zero_of_notMem hQa, Multiset.count_eq_zero_of_notMem hQb]
  have hsub : s'.image φ ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have h1 : (normalizedFactors a).count i.1 ≤ Multiset.card (normalizedFactors a) :=
      Multiset.count_le_card _ _
    have h2 : Multiset.card (normalizedFactors a) ≤
        ∑ a ∈ s', Multiset.card (normalizedFactors a) :=
      Finset.single_le_sum (f := fun a => Multiset.card (normalizedFactors a))
        (fun _ _ => Nat.zero_le _) ha
    change (normalizedFactors a).count i.1 < M
    omega
  have hg0 : ∀ e, 0 ≤ g e := fun e =>
    Finset.prod_nonneg fun i _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  calc ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := hzero
    _ = ∑ a ∈ s', g (φ a) := Finset.sum_congr rfl hβ
    _ = ∑ e ∈ s'.image φ, g e := (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range M), g e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hg0 e
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, L2D_betaP (Ideal.absNorm i.1) n :=
        by rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, L2D_E0 := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun n _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
        · intro i _
          apply L2D_sum_betaP_le
          have := L2D_two_le_absNorm (Multiset.mem_toFinset.1 i.2)
          exact_mod_cast this
    _ = L2D_E0 ^ L2D_omega 𝔣 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]; rfl
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

lemma L2D_prod_primes_dvd (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    (normalizedFactors h).toFinset.prod id ∣ h := by
  classical
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id, Multiset.toFinset_val]
  have h1 := Multiset.prod_dvd_prod_of_le (Multiset.dedup_le (normalizedFactors h))
  have h2 := prod_normalizedFactors hh
  rw [associated_iff_eq] at h2
  rwa [h2] at h1

lemma L2D_prod_absNorm_primes_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    ∏ P ∈ (normalizedFactors h).toFinset, (Ideal.absNorm P : ℝ) ≤ Ideal.absNorm h := by
  have hd := L2D_prod_primes_dvd h hh
  have hN : Ideal.absNorm ((normalizedFactors h).toFinset.prod id) ∣ Ideal.absNorm h :=
    map_dvd Ideal.absNorm hd
  have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hN
  rw [map_prod] at this
  exact_mod_cast this

/-- `A^{ω(h)} ≪_{A,δ} N(h)^δ`. -/
lemma L2D_omega_bound (A : ℝ) (hA : 1 ≤ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Ideal (𝓞 F), h ≠ ⊥ →
      A ^ L2D_omega h ≤ C * (Ideal.absNorm h : ℝ) ^ δ := by
  classical
  set S0 := L2D_le F (A ^ (1 / δ))
  refine ⟨A ^ S0.card, by positivity, fun h hh => ?_⟩
  set Pf := (normalizedFactors h).toFinset
  have hsplit : A ^ L2D_omega h =
      (∏ P ∈ Pf.filter (· ∈ S0), A) * ∏ P ∈ Pf.filter (· ∉ S0), A := by
    rw [Finset.prod_filter_mul_prod_filter_not, Finset.prod_const]; rfl
  have h1 : ∏ P ∈ Pf.filter (· ∈ S0), A ≤ A ^ S0.card := by
    rw [Finset.prod_const]
    apply pow_le_pow_right₀ hA
    apply Finset.card_le_card
    intro P hP; exact (Finset.mem_filter.1 hP).2
  have hge1 : ∀ P ∈ Pf, 1 ≤ (Ideal.absNorm P : ℝ) ^ δ := by
    intro P hP
    apply Real.one_le_rpow _ hδ.le
    have := L2D_two_le_absNorm (Multiset.mem_toFinset.1 hP)
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm P)
  have h2 : ∏ P ∈ Pf.filter (· ∉ S0), A ≤ ∏ P ∈ Pf, (Ideal.absNorm P : ℝ) ^ δ := by
    calc ∏ P ∈ Pf.filter (· ∉ S0), A ≤ ∏ P ∈ Pf.filter (· ∉ S0), (Ideal.absNorm P : ℝ) ^ δ := by
          apply Finset.prod_le_prod (fun _ _ => by linarith)
          intro P hP
          rw [Finset.mem_filter] at hP
          have hnot := hP.2
          rw [L2D_mem_le, not_le] at hnot
          have := Real.rpow_le_rpow (by positivity) hnot.le hδ.le
          rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hδ.ne', Real.rpow_one] at this
      _ ≤ ∏ P ∈ Pf, (Ideal.absNorm P : ℝ) ^ δ := by
          rw [← Finset.prod_filter_mul_prod_filter_not Pf (· ∉ S0)]
          have hA0 : 0 ≤ ∏ P ∈ Pf.filter (· ∉ S0), (Ideal.absNorm P : ℝ) ^ δ :=
            Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
          have hB1 : 1 ≤ ∏ P ∈ Pf.filter (fun P => ¬ (P ∉ S0)), (Ideal.absNorm P : ℝ) ^ δ := by
            calc (1 : ℝ) = ∏ P ∈ Pf.filter (fun P => ¬ (P ∉ S0)), (1 : ℝ) := by simp
              _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
                  (fun P hP => hge1 P (Finset.mem_filter.1 hP).1)
          exact le_mul_of_one_le_right hA0 hB1
  have h3 : ∏ P ∈ Pf, (Ideal.absNorm P : ℝ) ^ δ ≤ (Ideal.absNorm h : ℝ) ^ δ := by
    rw [Real.finset_prod_rpow _ _ (fun P _ => Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
      (L2D_prod_absNorm_primes_le h hh) hδ.le
  rw [hsplit]
  have h0 : 0 ≤ ∏ P ∈ Pf.filter (· ∉ S0), A := Finset.prod_nonneg fun _ _ => by linarith
  calc (∏ P ∈ Pf.filter (· ∈ S0), A) * ∏ P ∈ Pf.filter (· ∉ S0), A
      ≤ A ^ S0.card * ∏ P ∈ Pf.filter (· ∉ S0), A := mul_le_mul_of_nonneg_right h1 h0
    _ ≤ A ^ S0.card * (Ideal.absNorm h : ℝ) ^ δ := by gcongr; exact h2.trans h3

lemma L2D_nf_subset_of_dvd {f h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (hfh : f ∣ h) :
    (normalizedFactors f).toFinset ⊆ (normalizedFactors h).toFinset := by
  classical
  intro P hP
  rw [Multiset.mem_toFinset] at *
  have hf : f ≠ ⊥ := by rintro rfl; exact hh (zero_dvd_iff.1 hfh)
  exact (dvd_iff_normalizedFactors_le_normalizedFactors hf hh).1 hfh |> Multiset.subset_of_le
    |> fun h => h hP

lemma L2D_omega_mono {f h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (hfh : f ∣ h) :
    L2D_omega f ≤ L2D_omega h :=
  Finset.card_le_card (L2D_nf_subset_of_dvd hh hfh)

/-- The admissible active products: squarefree `𝔣` with `𝔣² ∣ 𝔥`. -/
noncomputable def L2D_Fset (h : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (L2D_le F (Ideal.absNorm h)).filter fun f => Squarefree f ∧ f * f ∣ h

lemma L2D_mem_Fset {h f : Ideal (𝓞 F)} (hh : h ≠ ⊥) :
    f ∈ L2D_Fset h ↔ Squarefree f ∧ f * f ∣ h := by
  classical
  unfold L2D_Fset
  rw [Finset.mem_filter, L2D_mem_le]
  constructor
  · exact fun h => h.2
  · intro hf
    refine ⟨?_, hf⟩
    have hd : f ∣ h := (dvd_mul_right f f).trans hf.2
    have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (map_dvd Ideal.absNorm hd)

lemma L2D_card_Fset_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    (L2D_Fset h).card ≤ 2 ^ L2D_omega h := by
  classical
  have hinj : Set.InjOn (fun f : Ideal (𝓞 F) => (normalizedFactors f).toFinset)
      (L2D_Fset h : Set (Ideal (𝓞 F))) := by
    intro f hf f' hf' heq
    rw [Finset.mem_coe, L2D_mem_Fset hh] at hf hf'
    have hf0 : f ≠ ⊥ := hf.1.ne_zero
    have hf0' : f' ≠ ⊥ := hf'.1.ne_zero
    apply L2D_eq_of_nf_eq hf0 hf0'
    have n1 := (squarefree_iff_nodup_normalizedFactors hf0).1 hf.1
    have n2 := (squarefree_iff_nodup_normalizedFactors hf0').1 hf'.1
    rw [← Multiset.dedup_eq_self.2 n1, ← Multiset.dedup_eq_self.2 n2,
      ← Multiset.toFinset_val, ← Multiset.toFinset_val]
    exact congr_arg Finset.val heq
  calc (L2D_Fset h).card = ((L2D_Fset h).image
        fun f : Ideal (𝓞 F) => (normalizedFactors f).toFinset).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((normalizedFactors h).toFinset.powerset).card := by
        apply Finset.card_le_card
        intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨f, hf, rfl⟩ := ht
        rw [L2D_mem_Fset hh] at hf
        rw [Finset.mem_powerset]
        exact L2D_nf_subset_of_dvd hh ((dvd_mul_right f f).trans hf.2)
    _ = 2 ^ L2D_omega h := by rw [Finset.card_powerset]; rfl


end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

/-! L2D: Fourier separation of a profile in the log variable ((5.19), (6.43), simplified). -/

/-- The majorant `min(e^{αt}, e^{-t})` of (6.22) with `N = 1`. -/
noncomputable def L2D_maj (α t : ℝ) : ℝ := min (Real.exp (α * t)) (Real.exp (-(1 * t)))

lemma L2D_maj_nonneg (α t : ℝ) : 0 ≤ L2D_maj α t :=
  le_min (Real.exp_pos _).le (Real.exp_pos _).le

lemma L2D_maj_continuous (α : ℝ) : Continuous (L2D_maj α) := by
  unfold L2D_maj; fun_prop

lemma L2D_maj_integrable (α : ℝ) (hα : 0 < α) : Integrable (L2D_maj α) := by
  have hm : ∀ μ : Measure ℝ, AEStronglyMeasurable (L2D_maj α) μ :=
    fun μ => (L2D_maj_continuous α).aestronglyMeasurable
  have h1 : IntegrableOn (L2D_maj α) (Set.Iic 0) := by
    refine Integrable.mono' (integrableOn_exp_mul_Iic hα 0) (hm _)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (L2D_maj_nonneg α t)]
    exact min_le_left _ _
  have h2 : IntegrableOn (L2D_maj α) (Set.Ioi 0) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 one_pos) (hm _)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (L2D_maj_nonneg α t)]
    have := min_le_right (Real.exp (α * t)) (Real.exp (-(1 * t)))
    simpa [L2D_maj, neg_mul] using this
  have h := h1.union h2
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at h

lemma L2D_inv_integrable : Integrable fun τ : ℝ => (1 + (2 * π * τ) ^ 2)⁻¹ :=
  integrable_inv_one_add_sq.comp_mul_left' (by positivity)

/-- Fourier separation: a `C²` profile `Ψ` with `|Ψ^{(j)}(t)| ≤ C min(e^{αt}, e^{-t})` (`j ≤ 2`) is
the inverse Fourier transform of an integrable `𝓕Ψ` with `∫|𝓕Ψ| ≤ K(α, C)`. -/
lemma L2D_fourier_sep (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ψ : ℝ → ℂ, ContDiff ℝ 2 Ψ →
      (∀ j : ℕ, j ≤ 2 → ∀ t, ‖iteratedDeriv j Ψ t‖ ≤ C * L2D_maj α t) →
      Integrable (𝓕 Ψ) ∧ Continuous (𝓕 Ψ) ∧ (∫ τ, ‖𝓕 Ψ τ‖) ≤ K ∧
      ∀ u : ℝ, Ψ u = ∫ τ, 𝓕 Ψ τ * Complex.exp (2 * π * Complex.I * τ * u) := by
  set I0 := ∫ t, L2D_maj α t
  set J0 := ∫ τ : ℝ, (1 + (2 * π * τ) ^ 2)⁻¹
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => L2D_maj_nonneg α t
  have hJ0 : 0 ≤ J0 := integral_nonneg fun τ => by positivity
  refine ⟨2 * (C * I0) * J0, by positivity, fun Ψ hΨ hb => ?_⟩
  have hint : ∀ j : ℕ, j ≤ 2 → Integrable (iteratedDeriv j Ψ) := by
    intro j hj
    refine Integrable.mono' ((L2D_maj_integrable α hα).const_mul C)
      (hΨ.continuous_iteratedDeriv j (by exact_mod_cast hj)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => hb j hj t)
  have hΨi : Integrable Ψ := by simpa using hint 0 (by norm_num)
  have hΨc : Continuous Ψ := hΨ.continuous
  -- the L¹ bound for the derivatives
  have hL1 : ∀ j : ℕ, j ≤ 2 → ∫ t, ‖iteratedDeriv j Ψ t‖ ≤ C * I0 := by
    intro j hj
    calc ∫ t, ‖iteratedDeriv j Ψ t‖ ≤ ∫ t, C * L2D_maj α t :=
          integral_mono (hint j hj).norm ((L2D_maj_integrable α hα).const_mul C) (hb j hj)
      _ = C * I0 := integral_const_mul _ _
  have hF0 : ∀ τ, ‖𝓕 Ψ τ‖ ≤ C * I0 := by
    intro τ
    calc ‖𝓕 Ψ τ‖ ≤ ∫ t, ‖Ψ t‖ :=
          VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ ≤ C * I0 := by simpa using hL1 0 (by norm_num)
  have hF2 : ∀ τ, ‖(2 * π * τ : ℝ) ^ 2‖ * ‖𝓕 Ψ τ‖ ≤ C * I0 := by
    intro τ
    have hfd := Real.fourier_iteratedDeriv (f := Ψ) (N := 2) (n := 2) hΨ
      (fun n hn => hint n (by exact_mod_cast hn)) le_rfl
    have h := congr_fun hfd τ
    have hn : ‖𝓕 (iteratedDeriv 2 Ψ) τ‖ ≤ C * I0 :=
      (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans (hL1 2 le_rfl)
    rw [h, norm_smul] at hn
    have e : ‖(2 * π * Complex.I * τ) ^ 2‖ = ‖(2 * π * τ : ℝ) ^ 2‖ := by
      rw [norm_pow, norm_pow]
      congr 1
      rw [show (2 * π * Complex.I * τ) = Complex.I * ((2 * π * τ : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    rwa [e] at hn
  have hFb : ∀ τ, ‖𝓕 Ψ τ‖ ≤ 2 * (C * I0) * (1 + (2 * π * τ) ^ 2)⁻¹ := by
    intro τ
    have h1 := hF0 τ
    have h2 := hF2 τ
    rw [Real.norm_of_nonneg (by positivity)] at h2
    have hp : 0 < 1 + (2 * π * τ) ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    nlinarith
  have hFc : Continuous (𝓕 Ψ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simp only [innerₗ_apply_apply]; exact continuous_fst.inner continuous_snd) hΨi
  have hFi : Integrable (𝓕 Ψ) :=
    Integrable.mono' (L2D_inv_integrable.const_mul (2 * (C * I0))) hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  refine ⟨hFi, hFc, ?_, ?_⟩
  · calc ∫ τ, ‖𝓕 Ψ τ‖ ≤ ∫ τ, 2 * (C * I0) * (1 + (2 * π * τ) ^ 2)⁻¹ :=
          integral_mono hFi.norm (L2D_inv_integrable.const_mul _) hFb
      _ = 2 * (C * I0) * J0 := integral_const_mul _ _
  · intro u
    have hinv := hΨc.fourierInv_fourier_eq hΨi hFi
    conv_lhs => rw [← hinv]
    rw [Real.fourierInv_eq']
    congr 1
    funext τ
    rw [smul_eq_mul, mul_comm]
    congr 1
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 1: the data of Cut63 for fixed `𝔪, χ, g`, and the elementary bounds. -/

variable {F : Type*} [Field F] [NumberField F]

/-- The frozen keys `(𝔣, 𝔞', 𝔫', s)` of Lemma 6.3 for the powerful part `𝔥`. -/
abbrev L2D_Key (𝔪 : Ideal (𝓞 F)) (T : Type) (𝔥 : Ideal (𝓞 F)) : Type _ :=
  {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
    {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T

/-- The columns: squarefree exterior ideals. -/
abbrev L2D_Col (𝔪 : Ideal (𝓞 F)) : Type _ := {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠}

/-- The output of Cut63 for fixed `𝔪, χ, g`. -/
structure L2D_Data {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) where
  T : Type
  fT : Fintype T
  ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ
  ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → Ideal (𝓞 F) → ℂ
  lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → Ideal (𝓞 F) → ℂ
  Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ
  α : ℝ
  hα : 0 < α
  hω : ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤ L2D_beta 𝔣 𝔞
  hρ : ∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1
  hlam : ∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1
  hΦ : ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))
  hΦb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
    ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
      C * min (Real.exp (α * t)) (Real.exp (-(N * t)))
  hid : ∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
    ∀ Z : ℝ, 0 < Z →
      χ.thetaSum g (rowElt g r) Z =
        ∑' k : L2D_Key 𝔪 T 𝔥,
          ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
            ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
            ∑' 𝔠 : L2D_Col 𝔪,
              lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                  (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                      (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                    ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                      (Ideal.absNorm k.1.1 : ℝ) ^ 2))

attribute [instance] L2D_Data.fT

lemma L2D_data_of_cut (n : ℕ) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (h : L2D_Cut63 n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), Nonempty (L2D_Data χ g) := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨T, fT, ω, ρ, lam, Φ, α, hα, hω, hρ, hlam, hΦ, hΦb, hid⟩ := hN₀ 𝔪 h𝔪 hs χ g
  exact ⟨⟨T, fT, ω, ρ, lam, Φ, α, hα, hω, hρ, hlam, hΦ, hΦb, hid⟩⟩

/-! ### Elementary bounds -/

lemma L2D_norm_sext_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma L2D_norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (L2D_norm_sext_le ι 𝔪 P x) (norm_nonneg _) ih

lemma L2D_one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- From (6.22) with `j = 0`: `|Φ(x)| ≤ C x^{-N}` for `x > 0`. -/
lemma L2D_Phi_le {Φ : ℝ → ℂ} {α N C : ℝ}
    (hb : ∀ t : ℝ, ‖Φ (Real.exp t)‖ ≤ C * min (Real.exp (α * t)) (Real.exp (-(N * t))))
    {x : ℝ} (hx : 0 < x) : ‖Φ x‖ ≤ C * x ^ (-N) := by
  have h := hb (Real.log x)
  rw [Real.exp_log hx] at h
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans h
    by_contra hneg; push Not at hneg
    have : 0 < min (Real.exp (α * Real.log x)) (Real.exp (-(N * Real.log x))) :=
      lt_min (Real.exp_pos _) (Real.exp_pos _)
    nlinarith
  calc ‖Φ x‖ ≤ C * min (Real.exp (α * Real.log x)) (Real.exp (-(N * Real.log x))) := h
    _ ≤ C * Real.exp (-(N * Real.log x)) := by gcongr; exact min_le_right _ _
    _ = C * x ^ (-N) := by
        rw [Real.rpow_def_of_pos hx]; congr 1; ring_nf

/-- A finite partial sum over keys is bounded by a product of the factor bounds. -/
lemma L2D_key_sum_le {A B C' D : Type*} [Fintype D] (g : A × (B × (C' × D)) → ℝ)
    (u : A → B → ℝ) (v : C' → ℝ) (hu : ∀ a b, 0 ≤ u a b) (hv : ∀ c, 0 ≤ v c)
    (hgle : ∀ k, g k ≤ u k.1 k.2.1 * v k.2.2.1) (Ub V : ℝ)
    (hU : ∀ (sa : Finset A) (sb : Finset B), ∑ a ∈ sa, ∑ b ∈ sb, u a b ≤ Ub)
    (hV : ∀ sc : Finset C', ∑ c ∈ sc, v c ≤ V) (s : Finset (A × (B × (C' × D)))) :
    ∑ k ∈ s, g k ≤ Ub * V * Fintype.card D := by
  classical
  set sa := s.image Prod.fst
  set sb := s.image fun k => k.2.1
  set sc := s.image fun k => k.2.2.1
  have hsub : s ⊆ sa ×ˢ (sb ×ˢ (sc ×ˢ Finset.univ)) := by
    intro k hk
    simp only [Finset.mem_product, Finset.mem_univ, and_true, sa, sb, sc, Finset.mem_image]
    exact ⟨⟨k, hk, rfl⟩, ⟨k, hk, rfl⟩, ⟨k, hk, rfl⟩⟩
  have hV0 : 0 ≤ V := by simpa using hV ∅
  have hg' : ∀ k : A × (B × (C' × D)), 0 ≤ u k.1 k.2.1 * v k.2.2.1 :=
    fun k => mul_nonneg (hu _ _) (hv _)
  calc ∑ k ∈ s, g k ≤ ∑ k ∈ s, u k.1 k.2.1 * v k.2.2.1 := Finset.sum_le_sum fun k _ => hgle k
    _ ≤ ∑ k ∈ sa ×ˢ (sb ×ˢ (sc ×ˢ Finset.univ)), u k.1 k.2.1 * v k.2.2.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hg' k
    _ = (∑ a ∈ sa, ∑ b ∈ sb, u a b) * ((∑ c ∈ sc, v c) * Fintype.card D) := by
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro c _
        ring
    _ ≤ Ub * (V * Fintype.card D) := by
        have h1 : 0 ≤ ∑ a ∈ sa, ∑ b ∈ sb, u a b :=
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hu a b
        have h2 : 0 ≤ ∑ c ∈ sc, v c := Finset.sum_nonneg fun c _ => hv c
        apply mul_le_mul (hU sa sb) _ (by positivity) ((h1.trans (hU sa sb)))
        gcongr
        exact hV sc
    _ = Ub * V * Fintype.card D := by ring

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid
open scoped FourierTransform

/-! L2D core, part 2: the split of the reflected expansion into retained and tail parts. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

/-- The profile argument `Z q_𝔞' q_𝔠 q_𝔫'^3 / (q_𝔡^2 q_𝔣^2)`. -/
noncomputable def L2D_x {T : Type} {h : Ideal (𝓞 F)} (Z : ℝ) (d : Ideal (𝓞 F))
    (k : L2D_Key 𝔪 T h) (c : Ideal (𝓞 F)) : ℝ :=
  Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm c * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
    ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2)

/-- The length `Q = q_𝔞' q_𝔠 q_𝔫'^3` of (6.36). -/
noncomputable def L2D_Q {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) (c : Ideal (𝓞 F)) : ℝ :=
  Ideal.absNorm k.2.1.1 * Ideal.absNorm c * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3

section defs
variable (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (Z R0 : ℝ)

/-- The column term of (6.27). -/
noncomputable def L2D_term (k : L2D_Key 𝔪 Dd.T h) (c : L2D_Col 𝔪) : ℂ :=
  Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c.1 * residueSymbol ι 𝔪 d (g.gen c.1) ^ 3 /
    ((Real.sqrt (Ideal.absNorm c.1) : ℝ) : ℂ) *
    Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (L2D_x Z d k c.1)

/-- The row coefficient `ω/q_𝔫' · ρ(𝔡)`. -/
noncomputable def L2D_coef (k : L2D_Key 𝔪 Dd.T h) : ℂ :=
  Dd.ω υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
    Dd.ρ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 d

/-- The retained column sum (`Q ≤ R₀`). -/
noncomputable def L2D_RetC (k : L2D_Key 𝔪 Dd.T h) : ℂ :=
  ∑' c : L2D_Col 𝔪, if L2D_Q k c.1 ≤ R0 then L2D_term Dd υ h d Z k c else 0

/-- The discarded column sum (`Q > R₀`). -/
noncomputable def L2D_TailC (k : L2D_Key 𝔪 Dd.T h) : ℂ :=
  ∑' c : L2D_Col 𝔪, if L2D_Q k c.1 ≤ R0 then 0 else L2D_term Dd υ h d Z k c

/-- `Ret_{𝔥,𝔡}`. -/
noncomputable def L2D_RetT : ℂ :=
  ∑' k : L2D_Key 𝔪 Dd.T h, L2D_coef Dd υ h d k * L2D_RetC Dd υ h d Z R0 k

/-- `Tail_{𝔥,𝔡}`. -/
noncomputable def L2D_TailT : ℂ :=
  ∑' k : L2D_Key 𝔪 Dd.T h, L2D_coef Dd υ h d k * L2D_TailC Dd υ h d Z R0 k

end defs

/-! ### Basic positivity -/

lemma L2D_absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I :=
  lt_of_lt_of_le one_pos (L2D_one_le_absNorm hI)

lemma L2D_col_ne_bot (c : L2D_Col 𝔪) : c.1 ≠ ⊥ := c.2.1.1

lemma L2D_key_f_ne_bot {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) : k.1.1 ≠ ⊥ :=
  k.1.2.1.ne_zero

lemma L2D_key_n_ne_bot {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) : k.2.2.1.1 ≠ ⊥ :=
  k.2.2.1.2.1

lemma L2D_x_pos {T : Type} {h d : Ideal (𝓞 F)} {Z : ℝ} (hZ : 0 < Z) (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 T h) (c : L2D_Col 𝔪) : 0 < L2D_x Z d k c.1 := by
  unfold L2D_x
  have := L2D_absNorm_pos k.2.1.2
  have := L2D_absNorm_pos (L2D_col_ne_bot c)
  have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
  have := L2D_absNorm_pos hd
  have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
  positivity

lemma L2D_Q_ge_one {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) (c : L2D_Col 𝔪) :
    1 ≤ L2D_Q k c.1 := by
  unfold L2D_Q
  have h1 := L2D_one_le_absNorm k.2.1.2
  have h2 := L2D_one_le_absNorm (L2D_col_ne_bot c)
  have h3 := L2D_one_le_absNorm (L2D_key_n_ne_bot k)
  have h3' : 1 ≤ (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := one_le_pow₀ h3
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

lemma L2D_x_eq {T : Type} {h d : Ideal (𝓞 F)} (Z : ℝ) (k : L2D_Key 𝔪 T h) (c : Ideal (𝓞 F)) :
    L2D_x Z d k c = L2D_Q k c * (Z / ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2)) := by
  unfold L2D_x L2D_Q; ring

/-! ### The profile constants -/

lemma L2D_prof (Dd : L2D_Data χ g) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N) := by
  obtain ⟨C, hC⟩ := Dd.hΦb N hN
  refine ⟨max C 0, le_max_right _ _, fun υ h f a n s x hx => ?_⟩
  have h1 : ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N) := by
    apply L2D_Phi_le (α := Dd.α) _ hx
    intro t
    have := hC υ h f a n s 0 (by norm_num) t
    simpa [iteratedDeriv_zero] using this
  exact h1.trans (by gcongr; exact le_max_left _ _)

/-! ### Term bounds -/

lemma L2D_sqrt_inv_mul_inv (y : ℝ) (hy : 0 < y) :
    (Real.sqrt y)⁻¹ * y⁻¹ = y ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_neg_one, ← Real.rpow_add hy]
  norm_num

lemma L2D_term_norm_le (Dd : L2D_Data χ g) {N C : ℝ}
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N))
    (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ} (hZ : 0 < Z) (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 Dd.T h) (c : L2D_Col 𝔪) :
    ‖L2D_term Dd υ h d Z k c‖ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (L2D_x Z d k c.1) ^ (-N)) := by
  unfold L2D_term
  have hl := Dd.hlam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c.1
  have hr : ‖residueSymbol ι 𝔪 d (g.gen c.1) ^ 3‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (L2D_norm_residueSymbol_le ι 𝔪 d _)
  have hp := hC υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 _ (L2D_x_pos hZ hd k c)
  have hsq : 0 < Real.sqrt (Ideal.absNorm c.1) := Real.sqrt_pos.2 (L2D_absNorm_pos (L2D_col_ne_bot c))
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsq.le]
  have hC0 : 0 ≤ C * (L2D_x Z d k c.1) ^ (-N) := (norm_nonneg _).trans hp
  calc ‖Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c.1‖ *
          ‖residueSymbol ι 𝔪 d (g.gen c.1) ^ 3‖ / Real.sqrt (Ideal.absNorm c.1) *
        ‖Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (L2D_x Z d k c.1)‖
      ≤ 1 * 1 / Real.sqrt (Ideal.absNorm c.1) * (C * (L2D_x Z d k c.1) ^ (-N)) := by
        gcongr
    _ = (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (L2D_x Z d k c.1) ^ (-N)) := by ring

/-- The Dedekind-type sum `∑ N(I)^{-σ}` over all ideals. -/
noncomputable def L2D_zeta (F : Type*) [Field F] [NumberField F] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)

lemma L2D_col_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable fun c : L2D_Col 𝔪 => ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-σ) :=
  (T12B.summable_absNorm_rpow (F := F) hσ).comp_injective Subtype.val_injective

lemma L2D_col_tsum_le (σ : ℝ) (hσ : 1 < σ) :
    ∑' c : L2D_Col 𝔪, ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-σ) ≤ L2D_zeta F σ :=
  Summable.tsum_subtype_le (f := fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ))
    _ (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (T12B.summable_absNorm_rpow hσ)

/-- With `N = 1`: `|term| ≤ C (q_𝔡² q_𝔣²/Z) q_𝔠^{-3/2}`. -/
lemma L2D_term_norm_le_one (Dd : L2D_Data χ g) {C : ℝ}
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-(1 : ℝ)))
    (hC0 : 0 ≤ C) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ} (hZ : 0 < Z) (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 Dd.T h) (c : L2D_Col 𝔪) :
    ‖L2D_term Dd υ h d Z k c‖ ≤ C * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 / Z) *
      ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have h1 := L2D_term_norm_le Dd hC υ h d hZ hd k c
  have hc := L2D_absNorm_pos (L2D_col_ne_bot c)
  have hxpos := L2D_x_pos hZ hd k c
  set A := (Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 with hA
  have hApos : 0 < A := by
    have := L2D_absNorm_pos hd
    have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
    positivity
  have hx : (L2D_x Z d k c.1) ^ (-(1 : ℝ)) ≤ A / Z * (Ideal.absNorm c.1 : ℝ)⁻¹ := by
    rw [Real.rpow_neg_one, L2D_x_eq]
    have hQ : (Ideal.absNorm c.1 : ℝ) ≤ L2D_Q k c.1 := by
      unfold L2D_Q
      have h1 := L2D_one_le_absNorm k.2.1.2
      have h3 := one_le_pow₀ (n := 3) (L2D_one_le_absNorm (L2D_key_n_ne_bot k))
      calc (Ideal.absNorm c.1 : ℝ) = 1 * Ideal.absNorm c.1 * 1 := by ring
        _ ≤ _ := by gcongr
    rw [mul_inv, inv_div]
    rw [mul_comm]
    gcongr
  calc ‖L2D_term Dd υ h d Z k c‖ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (L2D_x Z d k c.1) ^ (-(1 : ℝ))) := h1
    _ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (A / Z * (Ideal.absNorm c.1 : ℝ)⁻¹)) := by gcongr
    _ = C * (A / Z) * ((Real.sqrt (Ideal.absNorm c.1))⁻¹ * (Ideal.absNorm c.1 : ℝ)⁻¹) := by ring
    _ = C * (A / Z) * ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [L2D_sqrt_inv_mul_inv _ hc]

lemma L2D_term_summable (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ}
    (hZ : 0 < Z) (hd : d ≠ ⊥) (k : L2D_Key 𝔪 Dd.T h) :
    Summable fun c => ‖L2D_term Dd υ h d Z k c‖ := by
  obtain ⟨C, hC0, hC⟩ := L2D_prof Dd 1 one_pos
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (L2D_term_norm_le_one Dd hC hC0 υ h d hZ hd k) ?_
  exact (L2D_col_summable (3 / 2) (by norm_num)).mul_left _

/-! ### Coefficient bounds -/

lemma L2D_coef_norm_le (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F))
    (k : L2D_Key 𝔪 Dd.T h) :
    ‖L2D_coef Dd υ h d k‖ ≤ L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ := by
  unfold L2D_coef
  rw [norm_mul, norm_div, Complex.norm_natCast]
  have h1 := Dd.hω υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
  have h2 := Dd.hρ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 d
  have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
  calc ‖Dd.ω υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2‖ / (Ideal.absNorm k.2.2.1.1 : ℝ) *
        ‖Dd.ρ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 d‖
      ≤ L2D_beta k.1.1 k.2.1.1 / (Ideal.absNorm k.2.2.1.1 : ℝ) * 1 := by
        gcongr; exact div_nonneg (L2D_beta_nonneg _ _) hn.le
    _ = _ := by ring

lemma L2D_E0_ge_one : 1 ≤ L2D_E0 := by
  unfold L2D_E0
  have h1 := L2D_r_pos
  have h2 := L2D_r_lt_one
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `∑_{𝔣 ∈ sa} ∑_{𝔞' ∈ sb} β_𝔣(𝔞') ≤ #F(𝔥) E₀^{ω(𝔥)}`. -/
lemma L2D_key_beta_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (sa : Finset {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ h})
    (sb : Finset {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥}) :
    ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ (L2D_Fset h).card * L2D_E0 ^ L2D_omega h := by
  classical
  have hinner : ∀ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ L2D_E0 ^ L2D_omega h := by
    intro f _
    have hf0 : f.1 ≠ ⊥ := f.2.1.ne_zero
    have h1 : ∑ a ∈ sb, L2D_beta f.1 a.1 = ∑ a ∈ sb.map (Function.Embedding.subtype _),
        L2D_beta f.1 a := by rw [Finset.sum_map]; rfl
    rw [h1]
    calc ∑ a ∈ sb.map (Function.Embedding.subtype _), L2D_beta f.1 a
        ≤ L2D_E0 ^ L2D_omega f.1 := by
          apply L2D_sum_beta_le f.1 hf0
          intro a ha
          rw [Finset.mem_map] at ha
          obtain ⟨a', _, rfl⟩ := ha
          exact a'.2
      _ ≤ L2D_E0 ^ L2D_omega h := pow_le_pow_right₀ L2D_E0_ge_one
          (L2D_omega_mono hh ((dvd_mul_right f.1 f.1).trans f.2.2))
  have hcard : sa.card ≤ (L2D_Fset h).card := by
    calc sa.card = (sa.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (L2D_Fset h).card := by
          apply Finset.card_le_card
          intro f hf
          rw [Finset.mem_map] at hf
          obtain ⟨f', _, rfl⟩ := hf
          exact (L2D_mem_Fset hh).2 f'.2
  calc ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ ∑ _f ∈ sa, L2D_E0 ^ L2D_omega h :=
        Finset.sum_le_sum hinner
    _ = sa.card * L2D_E0 ^ L2D_omega h := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L2D_Fset h).card * L2D_E0 ^ L2D_omega h := by
        gcongr
        · have := L2D_E0_pos; positivity

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 3: the tail estimate and the decomposition `B = Ret + Tail`. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

lemma L2D_absNorm_f_sq_le {T : Type} {h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (k : L2D_Key 𝔪 T h) :
    (Ideal.absNorm k.1.1 : ℝ) ^ 2 ≤ Ideal.absNorm h := by
  have hd : Ideal.absNorm (k.1.1 * k.1.1) ∣ Ideal.absNorm h := map_dvd Ideal.absNorm k.1.2.2
  have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd
  rw [map_mul] at this
  rw [sq]; exact_mod_cast this

/-- The tail term bound: for `Q > R₀ = Z^δ L`, `|term| ≤ C J^{-(N-1)} L q_𝔠^{-3/2} q_𝔫'^{-3}`,
with `J = max(Z^δ, 1/L)`. -/
lemma L2D_tail_term_le (Dd : L2D_Data χ g) {N C : ℝ} (hN : 1 ≤ N)
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N)) (hC0 : 0 ≤ C)
    (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hd : d ≠ ⊥) {Z δ L : ℝ} (hZ : 0 < Z)
    (hL : 0 < L) (htL : (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z ≤ L)
    (k : L2D_Key 𝔪 Dd.T h) (c : L2D_Col 𝔪) (hQ : ¬ L2D_Q k c.1 ≤ Z ^ δ * L) :
    ‖L2D_term Dd υ h d Z k c‖ ≤ C * (max (Z ^ δ) L⁻¹) ^ (-(N - 1)) * L *
      ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
  have h1 := L2D_term_norm_le Dd hC υ h d hZ hd k c
  have hc := L2D_absNorm_pos (L2D_col_ne_bot c)
  have hxpos := L2D_x_pos hZ hd k c
  set t := (Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 / Z with ht
  have htpos : 0 < t := by
    have := L2D_absNorm_pos hd
    have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
    positivity
  have htL' : t ≤ L := by
    refine le_trans ?_ htL
    rw [ht]
    gcongr
    exact L2D_absNorm_f_sq_le hh k
  have hx : L2D_x Z d k c.1 = L2D_Q k c.1 / t := by
    rw [L2D_x_eq, ht]; field_simp
  have hQ1 := L2D_Q_ge_one k c
  push Not at hQ
  have hZd : 0 < Z ^ δ := Real.rpow_pos_of_pos hZ δ
  set J := max (Z ^ δ) L⁻¹ with hJ
  have hJpos : 0 < J := lt_of_lt_of_le hZd (le_max_left _ _)
  have hxJ : J ≤ L2D_x Z d k c.1 := by
    rw [hx]
    apply max_le
    · rw [le_div_iff₀ htpos]
      calc Z ^ δ * t ≤ Z ^ δ * L := by gcongr
        _ ≤ L2D_Q k c.1 := hQ.le
    · rw [le_div_iff₀ htpos, inv_mul_le_iff₀ hL]
      nlinarith
  have hsplit : (L2D_x Z d k c.1) ^ (-N) =
      (L2D_x Z d k c.1) ^ (-(N - 1)) * (L2D_x Z d k c.1) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hxpos]; ring_nf
  have hpow : (L2D_x Z d k c.1) ^ (-(N - 1)) ≤ J ^ (-(N - 1)) :=
    Real.rpow_le_rpow_of_nonpos hJpos hxJ (by linarith)
  have hinv : (L2D_x Z d k c.1) ^ (-(1 : ℝ)) ≤
      L * ((Ideal.absNorm c.1 : ℝ)⁻¹ * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by
    rw [Real.rpow_neg_one, hx, inv_div]
    have hQ' : (Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 ≤ L2D_Q k c.1 := by
      unfold L2D_Q
      have h1 := L2D_one_le_absNorm k.2.1.2
      have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
      calc (Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3
          = 1 * Ideal.absNorm c.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := by ring
        _ ≤ _ := by gcongr
    have hpos : 0 < (Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := by
      have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
      positivity
    rw [← mul_inv]
    calc t / L2D_Q k c.1 ≤ L / ((Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3) := by
          gcongr
      _ = _ := by rw [div_eq_mul_inv]
  have hJ0 : 0 ≤ J ^ (-(N - 1)) := Real.rpow_nonneg hJpos.le _
  calc ‖L2D_term Dd υ h d Z k c‖ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (L2D_x Z d k c.1) ^ (-N)) := h1
    _ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (J ^ (-(N - 1)) *
          (L * ((Ideal.absNorm c.1 : ℝ)⁻¹ * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹)))) := by
        rw [hsplit]
        gcongr
    _ = C * J ^ (-(N - 1)) * L * ((Real.sqrt (Ideal.absNorm c.1))⁻¹ * (Ideal.absNorm c.1 : ℝ)⁻¹) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by ring
    _ = _ := by rw [L2D_sqrt_inv_mul_inv _ hc]

lemma L2D_ite_summable (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ}
    (hZ : 0 < Z) (hd : d ≠ ⊥) (k : L2D_Key 𝔪 Dd.T h) (p : L2D_Col 𝔪 → Prop) [DecidablePred p] :
    Summable fun c => ‖if p c then L2D_term Dd υ h d Z k c else 0‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun c => by split_ifs <;> simp) (L2D_term_summable Dd υ h d hZ hd k)

lemma L2D_ite_summable' (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ}
    (hZ : 0 < Z) (hd : d ≠ ⊥) (k : L2D_Key 𝔪 Dd.T h) (p : L2D_Col 𝔪 → Prop) [DecidablePred p] :
    Summable fun c => ‖if p c then 0 else L2D_term Dd υ h d Z k c‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun c => by split_ifs <;> simp) (L2D_term_summable Dd υ h d hZ hd k)

/-- `|TailC| ≤ C J^{-(N-1)} L ζ(3/2) q_𝔫'^{-3}`. -/
lemma L2D_TailC_le (Dd : L2D_Data χ g) {N C : ℝ} (hN : 1 ≤ N)
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N)) (hC0 : 0 ≤ C)
    (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hd : d ≠ ⊥) {Z δ L : ℝ} (hZ : 0 < Z)
    (hL : 0 < L) (htL : (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z ≤ L)
    (k : L2D_Key 𝔪 Dd.T h) :
    ‖L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖ ≤ C * (max (Z ^ δ) L⁻¹) ^ (-(N - 1)) * L *
      L2D_zeta F (3 / 2) * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
  classical
  unfold L2D_TailC
  set M := C * (max (Z ^ δ) L⁻¹) ^ (-(N - 1)) * L with hM
  have hM0 : 0 ≤ M := by
    have : 0 < max (Z ^ δ) L⁻¹ := lt_of_lt_of_le (Real.rpow_pos_of_pos hZ δ) (le_max_left _ _)
    have := Real.rpow_nonneg this.le (-(N - 1))
    positivity
  have hn3 : 0 ≤ ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by positivity
  have hsum := L2D_ite_summable' Dd υ h d hZ hd k (fun c => L2D_Q k c.1 ≤ Z ^ δ * L)
  have hcs := L2D_col_summable (𝔪 := 𝔪) (3 / 2) (by norm_num)
  calc ‖∑' c : L2D_Col 𝔪, if L2D_Q k c.1 ≤ Z ^ δ * L then 0 else L2D_term Dd υ h d Z k c‖
      ≤ ∑' c : L2D_Col 𝔪, ‖if L2D_Q k c.1 ≤ Z ^ δ * L then 0 else L2D_term Dd υ h d Z k c‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' c : L2D_Col 𝔪, M * ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
        refine Summable.tsum_le_tsum (fun c => ?_) hsum ((hcs.mul_left M).mul_right _)
        split_ifs with hq
        · rw [norm_zero]
          have := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm c.1)) (-(3 / 2 : ℝ))
          positivity
        · exact L2D_tail_term_le Dd hN hC hC0 υ h d hh hd hZ hL htL k c hq
    _ = M * (∑' c : L2D_Col 𝔪, ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ M * L2D_zeta F (3 / 2) * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
        gcongr
        exact L2D_col_tsum_le (3 / 2) (by norm_num)

lemma L2D_ext_sum_le_zeta (σ : ℝ) (hσ : 1 < σ) (sc : Finset {n : Ideal (𝓞 F) // IsExterior 𝔪 n}) :
    ∑ n ∈ sc, ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-σ) ≤ L2D_zeta F σ := by
  have h1 : ∑ n ∈ sc, ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-σ) =
      ∑ x ∈ sc.map (Function.Embedding.subtype _), ((Ideal.absNorm x : ℕ) : ℝ) ^ (-σ) := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  exact (T12B.summable_absNorm_rpow hσ).sum_le_tsum _
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma L2D_ext_harm_le (X : ℝ) (sc : Finset {n : Ideal (𝓞 F) // IsExterior 𝔪 n}) :
    ∑ n ∈ sc, (if (Ideal.absNorm n.1 : ℝ) ≤ X then (Ideal.absNorm n.1 : ℝ)⁻¹ else 0) ≤
      ∑ I ∈ L2D_le F X, (1 / (Ideal.absNorm I : ℝ)) := by
  classical
  rw [← Finset.sum_filter]
  have h1 : ∑ n ∈ sc.filter (fun n => (Ideal.absNorm n.1 : ℝ) ≤ X), (Ideal.absNorm n.1 : ℝ)⁻¹ =
      ∑ x ∈ (sc.filter (fun n => (Ideal.absNorm n.1 : ℝ) ≤ X)).map (Function.Embedding.subtype _),
        (1 / (Ideal.absNorm x : ℝ)) := by
    rw [Finset.sum_map]; simp
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [Finset.mem_filter] at hn
    rw [L2D_mem_le]; exact hn.2
  · intro _ _ _; positivity

lemma L2D_rpow_four (n : ℝ) (hn : 0 < n) : n⁻¹ * (n ^ 3)⁻¹ = n ^ (-(4 : ℝ)) := by
  rw [Real.rpow_neg hn.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← mul_inv]
  ring

/-- The discarded part: summable over the keys, with
`|Tail_{𝔥,𝔡}| ≤ C J^{-(N-1)} L ζ(3/2) · #F(𝔥) E₀^{ω(𝔥)} · ζ(4) · |T|`. -/
lemma L2D_TailT_le (Dd : L2D_Data χ g) {N C : ℝ} (hN : 1 ≤ N)
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-N)) (hC0 : 0 ≤ C)
    (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hd : d ≠ ⊥) {Z δ L : ℝ} (hZ : 0 < Z)
    (hL : 0 < L) (htL : (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z ≤ L) :
    Summable (fun k : L2D_Key 𝔪 Dd.T h =>
        ‖L2D_coef Dd υ h d k * L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖) ∧
      ‖L2D_TailT Dd υ h d Z (Z ^ δ * L)‖ ≤
        C * (max (Z ^ δ) L⁻¹) ^ (-(N - 1)) * L * L2D_zeta F (3 / 2) *
          ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) * L2D_zeta F 4 * Fintype.card Dd.T := by
  set M := C * (max (Z ^ δ) L⁻¹) ^ (-(N - 1)) * L * L2D_zeta F (3 / 2) with hM
  have hM0 : 0 ≤ M := by
    have : 0 < max (Z ^ δ) L⁻¹ := lt_of_lt_of_le (Real.rpow_pos_of_pos hZ δ) (le_max_left _ _)
    have := Real.rpow_nonneg this.le (-(N - 1))
    have : 0 ≤ L2D_zeta F (3 / 2) := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hkey : ∀ k : L2D_Key 𝔪 Dd.T h,
      ‖L2D_coef Dd υ h d k * L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖ ≤
        (M * L2D_beta k.1.1 k.2.1.1) * ((Ideal.absNorm k.2.2.1.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) := by
    intro k
    rw [norm_mul]
    have h1 := L2D_coef_norm_le Dd υ h d k
    have h2 := L2D_TailC_le Dd hN hC hC0 υ h d hh hd (δ := δ) hZ hL htL k
    have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
    have hb := L2D_beta_nonneg k.1.1 k.2.1.1
    calc ‖L2D_coef Dd υ h d k‖ * ‖L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖
        ≤ (L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹) *
          (M * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by
          apply mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (M * L2D_beta k.1.1 k.2.1.1) * ((Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by ring
      _ = _ := by rw [L2D_rpow_four _ hn]
  have hpart : ∀ s : Finset (L2D_Key 𝔪 Dd.T h),
      ∑ k ∈ s, ‖L2D_coef Dd υ h d k * L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖ ≤
        (M * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) * L2D_zeta F 4 * Fintype.card Dd.T := by
    intro s
    apply L2D_key_sum_le _ (fun f a => M * L2D_beta f.1 a.1)
      (fun n => ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-(4 : ℝ)))
      (fun f a => mul_nonneg hM0 (L2D_beta_nonneg _ _))
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hkey
    · intro sa sb
      calc ∑ f ∈ sa, ∑ a ∈ sb, M * L2D_beta f.1 a.1 = M * ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 := by
            rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ M * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) := by
            gcongr; exact L2D_key_beta_le h hh sa sb
    · intro sc; exact L2D_ext_sum_le_zeta 4 (by norm_num) sc
  have hsum := summable_of_sum_le (fun k => norm_nonneg _) hpart
  refine ⟨hsum, ?_⟩
  calc ‖L2D_TailT Dd υ h d Z (Z ^ δ * L)‖
      ≤ ∑' k, ‖L2D_coef Dd υ h d k * L2D_TailC Dd υ h d Z (Z ^ δ * L) k‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ (M * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) * L2D_zeta F 4 * Fintype.card Dd.T :=
        Real.tsum_le_of_sum_le (fun k => norm_nonneg _) hpart
    _ = _ := by rw [hM]

/-- The retained column sum vanishes unless `q_𝔫' ≤ R₀`. -/
lemma L2D_RetC_eq_zero (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (Z R0 : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) (hk : ¬ (Ideal.absNorm k.2.2.1.1 : ℝ) ≤ R0) :
    L2D_RetC Dd υ h d Z R0 k = 0 := by
  unfold L2D_RetC
  have hz : (fun c : L2D_Col 𝔪 => if L2D_Q k c.1 ≤ R0 then L2D_term Dd υ h d Z k c else 0) =
      fun _ => 0 := by
    funext c
    rw [if_neg]
    intro hQ
    apply hk
    refine le_trans ?_ hQ
    unfold L2D_Q
    have h1 := L2D_one_le_absNorm k.2.1.2
    have h2 := L2D_one_le_absNorm (L2D_col_ne_bot c)
    have h3 := L2D_one_le_absNorm (L2D_key_n_ne_bot k)
    have h4 : (Ideal.absNorm k.2.2.1.1 : ℝ) ≤ (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := by
      calc (Ideal.absNorm k.2.2.1.1 : ℝ) = Ideal.absNorm k.2.2.1.1 * 1 * 1 := by ring
        _ ≤ Ideal.absNorm k.2.2.1.1 * Ideal.absNorm k.2.2.1.1 * Ideal.absNorm k.2.2.1.1 := by
          gcongr
        _ = _ := by ring
    calc (Ideal.absNorm k.2.2.1.1 : ℝ) ≤ 1 * 1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := by linarith
      _ ≤ _ := by gcongr
  rw [hz, tsum_zero]

/-- With `N = 1`, keeping the `𝔫'` decay: `|term| ≤ C (q_𝔡² q_𝔣²/Z) q_𝔠^{-3/2} q_𝔫'^{-3}`. -/
lemma L2D_term_norm_le_one' (Dd : L2D_Data χ g) {C : ℝ}
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-(1 : ℝ)))
    (hC0 : 0 ≤ C) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) {Z : ℝ} (hZ : 0 < Z) (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 Dd.T h) (c : L2D_Col 𝔪) :
    ‖L2D_term Dd υ h d Z k c‖ ≤ C * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 / Z) *
      ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
  have h1 := L2D_term_norm_le Dd hC υ h d hZ hd k c
  have hc := L2D_absNorm_pos (L2D_col_ne_bot c)
  have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
  set A := (Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 with hA
  have hApos : 0 < A := by
    have := L2D_absNorm_pos hd
    have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
    positivity
  have hx : (L2D_x Z d k c.1) ^ (-(1 : ℝ)) ≤
      A / Z * ((Ideal.absNorm c.1 : ℝ)⁻¹ * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by
    rw [Real.rpow_neg_one, L2D_x_eq]
    have hQ : (Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 ≤ L2D_Q k c.1 := by
      unfold L2D_Q
      have h1 := L2D_one_le_absNorm k.2.1.2
      calc (Ideal.absNorm c.1 : ℝ) * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3
          = 1 * Ideal.absNorm c.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 := by ring
        _ ≤ _ := by gcongr
    rw [mul_inv, inv_div, ← mul_inv, mul_comm]
    gcongr
  calc ‖L2D_term Dd υ h d Z k c‖ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ * (C * (L2D_x Z d k c.1) ^ (-(1 : ℝ))) := h1
    _ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ *
          (C * (A / Z * ((Ideal.absNorm c.1 : ℝ)⁻¹ * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹))) := by
        gcongr
    _ = C * (A / Z) * ((Real.sqrt (Ideal.absNorm c.1))⁻¹ * (Ideal.absNorm c.1 : ℝ)⁻¹) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by ring
    _ = _ := by rw [L2D_sqrt_inv_mul_inv _ hc]

/-- Any column sum dominated by the terms: `|∑ w| ≤ C (q_𝔡² q_𝔥/Z) ζ(3/2) q_𝔫'^{-3}`. -/
lemma L2D_colsum_norm_le (Dd : L2D_Data χ g) {C : ℝ}
    (hC : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ C * x ^ (-(1 : ℝ)))
    (hC0 : 0 ≤ C) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hd : d ≠ ⊥) {Z : ℝ}
    (hZ : 0 < Z) (k : L2D_Key 𝔪 Dd.T h) (w : L2D_Col 𝔪 → ℂ)
    (hw : ∀ c, ‖w c‖ ≤ ‖L2D_term Dd υ h d Z k c‖) :
    ‖∑' c, w c‖ ≤ C * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z) * L2D_zeta F (3 / 2) *
      ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
  have hsum : Summable fun c => ‖w c‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hw (L2D_term_summable Dd υ h d hZ hd k)
  have hcs := L2D_col_summable (𝔪 := 𝔪) (3 / 2) (by norm_num)
  set A := C * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z)
  have hA : C * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 / Z) ≤ A := by
    apply mul_le_mul_of_nonneg_left _ hC0
    apply div_le_div_of_nonneg_right _ hZ.le
    exact mul_le_mul_of_nonneg_left (L2D_absNorm_f_sq_le hh k) (by positivity)
  have hA0 : 0 ≤ A := by positivity
  have hn3 : 0 ≤ ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by positivity
  calc ‖∑' c, w c‖ ≤ ∑' c, ‖w c‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' c : L2D_Col 𝔪, A * ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
        refine Summable.tsum_le_tsum (fun c => ?_) hsum ((hcs.mul_left A).mul_right _)
        refine (hw c).trans ((L2D_term_norm_le_one' Dd hC hC0 υ h d hZ hd k c).trans ?_)
        have := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm c.1)) (-(3 / 2 : ℝ))
        gcongr
    _ = A * (∑' c : L2D_Col 𝔪, ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by rw [tsum_mul_right, tsum_mul_left]
    _ ≤ A * L2D_zeta F (3 / 2) * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
        gcongr; exact L2D_col_tsum_le (3 / 2) (by norm_num)

/-- Key sums `k ↦ coef_k · (∑ w_k)` with `w_k` dominated by the terms are absolutely summable. -/
lemma L2D_keysum_summable (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (hd : d ≠ ⊥) {Z : ℝ} (hZ : 0 < Z) (w : L2D_Key 𝔪 Dd.T h → L2D_Col 𝔪 → ℂ)
    (hw : ∀ k c, ‖w k c‖ ≤ ‖L2D_term Dd υ h d Z k c‖) :
    Summable (fun k : L2D_Key 𝔪 Dd.T h => ‖L2D_coef Dd υ h d k * ∑' c, w k c‖) := by
  obtain ⟨C, hC0, hC⟩ := L2D_prof Dd 1 one_pos
  set M := C * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z) * L2D_zeta F (3 / 2)
  have hM0 : 0 ≤ M := by
    have : 0 ≤ L2D_zeta F (3 / 2) := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hkey : ∀ k : L2D_Key 𝔪 Dd.T h, ‖L2D_coef Dd υ h d k * ∑' c, w k c‖ ≤
      (M * L2D_beta k.1.1 k.2.1.1) * ((Ideal.absNorm k.2.2.1.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) := by
    intro k
    rw [norm_mul]
    have h1 := L2D_coef_norm_le Dd υ h d k
    have h2 := L2D_colsum_norm_le Dd hC hC0 υ h d hh hd hZ k (w k) (hw k)
    have hb := L2D_beta_nonneg k.1.1 k.2.1.1
    have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
    calc ‖L2D_coef Dd υ h d k‖ * ‖∑' c, w k c‖
        ≤ (L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹) *
          (M * ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (M * L2D_beta k.1.1 k.2.1.1) * ((Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ *
          ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by ring
      _ = _ := by rw [L2D_rpow_four _ hn]
  have hpart : ∀ s : Finset (L2D_Key 𝔪 Dd.T h),
      ∑ k ∈ s, ‖L2D_coef Dd υ h d k * ∑' c, w k c‖ ≤
        (M * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) * L2D_zeta F 4 * Fintype.card Dd.T := by
    intro s
    apply L2D_key_sum_le _ (fun f a => M * L2D_beta f.1 a.1)
      (fun n => ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-(4 : ℝ)))
      (fun f a => mul_nonneg hM0 (L2D_beta_nonneg _ _))
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hkey
    · intro sa sb
      calc ∑ f ∈ sa, ∑ a ∈ sb, M * L2D_beta f.1 a.1 = M * ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 := by
            rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ M * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) := by
            gcongr; exact L2D_key_beta_le h hh sa sb
    · intro sc; exact L2D_ext_sum_le_zeta 4 (by norm_num) sc
  exact summable_of_sum_le (fun k => norm_nonneg _) hpart

/-- The decomposition `B_m(Z) = Ret + Tail` on a row class. -/
lemma L2D_decomp (Dd : L2D_Data χ g) (r : RowClass 𝔪) (h : Ideal (𝓞 F))
    (hh : h * simplePart r.1.1 = r.1.1) {Z : ℝ} (hZ : 0 < Z) (R0 : ℝ) :
    χ.thetaSum g (rowElt g r) Z =
      L2D_RetT Dd r.2 h (simplePart r.1.1) Z R0 + L2D_TailT Dd r.2 h (simplePart r.1.1) Z R0 := by
  classical
  have hb0 : r.1.1 ≠ ⊥ := r.1.2.1
  have hd : simplePart r.1.1 ≠ ⊥ := L2D_simplePart_ne_bot _ hb0
  have hh0 : h ≠ ⊥ := (L2D_powerful_of_mul _ h hb0 hh).1
  have hR := L2D_keysum_summable Dd r.2 h (simplePart r.1.1) hh0 hd hZ
    (fun k c => if L2D_Q k c.1 ≤ R0 then L2D_term Dd r.2 h (simplePart r.1.1) Z k c else 0)
    (fun k c => by split_ifs <;> simp)
  have hT := L2D_keysum_summable Dd r.2 h (simplePart r.1.1) hh0 hd hZ
    (fun k c => if L2D_Q k c.1 ≤ R0 then 0 else L2D_term Dd r.2 h (simplePart r.1.1) Z k c)
    (fun k c => by split_ifs <;> simp)
  rw [Dd.hid r h hh Z hZ]
  unfold L2D_RetT L2D_TailT L2D_RetC L2D_TailC
  rw [← (Summable.of_norm hR).tsum_add (Summable.of_norm hT)]
  congr 1
  funext k
  rw [← mul_add]
  unfold L2D_coef
  congr 1
  rw [← (Summable.of_norm (L2D_ite_summable Dd r.2 h (simplePart r.1.1) hZ hd k _)).tsum_add
    (Summable.of_norm (L2D_ite_summable' Dd r.2 h (simplePart r.1.1) hZ hd k
      (fun c => L2D_Q k c.1 ≤ R0)))]
  congr 1
  funext c
  split_ifs <;> simp [L2D_term, L2D_x]

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 4: the large sieve in finite-sum form. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma L2D_tsum_subtype_ite {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (p : Ideal (𝓞 F) → Prop) (s : Finset (Ideal (𝓞 F))) (hs : ∀ x ∈ s, p x)
    (f : Ideal (𝓞 F) → E) :
    ∑' x : {x // p x}, (if x.1 ∈ s then f x.1 else 0) = ∑ x ∈ s, f x := by
  classical
  have h1 := tsum_subtype ({x | p x} : Set (Ideal (𝓞 F))) (fun x => if x ∈ s then f x else 0)
  change ∑' x : ({x | p x} : Set (Ideal (𝓞 F))), (if (x : Ideal (𝓞 F)) ∈ s then f x else 0) = _
  rw [h1, tsum_eq_sum (s := s)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hs x hx), if_pos hx]
  · intro x hx
    by_cases hp : x ∈ {x | p x}
    · rw [Set.indicator_of_mem hp, if_neg hx]
    · rw [Set.indicator_of_notMem hp]

lemma L2D_sum_le_tsum_subtype (p : Ideal (𝓞 F) → Prop) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ x ∈ s, p x) (f : Ideal (𝓞 F) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hfin : Set.Finite {x | p x}) :
    ∑ x ∈ s, f x ≤ ∑' x : {x // p x}, f x.1 := by
  classical
  have : Finite {x // p x} := hfin.to_subtype
  calc ∑ x ∈ s, f x = ∑ x ∈ s.subtype p, f x.1 := (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' x : {x // p x}, f x.1 :=
        Summable.sum_le_tsum _ (fun x _ => hf x.1) (Summable.of_finite)

/-- Lemma 6.4 in finite-sum form. -/
lemma L2D_LS_finset (n : ℕ) [IsCyclotomicExtension {n} ℚ F] (g : AllowedGen ι 𝔪)
    (hLS : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
        ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
            ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
          K * (C + D) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D → ∀ (cs ds : Finset (Ideal (𝓞 F))),
      (∀ c ∈ cs, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ C) →
      (∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ D) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2 ≤
          K * (C + D) * (C * D) ^ ε * ∑ c ∈ cs, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨K, hK⟩ := hLS ε hε
  refine ⟨K, fun C D hC hD cs ds hcs hds z => ?_⟩
  set z' : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ :=
    fun c => if c.1 ∈ cs then z c.1 else 0
  have h := hK C D hC hD z'
  have hcol : ∀ d : Ideal (𝓞 F), ∑' c : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, z' c * residueSymbol ι 𝔪 d (g.gen c.1) ^ 3 =
      ∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3 := by
    intro d
    rw [← L2D_tsum_subtype_ite _ cs hcs]
    congr 1; funext c
    simp only [z']
    split_ifs <;> simp
  have hmass : ∑' c : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, ‖z' c‖ ^ 2 = ∑ c ∈ cs, ‖z c‖ ^ 2 := by
    rw [← L2D_tsum_subtype_ite _ cs hcs]
    congr 1; funext c
    simp only [z']
    split_ifs <;> simp
  have hfin : Set.Finite {d : Ideal (𝓞 F) | IsExterior 𝔪 d ∧ Squarefree d ∧
      (Ideal.absNorm d : ℝ) ≤ D} :=
    (L2D_finite_le D).subset fun d hd => hd.2.2
  calc ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2
      ≤ ∑' d : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
          ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d.1 (g.gen c) ^ 3‖ ^ 2 :=
        L2D_sum_le_tsum_subtype _ ds hds
          (fun d => ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2)
          (fun _ => by positivity) hfin
    _ = ∑' d : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
          ‖∑' c, z' c * residueSymbol ι 𝔪 d.1 (g.gen c.1) ^ 3‖ ^ 2 := by
        congr 1; funext d; rw [hcol]
    _ ≤ K * (C + D) * (C * D) ^ ε * ∑' c, ‖z' c‖ ^ 2 := h
    _ = K * (C + D) * (C * D) ^ ε * ∑ c ∈ cs, ‖z c‖ ^ 2 := by rw [hmass]

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

/-- The squarefree exterior rows of norm `≤ 2D`. -/
noncomputable def L2D_Rows (𝔪 : Ideal (𝓞 F)) (D : ℝ) : Finset (Ideal (𝓞 F)) := L2D_cols 𝔪 (2 * D)

lemma L2D_exterior_of_dvd {d 𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (hd : d ∣ 𝔟) :
    IsExterior 𝔪 d := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h𝔟.1 (zero_dvd_iff.1 hd)
  · have hle : 𝔟 ≤ d := Ideal.le_of_dvd hd
    rw [eq_top_iff, ← h𝔟.2]
    exact sup_le_sup_right hle _

lemma L2D_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  have h1 := norm_nonneg a
  have h2 := norm_nonneg b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

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
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid MeasureTheory Real
open scoped FourierTransform

/-! L2D core, part 5: the retained part of one frozen key, by Fourier separation and the large
sieve. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

/-- The ideal-indexed column term. -/
noncomputable def L2D_termI (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (Z : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) (d c : Ideal (𝓞 F)) : ℂ :=
  Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c * residueSymbol ι 𝔪 d (g.gen c) ^ 3 /
    ((Real.sqrt (Ideal.absNorm c) : ℝ) : ℂ) *
    Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (L2D_x Z d k c)

lemma L2D_Q_ge_absNorm {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) (c : Ideal (𝓞 F)) :
    (Ideal.absNorm c : ℝ) ≤ L2D_Q k c := by
  unfold L2D_Q
  have h1 := L2D_one_le_absNorm k.2.1.2
  have h3 := one_le_pow₀ (n := 3) (L2D_one_le_absNorm (L2D_key_n_ne_bot k))
  calc (Ideal.absNorm c : ℝ) = 1 * Ideal.absNorm c * 1 := by ring
    _ ≤ _ := by gcongr

lemma L2D_RetC_eq_finsum (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (Z R0 : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) :
    L2D_RetC Dd υ h d Z R0 k =
      ∑ c ∈ L2D_cols 𝔪 R0, if L2D_Q k c ≤ R0 then L2D_termI Dd υ h Z k d c else 0 := by
  classical
  unfold L2D_RetC
  rw [← L2D_tsum_subtype_ite (fun c => IsExterior 𝔪 c ∧ Squarefree c) (L2D_cols 𝔪 R0)
    (fun c hc => (L2D_mem_cols.1 hc).2)]
  congr 1; funext c
  by_cases hQ : L2D_Q k c.1 ≤ R0
  · have hc : c.1 ∈ L2D_cols 𝔪 R0 :=
      L2D_mem_cols.2 ⟨(L2D_Q_ge_absNorm k c.1).trans hQ, c.2⟩
    rw [if_pos hQ, if_pos hc, if_pos hQ]; rfl
  · rw [if_neg hQ]; split_ifs <;> rfl

/-- The Fourier constants of the profiles, uniform over the keys. -/
lemma L2D_prof_fourier (Dd : L2D_Data χ g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ υ h f a n s,
      Integrable (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      Continuous (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      (∫ τ, ‖𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ‖) ≤ K ∧
      ∀ u : ℝ, Dd.Φ υ h f a n s (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u) := by
  obtain ⟨C, hC⟩ := Dd.hΦb 1 one_pos
  obtain ⟨K, hK0, hK⟩ := L2D_fourier_sep Dd.α (max C 0) Dd.hα (le_max_right _ _)
  refine ⟨K, hK0, fun υ h f a n s => ?_⟩
  apply hK _ (Dd.hΦ υ h f a n s)
  intro j hj t
  refine (hC υ h f a n s j hj t).trans ?_
  unfold L2D_maj
  gcongr
  exact le_max_left _ _

/-- The Fourier expansion of one column term. -/
lemma L2D_termI_fourier (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) {Z : ℝ}
    (hZ : 0 < Z) (k : L2D_Key 𝔪 Dd.T h) (d c : Ideal (𝓞 F)) (hd : d ≠ ⊥) (hc : c ≠ ⊥)
    (hinv : ∀ u : ℝ, Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u)) :
    L2D_termI Dd υ h Z k d c =
      ∫ τ, 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ *
        (Complex.exp (2 * π * Complex.I * τ *
            Real.log (Z * Ideal.absNorm k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
              (Ideal.absNorm k.1.1 : ℝ) ^ 2)) *
          Complex.exp (-(2 * (2 * π * Complex.I * τ * Real.log (Ideal.absNorm d)))) *
          (Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c / ((Real.sqrt (Ideal.absNorm c) : ℝ) : ℂ) *
            Complex.exp (2 * π * Complex.I * τ * Real.log (Ideal.absNorm c))) *
          residueSymbol ι 𝔪 d (g.gen c) ^ 3) := by
  unfold L2D_termI
  have hNa := L2D_absNorm_pos k.2.1.2
  have hNn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
  have hNf := L2D_absNorm_pos (L2D_key_f_ne_bot k)
  have hNd := L2D_absNorm_pos hd
  have hNc := L2D_absNorm_pos hc
  have hx : L2D_x Z d k c = Real.exp (Real.log (Z * Ideal.absNorm k.2.1.1 *
      (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 / (Ideal.absNorm k.1.1 : ℝ) ^ 2) +
        Real.log (Ideal.absNorm c) - 2 * Real.log (Ideal.absNorm d)) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hNc,
      show 2 * Real.log (Ideal.absNorm d : ℝ) = Real.log ((Ideal.absNorm d : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    unfold L2D_x; field_simp
  rw [hx, hinv, ← integral_const_mul]
  congr 1; funext τ
  rw [show (2 * π * Complex.I * τ * ((Real.log (Z * Ideal.absNorm k.2.1.1 *
      (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 / (Ideal.absNorm k.1.1 : ℝ) ^ 2) +
        Real.log (Ideal.absNorm c) - 2 * Real.log (Ideal.absNorm d) : ℝ) : ℂ)) =
      2 * π * Complex.I * τ * Real.log (Z * Ideal.absNorm k.2.1.1 *
        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 / (Ideal.absNorm k.1.1 : ℝ) ^ 2) +
      2 * π * Complex.I * τ * Real.log (Ideal.absNorm c) +
      -(2 * (2 * π * Complex.I * τ * Real.log (Ideal.absNorm d))) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_add]
  ring

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid MeasureTheory Real
open scoped FourierTransform

/-! L2D core, part 6: the `ℓ²` bound for the retained part of one frozen key. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

section
variable (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (Z R0 : ℝ) (k : L2D_Key 𝔪 Dd.T h)

/-- The column coefficient `z_τ(𝔠)` after Fourier separation. -/
noncomputable def L2D_zf (τ : ℝ) (c : Ideal (𝓞 F)) : ℂ :=
  if L2D_Q k c ≤ R0 then
    Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c / ((Real.sqrt (Ideal.absNorm c) : ℝ) : ℂ) *
      Complex.exp (2 * π * Complex.I * τ * Real.log (Ideal.absNorm c))
  else 0

/-- The bilinear form `∑_𝔠 z_τ(𝔠) χ_𝔡(c)^3`. -/
noncomputable def L2D_S (τ : ℝ) (d : Ideal (𝓞 F)) : ℂ :=
  ∑ c ∈ L2D_cols 𝔪 R0, L2D_zf Dd υ h R0 k τ c * residueSymbol ι 𝔪 d (g.gen c) ^ 3

/-- The phase depending on the frozen data. -/
noncomputable def L2D_e0 (τ : ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * τ *
    Real.log (Z * Ideal.absNorm k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
      (Ideal.absNorm k.1.1 : ℝ) ^ 2))

/-- The row phase. -/
noncomputable def L2D_ed (τ : ℝ) (d : Ideal (𝓞 F)) : ℂ :=
  Complex.exp (-(2 * (2 * π * Complex.I * τ * Real.log (Ideal.absNorm d))))

/-- The separated integrand. -/
noncomputable def L2D_G (τ : ℝ) (d : Ideal (𝓞 F)) : ℂ :=
  L2D_coef Dd υ h d k *
    (𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ *
      (L2D_e0 Dd h Z k τ * L2D_ed τ d)) * L2D_S Dd υ h R0 k τ d

end

lemma L2D_norm_exp_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma L2D_norm_e (τ y : ℝ) : ‖Complex.exp (2 * π * Complex.I * τ * y)‖ = 1 := by
  rw [show (2 * π * Complex.I * τ * y : ℂ) = ((2 * π * τ * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact L2D_norm_exp_I _

lemma L2D_norm_ed (τ : ℝ) (d : Ideal (𝓞 F)) : ‖L2D_ed τ d‖ = 1 := by
  unfold L2D_ed
  rw [show (-(2 * (2 * π * Complex.I * τ * Real.log (Ideal.absNorm d)))) =
    ((-(4 * π * τ * Real.log (Ideal.absNorm d)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact L2D_norm_exp_I _

lemma L2D_norm_e0 (Dd : L2D_Data χ g) (h : Ideal (𝓞 F)) (Z : ℝ) (k : L2D_Key 𝔪 Dd.T h) (τ : ℝ) :
    ‖L2D_e0 Dd h Z k τ‖ = 1 := L2D_norm_e _ _

lemma L2D_zf_norm_sq_le (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (R0 : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) (τ : ℝ) (c : Ideal (𝓞 F)) (hc : c ≠ ⊥) :
    ‖L2D_zf Dd υ h R0 k τ c‖ ^ 2 ≤ (Ideal.absNorm c : ℝ)⁻¹ := by
  unfold L2D_zf
  have hNc := L2D_absNorm_pos hc
  have hsq : 0 < Real.sqrt (Ideal.absNorm c) := Real.sqrt_pos.2 hNc
  split_ifs
  · rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hsq.le, L2D_norm_e, mul_one]
    have hl := Dd.hlam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c
    calc (‖Dd.lam υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c‖ / Real.sqrt (Ideal.absNorm c)) ^ 2
        ≤ (1 / Real.sqrt (Ideal.absNorm c)) ^ 2 := by gcongr
      _ = (Ideal.absNorm c : ℝ)⁻¹ := by
        rw [div_pow, Real.sq_sqrt hNc.le]; ring
  · simp

lemma L2D_zf_continuous (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (R0 : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) (c : Ideal (𝓞 F)) :
    Continuous fun τ => L2D_zf Dd υ h R0 k τ c := by
  unfold L2D_zf
  split_ifs
  · fun_prop
  · exact continuous_const

lemma L2D_S_continuous (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (R0 : ℝ)
    (k : L2D_Key 𝔪 Dd.T h) (d : Ideal (𝓞 F)) :
    Continuous fun τ => L2D_S Dd υ h R0 k τ d := by
  unfold L2D_S
  exact continuous_finset_sum _ fun c _ =>
    (L2D_zf_continuous Dd υ h R0 k c).mul continuous_const

/-- Claim A: `coef · RetC = ∫ G`. -/
lemma L2D_coefRet_eq_integral (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) {Z : ℝ}
    (hZ : 0 < Z) (R0 : ℝ) (k : L2D_Key 𝔪 Dd.T h)
    (hFi : Integrable (𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))))
    (hinv : ∀ u : ℝ, Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u))
    (d : Ideal (𝓞 F)) (hd : d ≠ ⊥) :
    L2D_coef Dd υ h d k * L2D_RetC Dd υ h d Z R0 k = ∫ τ, L2D_G Dd υ h Z R0 k τ d := by
  classical
  set Fh := 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))
  -- each column term as an integral
  have hcol : ∀ c ∈ L2D_cols 𝔪 R0,
      (if L2D_Q k c ≤ R0 then L2D_termI Dd υ h Z k d c else 0) =
        ∫ τ, Fh τ * ((L2D_e0 Dd h Z k τ * L2D_ed τ d) *
          (L2D_zf Dd υ h R0 k τ c * residueSymbol ι 𝔪 d (g.gen c) ^ 3)) := by
    intro c hc
    have hc0 : c ≠ ⊥ := (L2D_mem_cols.1 hc).2.1.1
    by_cases hQ : L2D_Q k c ≤ R0
    · rw [if_pos hQ, L2D_termI_fourier Dd υ h hZ k d c hd hc0 hinv]
      congr 1; funext τ
      simp only [L2D_zf, if_pos hQ, L2D_e0, L2D_ed]
      ring
    · rw [if_neg hQ]
      simp [L2D_zf, if_neg hQ]
  have hint : ∀ c ∈ L2D_cols 𝔪 R0, Integrable (fun τ => Fh τ * ((L2D_e0 Dd h Z k τ * L2D_ed τ d) *
      (L2D_zf Dd υ h R0 k τ c * residueSymbol ι 𝔪 d (g.gen c) ^ 3))) := by
    intro c hc
    have hc0 : c ≠ ⊥ := (L2D_mem_cols.1 hc).2.1.1
    refine hFi.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun τ => ?_)
    · apply Continuous.aestronglyMeasurable
      unfold L2D_e0 L2D_ed
      exact ((by fun_prop : Continuous fun τ : ℝ => _).mul
        ((L2D_zf_continuous Dd υ h R0 k c).mul continuous_const))
    · rw [norm_mul, norm_mul, L2D_norm_e0, L2D_norm_ed, one_mul, one_mul, norm_mul, norm_pow]
      have h1 : ‖L2D_zf Dd υ h R0 k τ c‖ ≤ 1 := by
        have := L2D_zf_norm_sq_le Dd υ h R0 k τ c hc0
        have hN := L2D_one_le_absNorm hc0
        have : ‖L2D_zf Dd υ h R0 k τ c‖ ^ 2 ≤ 1 ^ 2 := by
          rw [one_pow]; exact this.trans (inv_le_one_of_one_le₀ hN)
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one (by norm_num)).1 this
      have h2 : ‖residueSymbol ι 𝔪 d (g.gen c)‖ ^ 3 ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (L2D_norm_residueSymbol_le ι 𝔪 d _)
      calc ‖L2D_zf Dd υ h R0 k τ c‖ * ‖residueSymbol ι 𝔪 d (g.gen c)‖ ^ 3 ≤ 1 * 1 := by
            gcongr
        _ = 1 := by ring
  rw [L2D_RetC_eq_finsum, Finset.sum_congr rfl hcol, ← integral_finset_sum _ hint,
    ← integral_const_mul]
  congr 1; funext τ
  unfold L2D_G L2D_S
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  ring

/-- The vector of retained parts of one key over a finite row set. -/
noncomputable def L2D_Vk (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (Z R0 : ℝ)
    (ds : Finset (Ideal (𝓞 F))) (k : L2D_Key 𝔪 Dd.T h) : EuclideanSpace ℂ {d // d ∈ ds} :=
  WithLp.toLp 2 fun d => L2D_coef Dd υ h d.1 k * L2D_RetC Dd υ h d.1 Z R0 k

/-- The `ℓ²` bound for one key (Fourier separation + Lemma 6.4). -/
lemma L2D_Vk_norm_le (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) {Z R0 D : ℝ}
    (hZ : 0 < Z) (hR0 : 1 ≤ R0) (hD : 1 ≤ D) (KΨ K ε : ℝ) (hK : 0 ≤ K)
    (hLS : ∀ (cs ds : Finset (Ideal (𝓞 F))),
      (∀ c ∈ cs, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ R0) →
      (∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ 2 * D) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2 ≤
          K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε * ∑ c ∈ cs, ‖z c‖ ^ 2)
    (ds : Finset (Ideal (𝓞 F)))
    (hds : ∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ 2 * D)
    (k : L2D_Key 𝔪 Dd.T h)
    (hFi : Integrable (𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))))
    (hFc : Continuous (𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))))
    (hFK : (∫ τ, ‖𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ‖) ≤ KΨ)
    (hinv : ∀ u : ℝ, Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u)) :
    ‖L2D_Vk Dd υ h Z R0 ds k‖ ≤ L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ *
      (KΨ * Real.sqrt (K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε *
        ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹)) := by
  classical
  set Fh := 𝓕 (fun t => Dd.Φ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))
  set W2 := K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε * ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹
    with hW2
  set W := Real.sqrt W2
  set bn := L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹
  have hbn : 0 ≤ bn := mul_nonneg (L2D_beta_nonneg _ _) (by positivity)
  have hcs : ∀ c ∈ L2D_cols 𝔪 R0, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ R0 :=
    fun c hc => by
      obtain ⟨h1, h2, h3⟩ := L2D_mem_cols.1 hc
      exact ⟨h2, h3, h1⟩
  -- the bilinear-form bound for each τ
  have hSb : ∀ τ : ℝ, ∑ d ∈ ds, ‖L2D_S Dd υ h R0 k τ d‖ ^ 2 ≤ W2 := by
    intro τ
    refine (hLS _ ds hcs hds (L2D_zf Dd υ h R0 k τ)).trans ?_
    have hK0 : 0 ≤ K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε := by
      have : 0 ≤ (R0 * (2 * D)) ^ ε := Real.rpow_nonneg (by positivity) _
      have : 0 ≤ R0 + 2 * D := by linarith
      positivity
    rw [hW2]
    gcongr with c hc
    exact L2D_zf_norm_sq_le Dd υ h R0 k τ c (hcs c hc).1.1
  set Gv : ℝ → EuclideanSpace ℂ {d // d ∈ ds} := fun τ =>
    WithLp.toLp 2 fun d => L2D_G Dd υ h Z R0 k τ d.1
  have hGv_apply : ∀ τ (d : {d // d ∈ ds}), Gv τ d = L2D_G Dd υ h Z R0 k τ d.1 := fun _ _ => rfl
  -- pointwise bound
  have hGb : ∀ τ, ‖Gv τ‖ ≤ bn * W * ‖Fh τ‖ := by
    intro τ
    have hsq : ‖Gv τ‖ ^ 2 ≤ (bn * W * ‖Fh τ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hterm : ∀ d : {d // d ∈ ds}, ‖Gv τ d‖ ^ 2 ≤
          (bn * ‖Fh τ‖) ^ 2 * ‖L2D_S Dd υ h R0 k τ d.1‖ ^ 2 := by
        intro d
        rw [hGv_apply]
        unfold L2D_G
        simp only [norm_mul, L2D_norm_e0, L2D_norm_ed, mul_one]
        have hc := L2D_coef_norm_le Dd υ h d.1 k
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        calc ‖L2D_coef Dd υ h d.1 k‖ * ‖Fh τ‖ * ‖L2D_S Dd υ h R0 k τ d.1‖
            ≤ bn * ‖Fh τ‖ * ‖L2D_S Dd υ h R0 k τ d.1‖ := by gcongr
          _ = _ := by ring
      calc ∑ d, ‖Gv τ d‖ ^ 2 ≤ ∑ d : {d // d ∈ ds}, (bn * ‖Fh τ‖) ^ 2 *
            ‖L2D_S Dd υ h R0 k τ d.1‖ ^ 2 := Finset.sum_le_sum fun d _ => hterm d
        _ = (bn * ‖Fh τ‖) ^ 2 * ∑ d ∈ ds, ‖L2D_S Dd υ h R0 k τ d‖ ^ 2 := by
            rw [← Finset.mul_sum]
            congr 1
            exact Finset.sum_coe_sort ds (fun d => ‖L2D_S Dd υ h R0 k τ d‖ ^ 2)
        _ ≤ (bn * ‖Fh τ‖) ^ 2 * W2 := by gcongr; exact hSb τ
        _ = (bn * W * ‖Fh τ‖) ^ 2 := by
            have hW2 : 0 ≤ W2 := (Finset.sum_nonneg fun _ _ => by positivity).trans (hSb τ)
            rw [show (bn * W * ‖Fh τ‖) ^ 2 = (bn * ‖Fh τ‖) ^ 2 * W ^ 2 by ring,
              Real.sq_sqrt hW2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq
  -- continuity and integrability
  have hGc : Continuous Gv := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro d
    unfold L2D_G L2D_e0 L2D_ed
    exact (continuous_const.mul (hFc.mul (by fun_prop))).mul
      (L2D_S_continuous Dd υ h R0 k d.1)
  have hGi : Integrable Gv :=
    Integrable.mono' (hFi.norm.const_mul (bn * W)) hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGb)
  -- the vector is the integral
  have hV : L2D_Vk Dd υ h Z R0 ds k = ∫ τ, Gv τ := by
    ext d
    have h1 := (EuclideanSpace.proj (𝕜 := ℂ) d).integral_comp_comm hGi
    rw [show (∫ τ, Gv τ) d = EuclideanSpace.proj (𝕜 := ℂ) d (∫ τ, Gv τ) from rfl, ← h1]
    show L2D_coef Dd υ h d.1 k * L2D_RetC Dd υ h d.1 Z R0 k = _
    rw [L2D_coefRet_eq_integral Dd υ h hZ R0 k hFi hinv d.1 (hds d.1 d.2).1.1]
    rfl
  rw [hV]
  calc ‖∫ τ, Gv τ‖ ≤ ∫ τ, ‖Gv τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ, bn * W * ‖Fh τ‖ := integral_mono hGi.norm (hFi.norm.const_mul _) hGb
    _ = bn * W * ∫ τ, ‖Fh τ‖ := integral_const_mul _ _
    _ ≤ bn * W * KΨ := by gcongr
    _ = bn * (KΨ * W) := by ring

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid MeasureTheory Real
open scoped FourierTransform

/-! L2D core, part 7: the retained part summed over the frozen keys (Minkowski in `ℓ²`). -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

lemma L2D_Vk_eq_zero (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (Z R0 : ℝ)
    (ds : Finset (Ideal (𝓞 F))) (k : L2D_Key 𝔪 Dd.T h)
    (hk : ¬ (Ideal.absNorm k.2.2.1.1 : ℝ) ≤ R0) : L2D_Vk Dd υ h Z R0 ds k = 0 := by
  ext d
  show L2D_coef Dd υ h d.1 k * L2D_RetC Dd υ h d.1 Z R0 k = 0
  rw [L2D_RetC_eq_zero Dd υ h d.1 Z R0 k hk, mul_zero]

/-- The retained mass for fixed `υ, 𝔥`: `∑_{𝔡} |Ret_{𝔥,𝔡}|² ≤ (K_Ψ W #F(𝔥) E₀^{ω(𝔥)} H(R₀) |T|)²`. -/
lemma L2D_ret_mass_le (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    {Z R0 D : ℝ} (hZ : 0 < Z) (hR0 : 1 ≤ R0) (hD : 1 ≤ D) (KΨ K ε : ℝ) (hK : 0 ≤ K)
    (hKΨ : ∀ υ h f a n s,
      Integrable (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      Continuous (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      (∫ τ, ‖𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ‖) ≤ KΨ ∧
      ∀ u : ℝ, Dd.Φ υ h f a n s (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u))
    (hKΨ0 : 0 ≤ KΨ)
    (hLS : ∀ (cs ds : Finset (Ideal (𝓞 F))),
      (∀ c ∈ cs, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ R0) →
      (∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ 2 * D) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2 ≤
          K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε * ∑ c ∈ cs, ‖z c‖ ^ 2)
    (ds : Finset (Ideal (𝓞 F)))
    (hds : ∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ 2 * D) :
    ∑ d ∈ ds, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 ≤
      (KΨ * Real.sqrt (K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε *
          ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹) *
        ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) *
        (∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ))) * Fintype.card Dd.T) ^ 2 := by
  classical
  set X := KΨ * Real.sqrt (K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε *
          ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹) with hX
  have hX0 : 0 ≤ X := mul_nonneg hKΨ0 (Real.sqrt_nonneg _)
  have hkey : ∀ k : L2D_Key 𝔪 Dd.T h, ‖L2D_Vk Dd υ h Z R0 ds k‖ ≤
      (X * L2D_beta k.1.1 k.2.1.1) *
        (if (Ideal.absNorm k.2.2.1.1 : ℝ) ≤ R0 then (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ else 0) := by
    intro k
    split_ifs with hk
    · obtain ⟨h1, h2, h3, h4⟩ := hKΨ υ h k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
      have := L2D_Vk_norm_le Dd υ h hZ hR0 hD KΨ K ε hK hLS ds hds k h1 h2 h3 h4
      rw [hX]; linarith [this]
    · rw [L2D_Vk_eq_zero Dd υ h Z R0 ds k hk]; simp
  have hpart : ∀ s : Finset (L2D_Key 𝔪 Dd.T h),
      ∑ k ∈ s, ‖L2D_Vk Dd υ h Z R0 ds k‖ ≤
        (X * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) *
          (∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ))) * Fintype.card Dd.T := by
    intro s
    apply L2D_key_sum_le _ (fun f a => X * L2D_beta f.1 a.1)
      (fun n => if (Ideal.absNorm n.1 : ℝ) ≤ R0 then (Ideal.absNorm n.1 : ℝ)⁻¹ else 0)
      (fun f a => mul_nonneg hX0 (L2D_beta_nonneg _ _))
      (fun n => by split_ifs <;> positivity) hkey
    · intro sa sb
      calc ∑ f ∈ sa, ∑ a ∈ sb, X * L2D_beta f.1 a.1 = X * ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 := by
            rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ X * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) := by
            gcongr; exact L2D_key_beta_le h hh sa sb
    · intro sc; exact L2D_ext_harm_le R0 sc
  have hsum := summable_of_sum_le (fun k => norm_nonneg _) hpart
  have hvsum : Summable (L2D_Vk Dd υ h Z R0 ds) := Summable.of_norm hsum
  -- the vector of retained parts is the sum of the key vectors
  have hRet : (WithLp.toLp 2 fun d : {d // d ∈ ds} => L2D_RetT Dd υ h d.1 Z R0 :
      EuclideanSpace ℂ {d // d ∈ ds}) = ∑' k, L2D_Vk Dd υ h Z R0 ds k := by
    ext d
    have h1 := (EuclideanSpace.proj (𝕜 := ℂ) d).map_tsum hvsum
    rw [show (∑' k, L2D_Vk Dd υ h Z R0 ds k) d =
      EuclideanSpace.proj (𝕜 := ℂ) d (∑' k, L2D_Vk Dd υ h Z R0 ds k) from rfl, h1]
    rfl
  have hnorm : ‖(WithLp.toLp 2 fun d : {d // d ∈ ds} => L2D_RetT Dd υ h d.1 Z R0 :
      EuclideanSpace ℂ {d // d ∈ ds})‖ ≤
      (X * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) *
          (∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ))) * Fintype.card Dd.T := by
    rw [hRet]
    exact (norm_tsum_le_tsum_norm hsum).trans
      (Real.tsum_le_of_sum_le (fun k => norm_nonneg _) hpart)
  have hsq := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 fun d : {d // d ∈ ds} =>
    L2D_RetT Dd υ h d.1 Z R0 : EuclideanSpace ℂ {d // d ∈ ds})
  calc ∑ d ∈ ds, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2
      = ∑ d : {d // d ∈ ds}, ‖L2D_RetT Dd υ h d.1 Z R0‖ ^ 2 :=
        (Finset.sum_coe_sort ds (fun d => ‖L2D_RetT Dd υ h d Z R0‖ ^ 2)).symm
    _ = ‖(WithLp.toLp 2 fun d : {d // d ∈ ds} => L2D_RetT Dd υ h d.1 Z R0 :
          EuclideanSpace ℂ {d // d ∈ ds})‖ ^ 2 := by rw [hsq]
    _ ≤ ((X * ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h)) *
          (∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ))) * Fintype.card Dd.T) ^ 2 := by
        gcongr
    _ = _ := by ring

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open Real

/-! L2D: the real-variable estimates for the final exponent bookkeeping in (4.5). -/

/-- `(2P)^{δ₁} ≤ (2c)^{δ₁} Z^{E δ₁}` when `P ≤ c Z^E`. -/
lemma L2D_B2 {c E Z P δ1 : ℝ} (hc : 1 ≤ c) (hZ : 1 ≤ Z) (hP : 1 ≤ P) (hδ1 : 0 ≤ δ1)
    (hPc : P ≤ c * Z ^ E) : (2 * P) ^ δ1 ≤ (2 * c) ^ δ1 * Z ^ (E * δ1) := by
  have hZ0 : 0 < Z := by linarith
  calc (2 * P) ^ δ1 ≤ (2 * (c * Z ^ E)) ^ δ1 := by gcongr
    _ = (2 * c) ^ δ1 * Z ^ (E * δ1) := by
        rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hZ0.le]

/-- `1 + log X ≤ A Z^η` for `1 ≤ X ≤ c Z^p`. -/
lemma L2D_log_le {c p η Z X : ℝ} (hc : 1 ≤ c) (hp : 0 ≤ p) (hη : 0 < η) (hZ : 1 ≤ Z)
    (hX : 1 ≤ X) (hXc : X ≤ c * Z ^ p) :
    1 + Real.log X ≤ (1 + Real.log c + p / η) * Z ^ η := by
  have hZ0 : 0 < Z := by linarith
  have hZη : 1 ≤ Z ^ η := Real.one_le_rpow hZ hη.le
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have h1 : Real.log X ≤ Real.log c + p * Real.log Z := by
    have := Real.log_le_log (by linarith) hXc
    rwa [Real.log_mul (by linarith) (by positivity), Real.log_rpow hZ0] at this
  have h2 : Real.log Z ≤ Z ^ η / η := Real.log_le_rpow_div hZ0.le hη
  have h3 : p * Real.log Z ≤ p / η * Z ^ η := by
    calc p * Real.log Z ≤ p * (Z ^ η / η) := by gcongr
      _ = p / η * Z ^ η := by ring
  have hpη : 0 ≤ p / η := by positivity
  nlinarith

/-- The tail factor: `J^{-M} L ≤ max 1 (8 c²)` with `J = max(Z^δ, 1/L)`, `δ M ≥ 2E - 1`. -/
lemma L2D_B3 {c E Z P D δ M : ℝ} (hc : 1 ≤ c) (hE : 1 ≤ E) (hZ : 1 ≤ Z) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hPD : P * D ≤ c * Z ^ E) (hδ : 0 < δ) (hM : 0 ≤ M) (hδM : 2 * E - 1 ≤ δ * M) :
    (max (Z ^ δ) (8 * D ^ 2 * P / Z)⁻¹) ^ (-M) * (8 * D ^ 2 * P / Z) ≤ max 1 (8 * c ^ 2) := by
  have hZ0 : 0 < Z := by linarith
  set L := 8 * D ^ 2 * P / Z with hL
  have hL0 : 0 < L := by positivity
  have hJ0 : 0 < max (Z ^ δ) L⁻¹ := lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 δ) (le_max_left _ _)
  by_cases hL1 : L ≤ 1
  · have hJ1 : 1 ≤ max (Z ^ δ) L⁻¹ := le_trans (one_le_inv₀ hL0 |>.2 hL1) (le_max_right _ _)
    have : (max (Z ^ δ) L⁻¹) ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hJ1 (by linarith)
    calc (max (Z ^ δ) L⁻¹) ^ (-M) * L ≤ 1 * 1 := by
          apply mul_le_mul this hL1 hL0.le zero_le_one
      _ ≤ max 1 (8 * c ^ 2) := by rw [one_mul]; exact le_max_left _ _
  · push Not at hL1
    have hJ : Z ^ δ ≤ max (Z ^ δ) L⁻¹ := le_max_left _ _
    have h1 : (max (Z ^ δ) L⁻¹) ^ (-M) ≤ (Z ^ δ) ^ (-M) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZ0 δ) hJ (by linarith)
    have h2 : (Z ^ δ) ^ (-M) ≤ Z ^ (-(2 * E - 1)) := by
      rw [← Real.rpow_mul hZ0.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
    have h3 : L ≤ 8 * c ^ 2 * Z ^ (2 * E - 1) := by
      rw [hL, div_le_iff₀ hZ0]
      have hPD2 : D ^ 2 * P ≤ (P * D) ^ 2 := by nlinarith
      have hc2 : (P * D) ^ 2 ≤ (c * Z ^ E) ^ 2 := by
        have : 0 ≤ P * D := by positivity
        gcongr
      have hZE : (c * Z ^ E) ^ 2 = c ^ 2 * (Z ^ (2 * E - 1) * Z) := by
        rw [← Real.rpow_add_one hZ0.ne', show 2 * E - 1 + 1 = E * 2 by ring,
          Real.rpow_mul hZ0.le, mul_pow]
        norm_cast
      nlinarith
    have hZp : 0 < Z ^ (2 * E - 1) := Real.rpow_pos_of_pos hZ0 _
    calc (max (Z ^ δ) L⁻¹) ^ (-M) * L ≤ Z ^ (-(2 * E - 1)) * (8 * c ^ 2 * Z ^ (2 * E - 1)) := by
          apply mul_le_mul (h1.trans h2) h3 hL0.le (Real.rpow_nonneg hZ0.le _)
      _ = 8 * c ^ 2 := by
          rw [Real.rpow_neg hZ0.le]; field_simp
      _ ≤ max 1 (8 * c ^ 2) := le_max_right _ _

/-- The retained variable factor:
`(R₀ + 2D)(2D R₀)^{ε₂}(1 + log R₀)^3 (2P)^{δ₁} ≤ Cv Z^ε (D + D² P/Z)`. -/
lemma L2D_B1 {c E Z P D ε : ℝ} (hc : 1 ≤ c) (hE : 1 ≤ E) (hZ : 1 ≤ Z) (hP : 1 ≤ P)
    (hD : 1 ≤ D) (hPD : P * D ≤ c * Z ^ E) (hε : 0 < ε)
    (hR0 : 1 ≤ Z ^ (ε / 4) * (8 * D ^ 2 * P / Z)) :
    (Z ^ (ε / 4) * (8 * D ^ 2 * P / Z) + 2 * D) *
        (Z ^ (ε / 4) * (8 * D ^ 2 * P / Z) * (2 * D)) ^ (ε / (4 * (ε / 4 + 3 * E))) *
        (1 + Real.log (Z ^ (ε / 4) * (8 * D ^ 2 * P / Z))) ^ 3 * (2 * P) ^ (ε / (4 * E)) ≤
      (8 * (16 * c ^ 3) ^ (ε / (4 * (ε / 4 + 3 * E))) *
          (1 + Real.log (8 * c ^ 2) + (ε / 4 + 2 * E) / (ε / 12)) ^ 3 *
          (2 * c) ^ (ε / (4 * E))) *
        Z ^ ε * (D + D ^ 2 * P / Z) := by
  have hZ0 : 0 < Z := by linarith
  have hE0 : 0 < E := by linarith
  set δ := ε / 4 with hδ
  set ε2 := ε / (4 * (δ + 3 * E)) with hε2
  set δ1 := ε / (4 * E) with hδ1
  set R0 := Z ^ δ * (8 * D ^ 2 * P / Z) with hR0def
  have hZδ : 1 ≤ Z ^ δ := Real.one_le_rpow hZ (by positivity)
  have hε20 : 0 ≤ ε2 := by positivity
  -- (R0 + 2D) ≤ 8 Z^δ (D + D² P / Z)
  have hA : R0 + 2 * D ≤ 8 * Z ^ δ * (D + D ^ 2 * P / Z) := by
    rw [hR0def]
    have h1 : 2 * D ≤ 8 * Z ^ δ * D := by nlinarith
    have e : Z ^ δ * (8 * D ^ 2 * P / Z) = 8 * Z ^ δ * (D ^ 2 * P / Z) := by ring
    rw [e, mul_add]
    linarith
  -- (2D R0)^{ε2} ≤ (16 c³)^{ε2} Z^{ε2(δ + 3E)}
  have hB : (R0 * (2 * D)) ^ ε2 ≤ (16 * c ^ 3) ^ ε2 * Z ^ (ε2 * (δ + 3 * E)) := by
    have h1 : R0 * (2 * D) ≤ 16 * c ^ 3 * Z ^ (δ + 3 * E) := by
      rw [hR0def, Real.rpow_add hZ0]
      have hD3 : D ^ 3 * P ≤ (P * D) ^ 3 := by
        have : 1 ≤ P ^ 2 := one_le_pow₀ hP
        have h' : D ^ 3 * P * 1 ≤ D ^ 3 * P * P ^ 2 := by gcongr
        nlinarith
      have hc3 : (P * D) ^ 3 ≤ (c * Z ^ E) ^ 3 := by
        have : 0 ≤ P * D := by positivity
        gcongr
      have hZE : (c * Z ^ E) ^ 3 = c ^ 3 * Z ^ (3 * E) := by
        rw [mul_pow, ← Real.rpow_natCast (Z ^ E) 3, ← Real.rpow_mul hZ0.le,
          show E * ((3 : ℕ) : ℝ) = 3 * E by push_cast; ring]
      have hdiv : Z ^ δ * (8 * D ^ 2 * P / Z) * (2 * D) ≤ Z ^ δ * (16 * (D ^ 3 * P)) := by
        have : 8 * D ^ 2 * P / Z * (2 * D) ≤ 16 * (D ^ 3 * P) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hZ0]
          have : 0 ≤ D ^ 3 * P := by positivity
          nlinarith
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      calc Z ^ δ * (8 * D ^ 2 * P / Z) * (2 * D) ≤ Z ^ δ * (16 * (D ^ 3 * P)) := hdiv
        _ ≤ Z ^ δ * (16 * (c ^ 3 * Z ^ (3 * E))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hD3.trans (hc3.trans hZE.le)]
        _ = 16 * c ^ 3 * (Z ^ δ * Z ^ (3 * E)) := by ring
    have h0 : 0 ≤ R0 * (2 * D) := by positivity
    calc (R0 * (2 * D)) ^ ε2 ≤ (16 * c ^ 3 * Z ^ (δ + 3 * E)) ^ ε2 := by gcongr
      _ = (16 * c ^ 3) ^ ε2 * Z ^ (ε2 * (δ + 3 * E)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hZ0.le, mul_comm ε2]
  -- log factor
  have hC : (1 + Real.log R0) ^ 3 ≤ (1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12)) ^ 3 *
      Z ^ (3 * (ε / 12)) := by
    have hR0c : R0 ≤ 8 * c ^ 2 * Z ^ (δ + 2 * E) := by
      rw [hR0def, Real.rpow_add hZ0]
      have hD2 : D ^ 2 * P ≤ (P * D) ^ 2 := by nlinarith
      have hc2 : (P * D) ^ 2 ≤ (c * Z ^ E) ^ 2 := by
        have : 0 ≤ P * D := by positivity
        gcongr
      have hZE : (c * Z ^ E) ^ 2 = c ^ 2 * Z ^ (2 * E) := by
        rw [mul_pow, ← Real.rpow_natCast (Z ^ E) 2, ← Real.rpow_mul hZ0.le,
          show E * ((2 : ℕ) : ℝ) = 2 * E by push_cast; ring]
      have : 8 * D ^ 2 * P / Z ≤ 8 * (D ^ 2 * P) := by
        rw [div_le_iff₀ hZ0]; nlinarith
      calc Z ^ δ * (8 * D ^ 2 * P / Z) ≤ Z ^ δ * (8 * (c ^ 2 * Z ^ (2 * E))) := by
            gcongr; linarith [hD2.trans (hc2.trans hZE.le)]
        _ = 8 * c ^ 2 * (Z ^ δ * Z ^ (2 * E)) := by ring
    have hc8 : 1 ≤ 8 * c ^ 2 := by nlinarith
    have hlog := L2D_log_le hc8 (by positivity : 0 ≤ δ + 2 * E) (by positivity : (0 : ℝ) < ε / 12)
      hZ hR0 hR0c
    have hl0 : 0 ≤ 1 + Real.log R0 := by linarith [Real.log_nonneg hR0]
    calc (1 + Real.log R0) ^ 3 ≤ ((1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12)) *
          Z ^ (ε / 12)) ^ 3 := by gcongr
      _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast (Z ^ (ε / 12)) 3, ← Real.rpow_mul hZ0.le,
            show ε / 12 * ((3 : ℕ) : ℝ) = 3 * (ε / 12) by push_cast; ring]
  -- the P factor
  have hDd : (2 * P) ^ δ1 ≤ (2 * c) ^ δ1 * Z ^ (E * δ1) := by
    have hPc : P ≤ c * Z ^ E := by nlinarith
    exact L2D_B2 hc hZ hP (by positivity) hPc
  -- combine the exponents
  have hexp : δ + ε2 * (δ + 3 * E) + 3 * (ε / 12) + E * δ1 = ε := by
    rw [hε2, hδ1, hδ]; field_simp; ring
  have hZs : Z ^ δ * Z ^ (ε2 * (δ + 3 * E)) * Z ^ (3 * (ε / 12)) * Z ^ (E * δ1) = Z ^ ε := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0, hexp]
  have hX : 0 ≤ D + D ^ 2 * P / Z := by positivity
  have hp1 : 0 ≤ (R0 * (2 * D)) ^ ε2 := Real.rpow_nonneg (by positivity) _
  have hp2 : 0 ≤ (1 + Real.log R0) ^ 3 := by
    have := Real.log_nonneg hR0; positivity
  have hp3 : 0 ≤ (2 * P) ^ δ1 := Real.rpow_nonneg (by positivity) _
  have hL0 : 0 ≤ 1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12) := by
    have : 0 ≤ Real.log (8 * c ^ 2) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ (δ + 2 * E) / (ε / 12) := by positivity
    linarith
  have hq1 : 0 ≤ 8 * Z ^ δ * (D + D ^ 2 * P / Z) := by positivity
  have hq2 : 0 ≤ (16 * c ^ 3) ^ ε2 * Z ^ (ε2 * (δ + 3 * E)) := by positivity
  have hq3 : 0 ≤ (1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12)) ^ 3 * Z ^ (3 * (ε / 12)) :=
    mul_nonneg (pow_nonneg hL0 3) (by positivity)
  have hR2 : 0 ≤ R0 + 2 * D := by positivity
  calc (R0 + 2 * D) * (R0 * (2 * D)) ^ ε2 * (1 + Real.log R0) ^ 3 * (2 * P) ^ δ1
      ≤ (8 * Z ^ δ * (D + D ^ 2 * P / Z)) * ((16 * c ^ 3) ^ ε2 * Z ^ (ε2 * (δ + 3 * E))) *
        ((1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12)) ^ 3 * Z ^ (3 * (ε / 12))) *
        ((2 * c) ^ δ1 * Z ^ (E * δ1)) := by
        apply mul_le_mul _ hDd hp3 (mul_nonneg (mul_nonneg hq1 hq2) hq3)
        apply mul_le_mul _ hC hp2 (mul_nonneg hq1 hq2)
        exact mul_le_mul hA hB hp1 hq1
    _ = (8 * (16 * c ^ 3) ^ ε2 * (1 + Real.log (8 * c ^ 2) + (δ + 2 * E) / (ε / 12)) ^ 3 *
          (2 * c) ^ δ1) * (Z ^ δ * Z ^ (ε2 * (δ + 3 * E)) * Z ^ (3 * (ε / 12)) * Z ^ (E * δ1)) *
          (D + D ^ 2 * P / Z) := by ring
    _ = _ := by rw [hZs]

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid MeasureTheory Real
open scoped FourierTransform

/-! L2D core, part 9: the per-`𝔥` retained and per-`(𝔥, 𝔡)` tail bounds with the final constants. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

lemma L2D_RetT_eq_zero (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (Z R0 : ℝ)
    (hR0 : R0 < 1) : L2D_RetT Dd υ h d Z R0 = 0 := by
  unfold L2D_RetT
  have : ∀ k : L2D_Key 𝔪 Dd.T h, L2D_RetC Dd υ h d Z R0 k = 0 := by
    intro k
    unfold L2D_RetC
    have hz : (fun c : L2D_Col 𝔪 => if L2D_Q k c.1 ≤ R0 then L2D_term Dd υ h d Z k c else 0) =
        fun _ => 0 := by
      funext c
      rw [if_neg]
      have := L2D_Q_ge_one k c
      linarith
    rw [hz, tsum_zero]
  simp [this]

/-- `(#F(𝔥) E₀^{ω(𝔥)})² ≤ C_ω N(𝔥)^{δ₁}`. -/
lemma L2D_FE_sq_le {Cω δ1 : ℝ}
    (hCω : ∀ h : Ideal (𝓞 F), h ≠ ⊥ → ((2 * L2D_E0) ^ 2) ^ L2D_omega h ≤
      Cω * (Ideal.absNorm h : ℝ) ^ δ1)
    (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) ^ 2 ≤ Cω * (Ideal.absNorm h : ℝ) ^ δ1 := by
  have hE := L2D_E0_pos
  have h1 : ((L2D_Fset h).card : ℝ) ≤ 2 ^ L2D_omega h := by
    exact_mod_cast L2D_card_Fset_le h hh
  calc ((L2D_Fset h).card * L2D_E0 ^ L2D_omega h) ^ 2 ≤ (2 ^ L2D_omega h * L2D_E0 ^ L2D_omega h) ^ 2 := by
        gcongr
    _ = ((2 * L2D_E0) ^ 2) ^ L2D_omega h := by
        rw [← mul_pow, ← pow_mul, ← pow_mul, mul_comm (L2D_omega h)]
    _ ≤ _ := hCω h hh

lemma L2D_cols_harm_le (R0 : ℝ) :
    ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹ ≤ ∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ)) := by
  classical
  unfold L2D_cols
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro I _
  split_ifs
  · rw [one_div]
  · positivity

/-- The retained bound for fixed `υ, 𝔥` in final form. -/
lemma L2D_RB (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    {Z R0 D P : ℝ} (hZ : 0 < Z) (hR0 : 1 ≤ R0) (hD : 1 ≤ D) (hhP : (Ideal.absNorm h : ℝ) ≤ 2 * P)
    (KΨ K ε2 Bh Cω δ1 : ℝ) (hK : 0 ≤ K) (hKΨ0 : 0 ≤ KΨ) (hBh0 : 0 ≤ Bh) (hδ1 : 0 ≤ δ1)
    (hKΨ : ∀ υ h f a n s,
      Integrable (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      Continuous (𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t))) ∧
      (∫ τ, ‖𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ‖) ≤ KΨ ∧
      ∀ u : ℝ, Dd.Φ υ h f a n s (Real.exp u) =
        ∫ τ, 𝓕 (fun t => Dd.Φ υ h f a n s (Real.exp t)) τ *
          Complex.exp (2 * π * Complex.I * τ * u))
    (hLS : ∀ (cs ds : Finset (Ideal (𝓞 F))),
      (∀ c ∈ cs, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ R0) →
      (∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ 2 * D) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2 ≤
          K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε2 * ∑ c ∈ cs, ‖z c‖ ^ 2)
    (hBh : ∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ)) ≤ Bh * (1 + Real.log R0))
    (hCω : ∀ h : Ideal (𝓞 F), h ≠ ⊥ → ((2 * L2D_E0) ^ 2) ^ L2D_omega h ≤
      Cω * (Ideal.absNorm h : ℝ) ^ δ1) :
    ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 ≤
      KΨ ^ 2 * K * Bh ^ 3 * (Fintype.card Dd.T : ℝ) ^ 2 * Cω *
        ((R0 + 2 * D) * (R0 * (2 * D)) ^ ε2 * (1 + Real.log R0) ^ 3 * (2 * P) ^ δ1) := by
  have hRows : ∀ d ∈ L2D_Rows 𝔪 D, IsExterior 𝔪 d ∧ Squarefree d ∧
      (Ideal.absNorm d : ℝ) ≤ 2 * D := by
    intro d hd
    obtain ⟨h1, h2, h3⟩ := L2D_mem_cols.1 hd
    exact ⟨h2, h3, h1⟩
  have hm := L2D_ret_mass_le Dd υ h hh hZ hR0 hD KΨ K ε2 hK hKΨ hKΨ0 hLS (L2D_Rows 𝔪 D) hRows
  set H1 := ∑ c ∈ L2D_cols 𝔪 R0, (Ideal.absNorm c : ℝ)⁻¹
  set H2 := ∑ I ∈ L2D_le F R0, (1 / (Ideal.absNorm I : ℝ))
  set FE := (L2D_Fset h).card * L2D_E0 ^ L2D_omega h
  set Tc := (Fintype.card Dd.T : ℝ)
  set X := K * (R0 + 2 * D) * (R0 * (2 * D)) ^ ε2
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (R0 * (2 * D)) ^ ε2 := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ R0 + 2 * D := by linarith
    positivity
  have hH1 : 0 ≤ H1 := Finset.sum_nonneg fun _ _ => by positivity
  have hH12 : H1 ≤ H2 := L2D_cols_harm_le R0
  have hH2 : H2 ≤ Bh * (1 + Real.log R0) := hBh
  have hlog : 0 ≤ 1 + Real.log R0 := by linarith [Real.log_nonneg hR0]
  have hFE : FE ^ 2 ≤ Cω * (2 * P) ^ δ1 := by
    refine (L2D_FE_sq_le hCω h hh).trans ?_
    have hCω0 : 0 ≤ Cω := by
      have := hCω h hh
      have h0 : 0 ≤ ((2 * L2D_E0) ^ 2) ^ L2D_omega h := by positivity
      by_contra hneg; push Not at hneg
      have : Cω * (Ideal.absNorm h : ℝ) ^ δ1 < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos (L2D_absNorm_pos hh) _)
      linarith
    gcongr
  have hT0 : 0 ≤ Tc := by positivity
  calc ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2
      ≤ (KΨ * Real.sqrt (X * H1) * FE * H2 * Tc) ^ 2 := hm
    _ = KΨ ^ 2 * (X * H1) * FE ^ 2 * H2 ^ 2 * Tc ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hX0 hH1)]
    _ ≤ KΨ ^ 2 * (X * (Bh * (1 + Real.log R0))) * (Cω * (2 * P) ^ δ1) *
          (Bh * (1 + Real.log R0)) ^ 2 * Tc ^ 2 := by
        have hH20 : 0 ≤ H2 := hH1.trans hH12
        have hB0 : 0 ≤ Bh * (1 + Real.log R0) := mul_nonneg hBh0 hlog
        have hH1b : H1 ≤ Bh * (1 + Real.log R0) := hH12.trans hH2
        have hCP : 0 ≤ Cω * (2 * P) ^ δ1 := (sq_nonneg FE).trans hFE
        have s1 : KΨ ^ 2 * (X * H1) ≤ KΨ ^ 2 * (X * (Bh * (1 + Real.log R0))) := by
          gcongr
        have s2 : KΨ ^ 2 * (X * H1) * FE ^ 2 ≤
            KΨ ^ 2 * (X * (Bh * (1 + Real.log R0))) * (Cω * (2 * P) ^ δ1) :=
          mul_le_mul s1 hFE (sq_nonneg _) (by positivity)
        have s3 : KΨ ^ 2 * (X * H1) * FE ^ 2 * H2 ^ 2 ≤
            KΨ ^ 2 * (X * (Bh * (1 + Real.log R0))) * (Cω * (2 * P) ^ δ1) *
              (Bh * (1 + Real.log R0)) ^ 2 :=
          mul_le_mul s2 (pow_le_pow_left₀ hH20 hH2 2) (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right s3 (sq_nonneg _)
    _ = _ := by ring

/-- The tail bound for fixed `υ, 𝔥, 𝔡` in final form. -/
lemma L2D_TB (Dd : L2D_Data χ g) (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hd : d ≠ ⊥)
    {Z D P δ M CN c Cω δ1 : ℝ} (hZ : 2 ≤ Z) (hD : 1 ≤ D) (hP : 1 ≤ P) (hc : 1 ≤ c)
    (hPD : P * D ≤ c * Z ^ ((1033 : ℝ) / 1000)) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hδM : 2 * ((1033 : ℝ) / 1000) - 1 ≤ δ * M)
    (hhP : (Ideal.absNorm h : ℝ) ≤ 2 * P) (hdD : (Ideal.absNorm d : ℝ) ≤ 2 * D)
    (hCN : ∀ υ h f a n s, ∀ x : ℝ, 0 < x → ‖Dd.Φ υ h f a n s x‖ ≤ CN * x ^ (-(M + 1)))
    (hCN0 : 0 ≤ CN) (hδ1 : 0 ≤ δ1)
    (hCω : ∀ h : Ideal (𝓞 F), h ≠ ⊥ → ((2 * L2D_E0) ^ 2) ^ L2D_omega h ≤
      Cω * (Ideal.absNorm h : ℝ) ^ δ1) :
    ‖L2D_TailT Dd υ h d Z (Z ^ δ * (8 * D ^ 2 * P / Z))‖ ^ 2 ≤
      (CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T) ^ 2 *
        (Cω * (2 * P) ^ δ1) := by
  have hZ0 : 0 < Z := by linarith
  have hL : 0 < 8 * D ^ 2 * P / Z := by positivity
  have htL : (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h / Z ≤ 8 * D ^ 2 * P / Z := by
    apply div_le_div_of_nonneg_right _ hZ0.le
    have h1 : (Ideal.absNorm d : ℝ) ^ 2 ≤ (2 * D) ^ 2 := by
      have := L2D_absNorm_pos hd; gcongr
    calc (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm h ≤ (2 * D) ^ 2 * (2 * P) := by
          have := L2D_absNorm_pos hh
          gcongr
      _ = 8 * D ^ 2 * P := by ring
  obtain ⟨_, hT⟩ := L2D_TailT_le Dd (N := M + 1) (by linarith) hCN hCN0 υ h d hh hd (δ := δ) hZ0 hL htL
  have hB3 := L2D_B3 (E := (1033 : ℝ) / 1000) hc (by norm_num) (by linarith) hP hD hPD hδ hM hδM
  have hneg : -(M + 1 - 1) = -M := by ring
  rw [hneg] at hT
  set FE := (L2D_Fset h).card * L2D_E0 ^ L2D_omega h
  have hFE0 : 0 ≤ FE := by have := L2D_E0_pos; positivity
  have hz3 : 0 ≤ L2D_zeta F (3 / 2) := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz4 : 0 ≤ L2D_zeta F 4 := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hJ0 : 0 ≤ (max (Z ^ δ) (8 * D ^ 2 * P / Z)⁻¹) ^ (-M) := by
    apply Real.rpow_nonneg
    exact le_trans (Real.rpow_pos_of_pos hZ0 δ).le (le_max_left _ _)
  have hTT : ‖L2D_TailT Dd υ h d Z (Z ^ δ * (8 * D ^ 2 * P / Z))‖ ≤
      (CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T) * FE := by
    refine hT.trans ?_
    calc CN * (max (Z ^ δ) (8 * D ^ 2 * P / Z)⁻¹) ^ (-M) * (8 * D ^ 2 * P / Z) *
          L2D_zeta F (3 / 2) * FE * L2D_zeta F 4 * Fintype.card Dd.T
        = CN * ((max (Z ^ δ) (8 * D ^ 2 * P / Z)⁻¹) ^ (-M) * (8 * D ^ 2 * P / Z)) *
          L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T * FE := by ring
      _ ≤ CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T * FE := by
          gcongr
  have hFE : FE ^ 2 ≤ Cω * (2 * P) ^ δ1 := by
    refine (L2D_FE_sq_le hCω h hh).trans ?_
    have hCω0 : 0 ≤ Cω := by
      have := hCω h hh
      have h0 : 0 ≤ ((2 * L2D_E0) ^ 2) ^ L2D_omega h := by positivity
      by_contra hneg; push Not at hneg
      have : Cω * (Ideal.absNorm h : ℝ) ^ δ1 < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos (L2D_absNorm_pos hh) _)
      linarith
    gcongr
  have hc0 : 0 ≤ CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T := by
    have : 0 ≤ max 1 (8 * c ^ 2) := le_trans zero_le_one (le_max_left _ _)
    positivity
  calc ‖L2D_TailT Dd υ h d Z (Z ^ δ * (8 * D ^ 2 * P / Z))‖ ^ 2
      ≤ ((CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T) * FE) ^ 2 := by
        gcongr
    _ = (CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) * L2D_zeta F 4 * Fintype.card Dd.T) ^ 2 * FE ^ 2 := by
        ring
    _ ≤ _ := by gcongr

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid MeasureTheory Real
open scoped FourierTransform

/-! L2D: the per-powerful-part second moment from Lemma 6.3 + Lemma 6.4. -/

set_option maxHeartbeats 4000000 in
theorem L2D_cutH_of_cuts (n : ℕ) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h63 : L2D_Cut63 n F ι) (h64 : L2D_Cut64 n F ι) : L2D_CutH n F ι := by
  classical
  obtain ⟨N1, hN1⟩ := L2D_data_of_cut n F ι h63
  obtain ⟨N2, hN2⟩ := h64
  refine ⟨max N1 N2, fun 𝔪 h𝔪 hsp χ g c₂ ε hε => ?_⟩
  have hsp1 : SmallPrimesDvd N1 𝔪 := fun P hP h0 hN => hsp P hP h0 (hN.trans (le_max_left _ _))
  have hsp2 : SmallPrimesDvd N2 𝔪 := fun P hP h0 hN => hsp P hP h0 (hN.trans (le_max_right _ _))
  obtain ⟨Dd⟩ := hN1 𝔪 h𝔪 hsp1 χ g
  have hLScut := hN2 𝔪 h𝔪 hsp2 g
  -- the exponents
  have hE1 : (1 : ℝ) ≤ (1033 : ℝ) / 1000 := by norm_num
  have hδ : 0 < ε / 4 := by positivity
  have hε2 : 0 < ε / (4 * (ε / 4 + 3 * ((1033 : ℝ) / 1000))) := by positivity
  have hδ1 : 0 < ε / (4 * ((1033 : ℝ) / 1000)) := by positivity
  have hM : 0 ≤ (2 * ((1033 : ℝ) / 1000) - 1) / (ε / 4) := by positivity
  have hδM : 2 * ((1033 : ℝ) / 1000) - 1 ≤ ε / 4 * ((2 * ((1033 : ℝ) / 1000) - 1) / (ε / 4)) := by
    rw [mul_div_cancel₀ _ hδ.ne']
  -- the constants
  obtain ⟨KΨ, hKΨ0, hKΨ⟩ := L2D_prof_fourier Dd
  obtain ⟨CN, hCN0, hCN⟩ := L2D_prof Dd ((2 * ((1033 : ℝ) / 1000) - 1) / (ε / 4) + 1)
    (by positivity)
  obtain ⟨K0, hK0⟩ := L2D_LS_finset n g hLScut _ hε2
  have hLSK : ∀ C D : ℝ, 1 ≤ C → 1 ≤ D → ∀ (cs ds : Finset (Ideal (𝓞 F))),
      (∀ c ∈ cs, IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ C) →
      (∀ d ∈ ds, IsExterior 𝔪 d ∧ Squarefree d ∧ (Ideal.absNorm d : ℝ) ≤ D) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        ∑ d ∈ ds, ‖∑ c ∈ cs, z c * residueSymbol ι 𝔪 d (g.gen c) ^ 3‖ ^ 2 ≤
          max K0 0 * (C + D) * (C * D) ^ (ε / (4 * (ε / 4 + 3 * ((1033 : ℝ) / 1000)))) *
            ∑ c ∈ cs, ‖z c‖ ^ 2 := by
    intro C D hC hD cs ds hcs hds z
    refine (hK0 C D hC hD cs ds hcs hds z).trans ?_
    have hX : 0 ≤ (C + D) * (C * D) ^ (ε / (4 * (ε / 4 + 3 * ((1033 : ℝ) / 1000)))) *
        ∑ c ∈ cs, ‖z c‖ ^ 2 := by
      have : 0 ≤ (C * D) ^ (ε / (4 * (ε / 4 + 3 * ((1033 : ℝ) / 1000)))) :=
        Real.rpow_nonneg (by positivity) _
      have : 0 ≤ ∑ c ∈ cs, ‖z c‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
      have : 0 ≤ C + D := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right (le_max_left K0 0) hX
    linarith [this]
  obtain ⟨Bh, hBh0, hBh⟩ := L2D_harmonic (F := F)
  obtain ⟨A, hA0, hA⟩ := L2D_count (F := F)
  have hE01 : 1 ≤ (2 * L2D_E0) ^ 2 := by
    have := L2D_E0_ge_one
    nlinarith
  obtain ⟨Cω, hCω0, hCω⟩ := L2D_omega_bound (F := F) ((2 * L2D_E0) ^ 2) hE01 _ hδ1
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max c₂ 1 := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ le_max_right _ _
  obtain ⟨CR, hCRdef⟩ : ∃ x : ℝ, x = KΨ ^ 2 * max K0 0 * Bh ^ 3 *
      (Fintype.card Dd.T : ℝ) ^ 2 * Cω := ⟨_, rfl⟩
  obtain ⟨Cv, hCvdef⟩ : ∃ x : ℝ, x = 8 * (16 * c ^ 3) ^ (ε / (4 * (ε / 4 + 3 * ((1033 : ℝ) / 1000)))) *
      (1 + Real.log (8 * c ^ 2) + (ε / 4 + 2 * ((1033 : ℝ) / 1000)) / (ε / 12)) ^ 3 *
      (2 * c) ^ (ε / (4 * ((1033 : ℝ) / 1000))) := ⟨_, rfl⟩
  obtain ⟨CT0, hCT0def⟩ : ∃ x : ℝ, x = CN * max 1 (8 * c ^ 2) * L2D_zeta F (3 / 2) *
      L2D_zeta F 4 * (Fintype.card Dd.T : ℝ) := ⟨_, rfl⟩
  obtain ⟨CT, hCTdef⟩ : ∃ x : ℝ, x = CT0 ^ 2 * Cω * (2 * c) ^ (ε / (4 * ((1033 : ℝ) / 1000))) :=
    ⟨_, rfl⟩
  have hCR : 0 ≤ CR := by
    rw [hCRdef]
    have : 0 ≤ max K0 0 := le_max_right _ _
    positivity
  have hCv : 0 ≤ Cv := by
    rw [hCvdef]
    have : 0 ≤ Real.log (8 * c ^ 2) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ 1 + Real.log (8 * c ^ 2) + (ε / 4 + 2 * ((1033 : ℝ) / 1000)) / (ε / 12) := by
      positivity
    positivity
  have hCT : 0 ≤ CT := by rw [hCTdef]; positivity
  refine ⟨2 * CR * Cv + 4 * A * CT, fun Z hZ P D hP hD υ h hPh hh2P => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZe : 0 ≤ Z ^ ε := Real.rpow_nonneg hZ0.le _
  have hXp : 0 ≤ D + D ^ 2 * P / Z := by positivity
  -- the row set
  let Q : RowClass 𝔪 → Prop := fun r => r.2 = υ ∧ h * simplePart r.1.1 = r.1.1 ∧
    (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
    D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧ (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D
  by_cases hne : ∃ r : RowClass 𝔪, Q r
  swap
  · refine ⟨0, ?_, ?_⟩
    · have : IsEmpty {r : RowClass 𝔪 // Q r} := ⟨fun r => hne ⟨r.1, r.2⟩⟩
      exact hasSum_empty
    · have : 0 ≤ 2 * CR * Cv + 4 * A * CT := by positivity
      positivity
  obtain ⟨r0, hr0⟩ := hne
  have hb0 : r0.1.1 ≠ ⊥ := r0.1.2.1
  have hpow := L2D_powerful_of_mul r0.1.1 h hb0 hr0.2.1
  have hh0 : h ≠ ⊥ := hpow.1
  have hPD : P * D ≤ c * Z ^ ((1033 : ℝ) / 1000) := by
    have hN : (Ideal.absNorm r0.1.1 : ℝ) = Ideal.absNorm h * Ideal.absNorm (simplePart r0.1.1) := by
      conv_lhs => rw [← hr0.2.1]
      rw [map_mul]; push_cast; ring
    have hD0 : 0 ≤ D := by linarith
    calc P * D ≤ Ideal.absNorm h * Ideal.absNorm (simplePart r0.1.1) :=
          mul_le_mul hPh hr0.2.2.2.1 hD0 (by positivity)
      _ = Ideal.absNorm r0.1.1 := hN.symm
      _ ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) := hr0.2.2.1
      _ ≤ c * Z ^ ((1033 : ℝ) / 1000) := by rw [hcdef]; gcongr; exact le_max_left _ _
  have hhP : (Ideal.absNorm h : ℝ) ≤ 2 * P := hh2P.le
  -- finiteness and the sum
  have hfin : Finite {r : RowClass 𝔪 // Q r} := by
    let φ : {r : RowClass 𝔪 // Q r} → {x // x ∈ L2D_le F (c₂ * Z ^ ((1033 : ℝ) / 1000))} :=
      fun r => ⟨r.1.1.1, L2D_mem_le.2 r.2.2.2.1⟩
    apply Finite.of_injective φ
    intro r r' hrr
    simp only [φ, Subtype.mk.injEq] at hrr
    apply Subtype.ext
    exact Prod.ext (Subtype.ext hrr) (r.2.1.trans r'.2.1.symm)
  have hSfin : Set.Finite {r : RowClass 𝔪 | Q r} := by
    have : Finite ({r : RowClass 𝔪 | Q r} : Set (RowClass 𝔪)) := hfin
    exact Set.toFinite _
  obtain ⟨R0, hR0def⟩ : ∃ x : ℝ, x = Z ^ (ε / 4) * (8 * D ^ 2 * P / Z) := ⟨_, rfl⟩
  let f : RowClass 𝔪 → ℝ := fun r => ‖χ.thetaSum g (rowElt g r) Z‖ ^ 2
  let G : Ideal (𝓞 F) → ℝ := fun d =>
    2 * ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 + 2 * ‖L2D_TailT Dd υ h d Z R0‖ ^ 2
  refine ⟨∑ r ∈ hSfin.toFinset, f r, ?_, ?_⟩
  · have hind : HasSum ({r : RowClass 𝔪 | Q r}.indicator f) (∑ r ∈ hSfin.toFinset, f r) := by
      have h1 : ∑ r ∈ hSfin.toFinset, f r =
          ∑ r ∈ hSfin.toFinset, ({r : RowClass 𝔪 | Q r}.indicator f) r := by
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
  -- per-row bound and injectivity
  have hpt : ∀ r ∈ hSfin.toFinset, f r ≤ G (simplePart r.1.1) := by
    intro r hr
    have hq := (Set.Finite.mem_toFinset hSfin).1 hr
    have hdec := L2D_decomp Dd r h hq.2.1 hZ0 R0
    simp only [f, G]
    rw [hdec, hq.1]
    exact L2D_norm_add_sq_le _ _
  have hinj : Set.InjOn (fun r : RowClass 𝔪 => simplePart r.1.1) hSfin.toFinset := by
    intro r hr r' hr' heq
    have hq := (Set.Finite.mem_toFinset hSfin).1 hr
    have hq' := (Set.Finite.mem_toFinset hSfin).1 hr'
    have h1 : r.1.1 = r'.1.1 := by
      rw [← hq.2.1, ← hq'.2.1]; simp only at heq; rw [heq]
    exact Prod.ext (Subtype.ext h1) (hq.1.trans hq'.1.symm)
  have hsub : hSfin.toFinset.image (fun r : RowClass 𝔪 => simplePart r.1.1) ⊆ L2D_Rows 𝔪 D := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨r, hr, rfl⟩ := hd
    have hq := (Set.Finite.mem_toFinset hSfin).1 hr
    have hbr : r.1.1 ≠ ⊥ := r.1.2.1
    unfold L2D_Rows
    rw [L2D_mem_cols]
    refine ⟨by linarith [hq.2.2.2.2], L2D_exterior_of_dvd r.1.2 (L2D_simplePart_dvd r.1.1 hbr),
      L2D_simplePart_squarefree r.1.1 hbr⟩
  -- the retained and tail bounds
  have hRB : ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 ≤
      CR * Cv * (Z ^ ε * (D + D ^ 2 * P / Z)) := by
    by_cases hR : 1 ≤ R0
    · have h1 := L2D_RB Dd υ h hh0 (P := P) hZ0 hR hD hhP KΨ (max K0 0) _ Bh Cω _
        (le_max_right _ _) hKΨ0 hBh0.le hδ1.le hKΨ (hLSK R0 (2 * D) hR (by linarith))
        (hBh R0 hR) hCω
      rw [hR0def] at hR
      have h2 := L2D_B1 hc1 hE1 hZ1 hP hD hPD hε hR
      rw [← hR0def] at h2
      calc _ ≤ _ := h1
        _ ≤ KΨ ^ 2 * max K0 0 * Bh ^ 3 * (Fintype.card Dd.T : ℝ) ^ 2 * Cω *
              (Cv * Z ^ ε * (D + D ^ 2 * P / Z)) := by
            rw [hCvdef]
            have : 0 ≤ KΨ ^ 2 * max K0 0 * Bh ^ 3 * (Fintype.card Dd.T : ℝ) ^ 2 * Cω := by
              have : 0 ≤ max K0 0 := le_max_right _ _
              positivity
            exact mul_le_mul_of_nonneg_left h2 this
        _ = CR * Cv * (Z ^ ε * (D + D ^ 2 * P / Z)) := by rw [hCRdef]; ring
    · have : ∀ d ∈ L2D_Rows 𝔪 D, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 = 0 := by
        intro d _
        rw [L2D_RetT_eq_zero Dd υ h d Z R0 (by linarith)]; simp
      rw [Finset.sum_eq_zero this]
      positivity
  have hTB : ∀ d ∈ L2D_Rows 𝔪 D, ‖L2D_TailT Dd υ h d Z R0‖ ^ 2 ≤ CT * Z ^ ε := by
    intro d hd
    obtain ⟨hd1, hd2, _⟩ := L2D_mem_cols.1 hd
    have h1 := L2D_TB Dd υ h d hh0 hd2.1 hZ hD hP hc1 hPD hδ hM hδM hhP hd1 hCN hCN0 hδ1.le hCω
    rw [← hR0def] at h1
    have hPc : P ≤ c * Z ^ ((1033 : ℝ) / 1000) := le_trans (le_mul_of_one_le_right (by linarith) hD) hPD
    have h2 := L2D_B2 hc1 hZ1 hP hδ1.le hPc
    have h3 : Z ^ ((1033 : ℝ) / 1000 * (ε / (4 * ((1033 : ℝ) / 1000)))) ≤ Z ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_le hZ1
      have e : (1033 : ℝ) / 1000 * (ε / (4 * ((1033 : ℝ) / 1000))) = ε / 4 := by
        field_simp
      rw [e]; linarith
    have hq : 0 ≤ CT0 ^ 2 * Cω := by positivity
    calc ‖L2D_TailT Dd υ h d Z R0‖ ^ 2 ≤ CT0 ^ 2 * (Cω * (2 * P) ^ (ε / (4 * ((1033 : ℝ) / 1000)))) := by
          rw [hCT0def]; exact h1
      _ = CT0 ^ 2 * Cω * (2 * P) ^ (ε / (4 * ((1033 : ℝ) / 1000))) := by ring
      _ ≤ CT0 ^ 2 * Cω * ((2 * c) ^ (ε / (4 * ((1033 : ℝ) / 1000))) * Z ^ ε) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = CT * Z ^ ε := by rw [hCTdef]; ring
  have hRows : ((L2D_Rows 𝔪 D).card : ℝ) ≤ A * (2 * D) := by
    have hsub' : L2D_Rows 𝔪 D ⊆ L2D_le F (2 * D) := by
      intro d hd
      rw [L2D_mem_le]; exact (L2D_mem_cols.1 hd).1
    exact (Nat.cast_le.2 (Finset.card_le_card hsub')).trans (hA _ (by linarith))
  have hG0 : ∀ d, 0 ≤ G d := fun d => by positivity
  have hDX : D ≤ D + D ^ 2 * P / Z := by
    have : 0 ≤ D ^ 2 * P / Z := by positivity
    linarith
  calc ∑ r ∈ hSfin.toFinset, f r ≤ ∑ r ∈ hSfin.toFinset, G (simplePart r.1.1) :=
        Finset.sum_le_sum hpt
    _ = ∑ d ∈ hSfin.toFinset.image (fun r : RowClass 𝔪 => simplePart r.1.1), G d :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ d ∈ L2D_Rows 𝔪 D, G d := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => hG0 d
    _ = 2 * ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_RetT Dd υ h d Z R0‖ ^ 2 +
          2 * ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_TailT Dd υ h d Z R0‖ ^ 2 := by
        simp only [G, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (CR * Cv * (Z ^ ε * (D + D ^ 2 * P / Z))) + 2 * ((L2D_Rows 𝔪 D).card * (CT * Z ^ ε)) := by
        have h1 : ∑ d ∈ L2D_Rows 𝔪 D, ‖L2D_TailT Dd υ h d Z R0‖ ^ 2 ≤
            (L2D_Rows 𝔪 D).card * (CT * Z ^ ε) := by
          calc _ ≤ ∑ _d ∈ L2D_Rows 𝔪 D, CT * Z ^ ε := Finset.sum_le_sum hTB
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        linarith [hRB, h1]
    _ ≤ 2 * (CR * Cv * (Z ^ ε * (D + D ^ 2 * P / Z))) + 2 * ((A * (2 * D)) * (CT * Z ^ ε)) := by
        have : 0 ≤ CT * Z ^ ε := mul_nonneg hCT hZe
        have := mul_le_mul_of_nonneg_right hRows this
        linarith
    _ ≤ (2 * CR * Cv + 4 * A * CT) * Z ^ ε * (D + D ^ 2 * P / Z) := by
        have : (A * (2 * D)) * (CT * Z ^ ε) ≤ (2 * A * CT * Z ^ ε) * (D + D ^ 2 * P / Z) := by
          calc (A * (2 * D)) * (CT * Z ^ ε) = (2 * A * CT * Z ^ ε) * D := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hDX (by positivity)
        nlinarith [this]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: the cuts `L2D_Cut63`, `L2D_Cut64` from the published Lemma 6.3 and Lemma 6.4. -/

open Classical in
lemma L2D_cut63_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L2D_Cut63 n F ι := by
  obtain ⟨N₀, hN₀⟩ := exists_cutoff_exists_thetaSum_rowElt_eq_tsum n hn0 hn F ι
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨T, fT, ω, ρ, lam, Φ, α, hα, hω, hω0, hρ, hlam, hΦ, hΦb, hid⟩ := hN₀ 𝔪 h𝔪 hs χ g
  refine ⟨T, fT, ω, ρ, lam, Φ, α, hα, fun υ 𝔥 𝔣 𝔞 𝔫 s => ?_, hρ, hlam, hΦ, hΦb, hid⟩
  unfold L2D_beta
  split_ifs with hsupp
  · exact hω υ 𝔥 𝔣 𝔞 𝔫 s
  · push Not at hsupp
    rw [hω0 υ 𝔥 𝔣 𝔞 𝔫 s hsupp, norm_zero]

lemma L2D_cut64_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L2D_Cut64 n F ι :=
  exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le n hn0 hn F ι

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: the per-powerful-part bound from Lemma 6.3 and Lemma 6.4. -/

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
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
              σ ≤ C * Z ^ ε * (D + D ^ 2 * P / Z) :=
  L2D_cutH_of_cuts n F ι (L2D_cut63_of_stub n hn0 hn F ι) (L2D_cut64_of_stub n hn0 hn F ι)
end
