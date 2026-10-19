-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:00:37.406764+00:00
-- url     : https://prove2.me/submissions/4d770877-2150-41b6-af6a-efff29134b54

import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent
import Mathlib


section
section
/-! # L3G_Iter: the Heath-Brown / Goldmakher–Louvel exponent iteration, abstractly

`B C D v` stands for "the sieve form with columns of norm `≤ C` and rows of norm `≤ D` is bounded
by `v · ‖z‖²`". Rows are cut by `≤ D`, so `B` is monotone in `D` for free (GL's Lemma 4.4 is not
needed). From GL Lemma 4.2 (`E 2`, or any `E α₀`) and GL Theorem 4.3 (`E α → T α`) we get `E 1`. -/

namespace L3G

open Real

/-- (E_α) of Goldmakher–Louvel §4, with `M = D` (rows) and `N = C` (columns). -/
def E (B : ℝ → ℝ → ℝ → Prop) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D → B C D (K * (D + C ^ α) * (C * D) ^ ε)

/-- The conclusion of Goldmakher–Louvel Theorem 4.3. -/
def T (B : ℝ → ℝ → ℝ → Prop) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
    B C D (K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε)

variable {B : ℝ → ℝ → ℝ → Prop}

/-- GL Theorem 4.1: `T α ⇒ E (2 − 1/α)`. -/
theorem step (monoD : ∀ C D D' v, D ≤ D' → B C D' v → B C D v)
    (monoV : ∀ C D v v', v ≤ v' → B C D v → B C D v') {α : ℝ} (hα : 1 ≤ α)
    (hT : T B α) : E B (2 - 1 / α) := by
  intro ε hε
  obtain ⟨K, hK⟩ := hT (ε / 3) (by positivity)
  refine ⟨3 * max K 0, fun C D hC hD => ?_⟩
  set β := 2 - 1 / α with hβdef
  have hα0 : 0 < α := by linarith
  have hβ1 : 1 ≤ β := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  have hβ2 : β ≤ 2 := by have : 0 < 1 / α := by positivity
                         linarith
  set D2 := max D (C ^ β) with hD2
  have hC0 : 0 < C := by linarith
  have hCβ : 1 ≤ C ^ β := Real.one_le_rpow hC (by linarith)
  have hD21 : 1 ≤ D2 := le_trans hD (le_max_left _ _)
  have hD20 : 0 < D2 := by linarith
  have h1 := monoD C D D2 _ (le_max_left _ _) (hK C D2 hC hD21)
  apply monoV _ _ _ _ _ h1
  -- the value bound
  have ha : C ^ (2 * α - 1) * D2 ^ (1 - α) ≤ D2 := by
    have hpow : C ^ (2 * α - 1) ≤ D2 ^ α := by
      have : C ^ (2 * α - 1) = (C ^ β) ^ α := by
        rw [← Real.rpow_mul hC0.le]; congr 1; rw [hβdef]; field_simp
      rw [this]
      exact Real.rpow_le_rpow (by positivity) (le_max_right _ _) hα0.le
    calc C ^ (2 * α - 1) * D2 ^ (1 - α) ≤ D2 ^ α * D2 ^ (1 - α) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = D2 := by rw [← Real.rpow_add hD20]; simp
  have hb : C ≤ C ^ β := by
    calc C = C ^ (1 : ℝ) := (Real.rpow_one C).symm
      _ ≤ C ^ β := Real.rpow_le_rpow_of_exponent_le hC hβ1
  have hc : D2 ≤ D + C ^ β := by
    rw [hD2]; apply max_le <;> linarith
  have hsum : D2 + C + C ^ (2 * α - 1) * D2 ^ (1 - α) ≤ 3 * (D + C ^ β) := by linarith
  have hCD : 1 ≤ C * D := by nlinarith
  have hd : (C * D2) ^ (ε / 3) ≤ (C * D) ^ ε := by
    have hC2 : C ^ β ≤ C ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC hβ2
    have hD2le : D2 ≤ D * C ^ 2 := by
      rw [hD2]; apply max_le
      · nlinarith
      · rw [Real.rpow_two] at hC2; nlinarith
    have : C * D2 ≤ (C * D) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h3 : C * D2 ≤ C * (D * C ^ 2) := mul_le_mul_of_nonneg_left hD2le hC0.le
      have hD3 : D ≤ D ^ 3 := by
        have : 1 ≤ D ^ 2 := by nlinarith
        nlinarith
      have : C * (D * C ^ 2) ≤ (C * D) ^ 3 := by
        rw [mul_pow]
        have : 0 ≤ C ^ 3 := by positivity
        nlinarith
      linarith
    calc (C * D2) ^ (ε / 3) ≤ ((C * D) ^ (3 : ℝ)) ^ (ε / 3) :=
          Real.rpow_le_rpow (by positivity) this (by positivity)
      _ = (C * D) ^ ε := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; ring
  have hK0 : K ≤ max K 0 := le_max_left _ _
  have hM0 : 0 ≤ max K 0 := le_max_right _ _
  have hs0 : 0 ≤ D2 + C + C ^ (2 * α - 1) * D2 ^ (1 - α) := by positivity
  have he0 : 0 ≤ (C * D2) ^ (ε / 3) := by positivity
  calc K * (D2 + C + C ^ (2 * α - 1) * D2 ^ (1 - α)) * (C * D2) ^ (ε / 3)
      ≤ max K 0 * (D2 + C + C ^ (2 * α - 1) * D2 ^ (1 - α)) * (C * D2) ^ (ε / 3) := by
        gcongr
    _ ≤ max K 0 * (3 * (D + C ^ β)) * (C * D) ^ ε := by gcongr
    _ = 3 * max K 0 * (D + C ^ β) * (C * D) ^ ε := by ring

/-- Iterating `step` from `E (1 + t)`: `E (1 + t/(1 + k t))` for all `k`. -/
theorem iterate (monoD : ∀ C D D' v, D ≤ D' → B C D' v → B C D v)
    (monoV : ∀ C D v v', v ≤ v' → B C D v → B C D v')
    (hT : ∀ α : ℝ, 1 ≤ α → E B α → T B α) {t : ℝ} (ht : 0 ≤ t) (h0 : E B (1 + t)) :
    ∀ k : ℕ, E B (1 + t / (1 + k * t)) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hk : 0 ≤ (k : ℝ) * t := by positivity
    have hα : 1 ≤ 1 + t / (1 + k * t) := by
      have : 0 ≤ t / (1 + k * t) := by positivity
      linarith
    have h := step monoD monoV hα (hT _ hα ih)
    have : 2 - 1 / (1 + t / (1 + k * t)) = 1 + t / (1 + ((k + 1 : ℕ) : ℝ) * t) := by
      push_cast
      field_simp
      ring
    rwa [this] at h

/-- `E 1` in the leaf's shape `K (C + D) (C D)^ε`, from `E (1 + t)` and GL Theorem 4.3. -/
theorem final (monoD : ∀ C D D' v, D ≤ D' → B C D' v → B C D v)
    (monoV : ∀ C D v v', v ≤ v' → B C D v → B C D v')
    (hT : ∀ α : ℝ, 1 ≤ α → E B α → T B α) {t : ℝ} (ht : 0 ≤ t) (h0 : E B (1 + t)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      B C D (K * (C + D) * (C * D) ^ ε) := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hit := iterate monoD monoV hT ht h0 k
  obtain ⟨K, hK⟩ := hit (ε / 2) (by positivity)
  refine ⟨max K 0, fun C D hC hD => ?_⟩
  apply monoV _ _ _ _ _ (hK C D hC hD)
  set s := t / (1 + k * t) with hs
  have hs0 : 0 ≤ s := by positivity
  have hk0 : (0 : ℝ) < k := by
    have : 0 < 2 / ε := by positivity
    linarith
  have hsle : s ≤ ε / 2 := by
    rw [hs]
    rcases ht.eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · rw [div_le_iff₀ (by positivity)]
      have : 2 / ε * ε = 2 := by field_simp
      have h2 : 2 < k * ε := by nlinarith
      nlinarith
  have hC0 : 0 < C := by linarith
  have hCD : 1 ≤ C * D := by nlinarith
  have hCs : C ^ (1 + s) ≤ C * (C * D) ^ (ε / 2) := by
    rw [Real.rpow_add hC0, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    calc C ^ s ≤ (C * D) ^ s := Real.rpow_le_rpow hC0.le (by nlinarith) hs0
      _ ≤ (C * D) ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hCD hsle
  have he1 : 1 ≤ (C * D) ^ (ε / 2) := Real.one_le_rpow hCD (by positivity)
  have hsum : D + C ^ (1 + s) ≤ (C + D) * (C * D) ^ (ε / 2) := by nlinarith
  have hmul : (C * D) ^ (ε / 2) * (C * D) ^ (ε / 2) = (C * D) ^ ε := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  have hM0 : 0 ≤ max K 0 := le_max_right _ _
  calc K * (D + C ^ (1 + s)) * (C * D) ^ (ε / 2)
      ≤ max K 0 * (D + C ^ (1 + s)) * (C * D) ^ (ε / 2) := by
        have hX : 0 ≤ D + C ^ (1 + s) := by
          have : 0 ≤ C ^ (1 + s) := by positivity
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
          (by positivity)
    _ ≤ max K 0 * ((C + D) * (C * D) ^ (ε / 2)) * (C * D) ^ (ε / 2) := by gcongr
    _ = max K 0 * (C + D) * (C * D) ^ ε := by rw [← hmul]; ring

end L3G

end
end

section
section
/-! # L3G_Core: Cut64 (Lemma 6.4) from GL Lemma 4.2 (E_α) and GL Theorem 4.3

`L3G.leaf_of_cuts` proves the leaf's statement from the two cut statements given as hypotheses
(stated verbatim as in the draft stubs, but taking (E_{α₀}) for any `α₀ ≥ 1` in
`L3G.leaf_of_cutE_cut43`). No stub is imported here. -/

namespace L3G

open NumberField ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F]

/-- The sieve form with columns of norm `≤ C`, rows of norm `≤ D`, is bounded by `v ‖z‖²`. -/
def SB (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (C D v : ℝ) : Prop :=
  ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
    ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
        ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
      v * ∑' 𝔠, ‖z 𝔠‖ ^ 2

theorem rows_finite (𝔪 : Ideal (𝓞 F)) (D : ℝ) :
    Finite {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D} := by
  have hs : {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ D}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊D⌋₊).subset
      (fun 𝔡 h => Nat.le_floor h.2.2)
  exact hs.to_subtype

theorem SB_monoD (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) :
    ∀ C D D' v, D ≤ D' → SB ι 𝔪 g C D' v → SB ι 𝔪 g C D v := by
  intro C D D' v hDD h z
  refine le_trans ?_ (h z)
  have := rows_finite 𝔪 D
  have := rows_finite 𝔪 D'
  let e : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D} →
      {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D'} :=
    fun 𝔡 => ⟨𝔡.1, 𝔡.2.1, 𝔡.2.2.1, 𝔡.2.2.2.trans hDD⟩
  have he : Function.Injective e := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext this
  exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => by positivity) (fun _ => le_rfl)
    (Summable.of_finite) (Summable.of_finite)

theorem SB_monoV (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) :
    ∀ C D v v', v ≤ v' → SB ι 𝔪 g C D v → SB ι 𝔪 g C D v' := by
  intro C D v v' hv h z
  refine (h z).trans ?_
  exact mul_le_mul_of_nonneg_right hv (tsum_nonneg fun _ => by positivity)

theorem smallPrimesDvd_mono {N₁ N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪)
    (hN : N₁ ≤ N₀) : SmallPrimesDvd N₁ 𝔪 :=
  fun P hP hb hle => h P hP hb (hle.trans hN)

/-- The leaf from (E_{α₀}) for some `α₀ ≥ 1` (GL Lemma 4.2 has `α₀ = 2`) and GL Theorem 4.3. -/
theorem leaf_of_cutE_cut43 (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) (α₀ : ℝ)
    (hα₀ : 1 ≤ α₀)
    (hE : ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        SB ι 𝔪 g C D (K * (D + C ^ α₀) * (C * D) ^ ε))
    (hT : ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          SB ι 𝔪 g C D (K * (D + C ^ α) * (C * D) ^ ε)) →
        ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          SB ι 𝔪 g C D (K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε)) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        SB ι 𝔪 g C D (K * (C + D) * (C * D) ^ ε) := by
  obtain ⟨N₁, h₁⟩ := hE
  obtain ⟨N₂, h₂⟩ := hT
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hs g => ?_⟩
  have hs₁ := smallPrimesDvd_mono hs (le_max_left N₁ N₂)
  have hs₂ := smallPrimesDvd_mono hs (le_max_right N₁ N₂)
  have h0 : E (SB ι 𝔪 g) (1 + (α₀ - 1)) := by
    rw [show 1 + (α₀ - 1) = α₀ by ring]
    exact h₁ 𝔪 h𝔪 hs₁ g
  exact final (SB_monoD ι 𝔪 g) (SB_monoV ι 𝔪 g) (fun α hα hEα => h₂ 𝔪 h𝔪 hs₂ g α hα hEα)
    (by linarith) h0

end L3G

end
end

section
section
/-! # L3E_Leaf: Cut64 (b6fc3e16) from the E₆ draft cut and GL Theorem 4.3 (10138558)

The variant of `L3G_Main` with `α₀ = 6`: E₆ replaces GL Lemma 4.2 (E₂) as the starting bound. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (C + D) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  obtain ⟨N₁, h₁⟩ :=
    exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six n hn0 hn F ι
  refine L3G.leaf_of_cutE_cut43 F ι 6 (by norm_num) ⟨N₁, fun 𝔪 h𝔪 hs g ε hε => ?_⟩
    (exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent n hn0 hn F ι)
  obtain ⟨K, hK⟩ := h₁ 𝔪 h𝔪 hs g ε hε
  refine ⟨K, fun C D hC hD => ?_⟩
  rw [show (C ^ (6 : ℝ)) = C ^ 6 by norm_cast]
  exact hK C D hC hD

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (C + D) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  exact ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le n hn0 hn F ι

end
