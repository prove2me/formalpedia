-- Prove2me | Definitions.Def_RPLib_S3_HasseWeilB
-- name    : RPLib_S3_HasseWeilB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:48:07.736124+00:00
-- url     : https://prove2.me/theorems/5671dd4d-da13-41d4-a2fe-392af9002c6c
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound
-- statement:
--   S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound.
--
--   For a function field `F / Fq` with full constant field (`q = #Fq`, `g = genusF Fq F`):
--   * `delta_eq_one`: the least positive divisor degree is `1` (F.K. Schmidt). By `numPoints_powerSum` (any `δ`),
--     `δ + Q ^ k - N_{δk} = Σ_z e(z) z ^ k` with `Q = q ^ δ`, `e = δ · count_c - (δ - 1)·[z = Q]`; the two-sided bound
--     `two_sided` makes this `O(√Q ^ k)` along `k ∈ D·ℕ`, so (ExpSum) the grouped coefficient at `Q` (`|Q| > √Q`)
--     vanishes: `δ · a = δ - 1` with `a ∈ ℕ`, hence `δ = 1`.
--   * `zeta_shape`: `N_m = 1 + q ^ m - Σ_i α_i ^ m` for all `m ≥ 1`, at most `2g` numbers `α_i`, each `|α_i| ≤ √q`.
--   * `hasse_weil`: `|N_m - q ^ m - 1| ≤ 2 g √q ^ m` for all `m ≥ 1`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_HasseWeilA
import Definitions.Def_RPLib_S3_ZetaC
import Definitions.Def_RPLib_S3_ExpSum

/-!
# S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound

For a function field `F / Fq` with full constant field (`q = #Fq`, `g = genusF Fq F`):
* `delta_eq_one`: the least positive divisor degree is `1` (F.K. Schmidt). By `numPoints_powerSum` (any `δ`),
  `δ + Q ^ k - N_{δk} = Σ_z e(z) z ^ k` with `Q = q ^ δ`, `e = δ · count_c - (δ - 1)·[z = Q]`; the two-sided bound
  `two_sided` makes this `O(√Q ^ k)` along `k ∈ D·ℕ`, so (ExpSum) the grouped coefficient at `Q` (`|Q| > √Q`)
  vanishes: `δ · a = δ - 1` with `a ∈ ℕ`, hence `δ = 1`.
* `zeta_shape`: `N_m = 1 + q ^ m - Σ_i α_i ^ m` for all `m ≥ 1`, at most `2g` numbers `α_i`, each `|α_i| ≤ √q`.
* `hasse_weil`: `|N_m - q ^ m - 1| ≤ 2 g √q ^ m` for all `m ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Filter Asymptotics

namespace RamanujanPetersson.ZetaSB

open Places RR

section HWB

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **F.K. Schmidt**: a function field with full constant field has a divisor of degree one. -/
theorem delta_eq_one (hk : constField Fq F = ⊥) : delta Fq F = 1 := by
  classical
  have hδ := delta_pos Fq F
  obtain ⟨c, -, hN⟩ := numPoints_powerSum hk (2 * genusF Fq F + 2) (by omega)
    (fun k hk2 => by
      have h1 : k ≤ delta Fq F * k := Nat.le_mul_of_pos_left k hδ
      generalize delta Fq F * k = t at h1 ⊢
      omega)
    (fun h => absurd h (by omega))
  obtain ⟨D, hD, C, j0, hb⟩ := two_sided Fq F hk
  set δ := delta Fq F with hδdef
  set q := Fintype.card Fq with hqdef
  have hq1 : 1 < q := Fintype.one_lt_card
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ, Q = (q : ℂ) ^ δ := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt q ^ δ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := hR ▸ pow_nonneg (Real.sqrt_nonneg _) _
  have hR1 : 1 ≤ R := hR ▸ one_le_pow₀ (Real.one_le_sqrt.mpr (by exact_mod_cast hq1.le))
  have hexp : ∀ k, 1 ≤ k → ∑ z ∈ insert Q c.toFinset,
      ((δ : ℂ) * (c.count z : ℂ) - if z = Q then (δ : ℂ) - 1 else 0) * z ^ k =
        (δ : ℂ) + Q ^ k - (Places.numPoints Fq F (δ * k) : ℂ) := by
    intro k hk1
    rw [hN k hk1]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_insert_self, if_true]
    rw [← ExpSum.powerSum_eq_sum_count_of_subset c (Finset.subset_insert _ _), hQ, ← pow_mul]
    ring
  have hbig : (fun N : ℕ => ∑ z ∈ insert Q c.toFinset,
      ((δ : ℂ) * (c.count z : ℂ) - if z = Q then (δ : ℂ) - 1 else 0) * z ^ (D * N + 0)) =O[atTop]
        (fun N : ℕ => R ^ (D * N)) := by
    refine Asymptotics.IsBigO.of_bound ((δ : ℝ) + |C|)
      (Filter.eventually_atTop.mpr ⟨max j0 1, fun N hN => ?_⟩)
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNj : j0 ≤ δ * N := le_trans (le_of_max_le_left hN) (Nat.le_mul_of_pos_left N hδ)
    have hk1 : 1 ≤ D * N := Nat.mul_pos hD hN1
    rw [add_zero, hexp (D * N) hk1]
    have hb' := hb (δ * N) hNj
    rw [show D * (δ * N) = δ * (D * N) by ring] at hb'
    have hcast : (δ : ℂ) + Q ^ (D * N) - (Places.numPoints Fq F (δ * (D * N)) : ℂ) =
        (((δ : ℝ) + (q : ℝ) ^ (δ * (D * N)) - Places.numPoints Fq F (δ * (D * N)) : ℝ) : ℂ) := by
      rw [hQ, ← pow_mul]; push_cast; ring
    have hRk : Real.sqrt q ^ (δ * (D * N)) = R ^ (D * N) := by rw [hR, ← pow_mul]
    rw [hRk] at hb'
    have hR1k : 1 ≤ R ^ (D * N) := one_le_pow₀ hR1
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR0 _)]
    obtain ⟨h1, h2⟩ := abs_le.mp hb'
    have hCa := le_abs_self C
    have hCa' := neg_abs_le C
    have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
    have p1 := mul_le_mul_of_nonneg_right hCa (le_trans zero_le_one hR1k)
    have p2 := mul_le_mul_of_nonneg_right hCa' (le_trans zero_le_one hR1k)
    have p3 := mul_le_mul_of_nonneg_left hR1k hδ0
    rw [abs_le]
    constructor <;> nlinarith
  have hQs : Q ∈ insert Q c.toFinset := Finset.mem_insert_self _ _
  have hkey := ExpSum.norm_le_of_expSum_isBigO_ap (insert Q c.toFinset) _ hR0 hD 0 hbig Q hQs
  have hQR : R < ‖Q‖ := by
    rw [hQ, hR, norm_pow, Complex.norm_natCast]
    exact pow_lt_pow_left₀ (Real.sqrt_lt_self_iff.mpr (by exact_mod_cast hq1)) (Real.sqrt_nonneg _) hδ.ne'
  have hfib : ∑ w ∈ insert Q c.toFinset with w ^ D = Q ^ D,
      ((δ : ℂ) * (c.count w : ℂ) - if w = Q then (δ : ℂ) - 1 else 0) * w ^ 0 = 0 := by
    by_contra h
    exact absurd (hkey h) (not_le.mpr hQR)
  have hQt : Q ∈ (insert Q c.toFinset).filter (fun w => w ^ D = Q ^ D) :=
    Finset.mem_filter.mpr ⟨hQs, rfl⟩
  set a := ∑ w ∈ insert Q c.toFinset with w ^ D = Q ^ D, c.count w with ha
  have hcalc : ∑ w ∈ insert Q c.toFinset with w ^ D = Q ^ D,
      ((δ : ℂ) * (c.count w : ℂ) - if w = Q then (δ : ℂ) - 1 else 0) * w ^ 0 =
        (δ : ℂ) * (a : ℂ) - ((δ : ℂ) - 1) := by
    simp only [pow_zero, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum, ha, Nat.cast_sum]
    rw [Finset.sum_ite_eq', if_pos hQt]
  rw [hcalc] at hfib
  have hnat : δ * a + 1 = δ := by
    have : ((δ * a + 1 : ℕ) : ℂ) = (δ : ℂ) := by push_cast; linear_combination hfib
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · rw [ha0, mul_zero, zero_add] at hnat
    exact hnat.symm
  · exfalso
    nlinarith

/-- `A_1 = q + 1` in genus `0` (from `numEff_formula` at `n = 0, 1`). -/
theorem numEff_one_of_genus_zero (hk : constField Fq F = ⊥) (hg : genusF Fq F = 0)
    (hδ1 : delta Fq F = 1) : numEff Fq F 1 = 1 + Fintype.card Fq := by
  obtain ⟨h, hh⟩ := numEff_formula hk
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hq0 : ((Fintype.card Fq : ℤ) - 1) ≠ 0 := by omega
  have h0 := hh 0 (by rw [hδ1]; exact one_dvd 0) (by rw [hg]; norm_num)
  have h1 := hh 1 (by rw [hδ1]) (by rw [hg]; norm_num)
  rw [numEff_zero, hg] at h0
  rw [hg] at h1
  simp only [Nat.cast_one, mul_one, Nat.sub_zero, zero_add, pow_one] at h0
  have hfac : ((h : ℤ) - 1) * ((Fintype.card Fq : ℤ) - 1) = 0 := by linear_combination -h0
  have hh1 : (h : ℤ) = 1 := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · exact absurd h' hq0
  have hfac2 : ((numEff Fq F 1 : ℤ) - (1 + Fintype.card Fq)) * ((Fintype.card Fq : ℤ) - 1) = 0 := by
    simp only [Nat.sub_zero] at h1
    linear_combination h1 + ((Fintype.card Fq : ℤ) ^ 2 - 1) * hh1
  rcases mul_eq_zero.mp hfac2 with h' | h'
  · have : (numEff Fq F 1 : ℤ) = 1 + Fintype.card Fq := by linarith
    exact_mod_cast this
  · exact absurd h' hq0

/-- **Shape of the zeta function**: `N_m = 1 + q ^ m - Σ_i α_i ^ m` (`m ≥ 1`) with at most `2g` numbers `α_i`,
all of modulus at most `√q`. -/
theorem zeta_shape (hk : constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      ∀ m : ℕ, 1 ≤ m →
        (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum := by
  classical
  have hδ1 := delta_eq_one Fq F hk
  obtain ⟨c, hc, hN⟩ := numPoints_powerSum hk (2 * genusF Fq F + 1) (by omega)
    (fun k hk2 => by rw [hδ1, one_mul]; omega)
    (fun h => by
      have hg : genusF Fq F = 0 := by omega
      rw [hδ1, pow_one]
      exact numEff_one_of_genus_zero Fq F hk hg hδ1)
  have hN' : ∀ m : ℕ, 1 ≤ m →
      (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum := by
    intro m hm
    have := hN m hm
    simpa only [hδ1, one_mul, Nat.cast_one] using this
  refine ⟨c, by omega, ?_, hN'⟩
  obtain ⟨D, hD, C, j0, hb⟩ := two_sided Fq F hk
  have hR0 : 0 ≤ Real.sqrt (Fintype.card Fq) := Real.sqrt_nonneg _
  have hR1 : 1 ≤ Real.sqrt (Fintype.card Fq) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (Fintype.one_lt_card (α := Fq)).le)
  refine ExpSum.multiset_norm_le_of_powerSum_isBigO_ap c hR0 hD ?_
  refine Asymptotics.IsBigO.of_bound (1 + |C|) (Filter.eventually_atTop.mpr ⟨max j0 1, fun N hN => ?_⟩)
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hk1 : 1 ≤ D * N := Nat.mul_pos hD hN1
  have hb' := hb N (le_of_max_le_left hN)
  have hS : (c.map (· ^ (D * N))).sum = (((1 : ℝ) + (Fintype.card Fq : ℝ) ^ (D * N) -
      Places.numPoints Fq F (D * N) : ℝ) : ℂ) := by
    push_cast; rw [hN' (D * N) hk1]; ring
  have hR1k : 1 ≤ Real.sqrt (Fintype.card Fq) ^ (D * N) := one_le_pow₀ hR1
  rw [hS, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR0 _)]
  obtain ⟨h1, h2⟩ := abs_le.mp hb'
  have p1 := mul_le_mul_of_nonneg_right (le_abs_self C) (le_trans zero_le_one hR1k)
  have p2 := mul_le_mul_of_nonneg_right (neg_abs_le C) (le_trans zero_le_one hR1k)
  rw [abs_le]
  constructor <;> nlinarith

/-- **Hasse-Weil bound** (Stepanov-Bombieri route): for a function field `F / Fq` with full constant field,
`|N_m - q ^ m - 1| ≤ 2 g √q ^ m` for every `m ≥ 1`. -/
theorem hasse_weil (hk : constField Fq F = ⊥) (m : ℕ) (hm : 1 ≤ m) :
    |(Places.numPoints Fq F m : ℝ) - (Fintype.card Fq : ℝ) ^ m - 1| ≤
      2 * (genusF Fq F : ℝ) * Real.sqrt (Fintype.card Fq) ^ m := by
  obtain ⟨c, hc, hnorm, hN⟩ := zeta_shape Fq F hk
  have hS : (c.map (· ^ m)).sum = (((1 : ℝ) + (Fintype.card Fq : ℝ) ^ m - Places.numPoints Fq F m : ℝ) : ℂ) := by
    push_cast; rw [hN m hm]; ring
  have hbound : ‖(c.map (· ^ m)).sum‖ ≤ Multiset.card c * Real.sqrt (Fintype.card Fq) ^ m := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    refine (Multiset.sum_le_card_nsmul _ (Real.sqrt (Fintype.card Fq) ^ m) fun x hx => ?_).trans ?_
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      simp only [Function.comp_apply, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm y hy) m
    · rw [Multiset.card_map, nsmul_eq_mul]
  rw [hS, Complex.norm_real, Real.norm_eq_abs] at hbound
  rw [show (Places.numPoints Fq F m : ℝ) - (Fintype.card Fq : ℝ) ^ m - 1 =
    -((1 : ℝ) + (Fintype.card Fq : ℝ) ^ m - Places.numPoints Fq F m) by ring, abs_neg]
  refine hbound.trans ?_
  have : (Multiset.card c : ℝ) ≤ 2 * (genusF Fq F : ℝ) := by exact_mod_cast hc
  exact mul_le_mul_of_nonneg_right this (pow_nonneg (Real.sqrt_nonneg _) _)

end HWB

end RamanujanPetersson.ZetaSB


