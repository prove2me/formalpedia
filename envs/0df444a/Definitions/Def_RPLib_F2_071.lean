-- Prove2me | Definitions.Def_RPLib_F2_071
-- name    : RPLib_F2_071
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:01:26.560601+00:00
-- url     : https://prove2.me/theorems/e39494d5-487c-49a1-b453-3bf39b699e42
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 071 (part 1 of file 028 of 70)
-- statement:
--   File 071 (part 1 of file 028 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S3.HasseWeil_B`: S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound
--   * `S4.Def_RP_PicDescent_A`: S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`
--   * `S4.Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
--   * `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
--   * `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
--   * `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
--   * `S4.Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--   * `S4.Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
--   * `S4.Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
--   * `S4.Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_026

/-!
# Ramanujan-Petersson curve library (flat edition), file 071 (part 1 of file 028 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S3.HasseWeil_B`: S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound
* `S4.Def_RP_PicDescent_A`: S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`
* `S4.Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
* `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
* `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
* `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
* `S4.Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
* `S4.Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
* `S4.Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
* `S4.Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
-/

set_option autoImplicit false

-- ===== S3.HasseWeil_B =====
section

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

end HWB

end RamanujanPetersson.ZetaSB


end

-- ===== S4.Def_RP_PicDescent_A =====
section

/-!
# S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`

* `Pic Fq F := Divisor Fq F ⧸ princ Fq F`, `degPic`, `Pic0 Fq F := ker degPic`.
* `exists_deg_one` (**F. K. Schmidt**, from S3-ZetaSB's `delta_eq_one`): with full constant field there is a
  divisor of degree `1`.
* `finite_Pic0`, `card_Pic0_eq_hcl`: `Pic⁰` is finite and its order is the number of classes of any degree
  `N ≥ 2g - 1`; `card_Pic0_mul`: `A_N (q - 1) = h (q ^ (N + 1 - g) - 1)` with `h = #Pic⁰`.
* `prod_eq_of_newton` (abstract power-series lemma) and **`classNumber_eq_prod`**: for EVERY multiset `c ⊆ ℂ` with
  `N_m = 1 + q^m - Σ_i c_i^m` for all `m ≥ 1`, `#Pic⁰(F) = Π_i (1 - c_i)`, i.e. `h = L(1)`.
* `classNumber_zeta`: the same together with S3-ZetaSB's `zeta_shape` (`#c ≤ 2g`, `‖c_i‖ ≤ √q`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places RR ZetaSB

section PS

open PowerSeries

end PS

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **F. K. Schmidt**: with full constant field there is a divisor of degree `1`. -/
theorem exists_deg_one (hk : constField Fq F = ⊥) : ∃ D : Divisor Fq F, Divisor.deg D = 1 := by
  obtain ⟨-, D, hD⟩ := delta_mem Fq F
  exact ⟨D, by rw [hD, delta_eq_one Fq F hk, Nat.cast_one]⟩

variable {Fq F}

/-- Translation by a class of degree `N` identifies `Pic⁰` with the classes of degree `N`, which (for
`N ≥ 2g - 1`) are exactly the classes of effective divisors of degree `N`. -/
theorem nonempty_equiv_classes [DecidableEq (Pic Fq F)] (hk : constField Fq F = ⊥) {N : ℕ}
    (hN : 2 * (genusF Fq F : ℤ) - 1 ≤ N) :
    Nonempty (Pic0 Fq F ≃ ((effDivs Fq F N).image (cls Fq F))) := by
  obtain ⟨D1, hD1⟩ := exists_deg_one Fq F hk
  set B : Pic Fq F := cls Fq F ((N : ℤ) • D1) with hB
  have hdegB : degPic Fq F B = N := by rw [hB, cls, degPic_mk, deg_zsmul, hD1, mul_one]
  have hT : ∀ y : Pic Fq F, y ∈ (effDivs Fq F N).image (cls Fq F) ↔ degPic Fq F y = N := by
    intro y
    constructor
    · intro hy
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hy
      rw [cls, degPic_mk, (mem_effDivs.mp hE).2]
    · intro hy
      obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective y
      obtain ⟨E, hE, hEc⟩ := exists_eff_of_deg hk hN D (by rwa [degPic_mk] at hy)
      exact Finset.mem_image.mpr ⟨E, hE, hEc⟩
  exact ⟨{ toFun := fun x => ⟨x.1 + B, (hT _).mpr (by rw [map_add, (mem_Pic0 Fq F).mp x.2, hdegB, zero_add])⟩
           invFun := fun y => ⟨y.1 - B, (mem_Pic0 Fq F).mpr (by rw [map_sub, (hT _).mp y.2, hdegB, sub_self])⟩
           left_inv := fun x => Subtype.ext (add_sub_cancel_right _ _)
           right_inv := fun y => Subtype.ext (sub_add_cancel _ _) }⟩

/-- `Pic⁰(F)` is finite (full constant field). -/
theorem finite_Pic0 (hk : constField Fq F = ⊥) : Finite (Pic0 Fq F) := by
  classical
  obtain ⟨e⟩ := nonempty_equiv_classes (F := F) hk (N := 2 * genusF Fq F) (by push_cast; omega)
  exact Finite.of_equiv _ e.symm

theorem card_Pic0_eq_hcl [DecidableEq (Pic Fq F)] (hk : constField Fq F = ⊥) {N : ℕ}
    (hN : 2 * (genusF Fq F : ℤ) - 1 ≤ N) : Nat.card (Pic0 Fq F) = hcl Fq F N := by
  obtain ⟨e⟩ := nonempty_equiv_classes hk hN
  rw [Nat.card_congr e, Nat.card_eq_finsetCard]
  rfl

/-- `A_N (q - 1) = h (q ^ (N + 1 - g) - 1)` for `N ≥ 2g - 1`, with `h = #Pic⁰(F)`. -/
theorem card_Pic0_mul (hk : constField Fq F = ⊥) {N : ℕ} (hN : 2 * (genusF Fq F : ℤ) - 1 ≤ N) :
    numEff Fq F N * (Fintype.card Fq - 1) =
      Nat.card (Pic0 Fq F) * (Fintype.card Fq ^ (N + 1 - genusF Fq F) - 1) := by
  classical
  rw [card_Pic0_eq_hcl hk hN]
  exact numEff_mul hk hN

/-- **Class number = `L(1)`.** For every multiset `c ⊆ ℂ` with `N_m = 1 + q^m - Σ_i c_i^m` (`m ≥ 1`),
`#Pic⁰(F) = Π_i (1 - c_i)`. -/
theorem classNumber_eq_prod (hk : constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) :
    (Nat.card (Pic0 Fq F) : ℂ) = (c.map fun z => 1 - z).prod := by
  classical
  have hδ1 := delta_eq_one Fq F hk
  have hq1 : 1 ≤ Fintype.card Fq := Fintype.card_pos
  have hp1 : ∀ e : ℕ, 1 ≤ Fintype.card Fq ^ e := fun e => Nat.one_le_pow _ _ Fintype.card_pos
  have hq : (Fintype.card Fq : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (Fintype.one_lt_card (α := Fq)).ne')
  have key : ∀ n : ℕ, 2 * (genusF Fq F : ℤ) - 1 ≤ n →
      (numEff Fq F n : ℂ) * ((Fintype.card Fq : ℂ) - 1) =
        (Nat.card (Pic0 Fq F) : ℂ) * ((Fintype.card Fq : ℂ) ^ (n + 1 - genusF Fq F) - 1) := by
    intro n hn
    have h := congrArg (Nat.cast : ℕ → ℂ) (card_Pic0_mul hk hn)
    push_cast [Nat.cast_sub hq1, Nat.cast_sub (hp1 _)] at h
    exact h
  symm
  refine prod_eq_of_newton (fun k => (numEff Fq F k : ℂ)) (fun j => (numPoints Fq F j : ℂ))
    (Fintype.card Fq : ℂ) (Nat.card (Pic0 Fq F) : ℂ) c (2 * genusF Fq F) (by simp [numEff_zero]) ?_
    (fun k => hc (k + 1) (Nat.succ_pos k)) ?_
  · intro k
    have h := newton_delta' Fq F k
    simp only [hδ1, one_mul] at h
    have h' := congrArg (Nat.cast : ℕ → ℂ) h
    push_cast at h'
    linear_combination h'
  · intro n hn
    have e1 := key n (by omega)
    have e2 := key (n + 1) (by push_cast; omega)
    rw [show n + 1 + 1 - genusF Fq F = (n + 1 - genusF Fq F) + 1 by omega, pow_succ] at e2
    apply mul_left_cancel₀ hq
    linear_combination e2 - (Fintype.card Fq : ℂ) * e1

/-- `h = L(1)` with S3-ZetaSB's inverse roots: `#c ≤ 2g`, `‖c_i‖ ≤ √q`, `N_m = 1 + q^m - Σ c_i^m`,
`#Pic⁰(F) = Π (1 - c_i)`. -/
theorem classNumber_zeta (hk : constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) ∧
      (Nat.card (Pic0 Fq F) : ℂ) = (c.map fun z => 1 - z).prod := by
  obtain ⟨c, h1, h2, h3⟩ := zeta_shape Fq F hk
  exact ⟨c, h1, h2, h3, classNumber_eq_prod hk c h3⟩

end Pic

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_CoreA_ZInt =====
section

/-!
# S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function

For a function field `F / Fq` with full constant field, `q = #Fq`, `g = genusF Fq F`, `A_n = numEff Fq F n`, and
ANY multiset `c ⊆ ℂ` with `N_m = 1 + q^m - Σ_i c_i^m` (`m ≥ 1`):
* `prod_eq_zeta_F` (Z1): `Π_i (1 - c_i X) = (1 - X)(1 - q X) Σ_n A_n X^n` in `ℂ⟦X⟧`;
* `exists_int_poly` (Z1): `Π_i (1 - c_i X)` has integer coefficients;
* `numEff_top'` (Z2): `(q - 1) A_{2g-2} = h (q^(g-1) - 1) + q^g - q^(g-1)` (`g ≥ 1`, `h = #Pic⁰`), from Riemann-Roch:
  a class of degree `2g - 2` has `ℓ = g` if it is canonical and `ℓ = g - 1` otherwise;
* **`card_eq_two_genus`** (Z2): if moreover `#c ≤ 2g`, then `#c = 2g`, `Π_i c_i = q^g`, and `Π_i (1 - c_i X)` is the
  image of an integer polynomial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.CoreA

open Places RR ZetaSB PicDescent

section PS

open PowerSeries

end PS

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

open PowerSeries in
/-- Z1, concrete: `Π (1 - c_i X) = (1 - X)(1 - q X) Z(X)` with `Z(X) = Σ A_n X^n`. -/
theorem prod_eq_zeta_F (hk : constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) :
    (c.map fun r => 1 - C r * X).prod = (1 - C 1 * X) * ((1 - C (Fintype.card Fq : ℂ) * X) *
      PowerSeries.mk fun k => (numEff Fq F k : ℂ)) := by
  refine prod_eq_zeta (fun k => (numEff Fq F k : ℂ)) (fun j => (numPoints Fq F j : ℂ)) _ c
    (by simp [numEff_zero]) ?_ (fun k => hc (k + 1) (Nat.succ_pos k))
  intro k
  have h := newton_delta' Fq F k
  simp only [delta_eq_one Fq F hk, one_mul] at h
  have h' := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at h'
  linear_combination h'

/-- For `g ≥ 2` every class of degree `2g - 2` has an effective member, so there are `h` of them. -/
theorem hcl_top [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) (hg : 2 ≤ genusF Fq F) :
    hcl Fq F (2 * genusF Fq F - 2) = Nat.card (Pic0 Fq F) := by
  obtain ⟨D1, hD1⟩ := exists_deg_one Fq F hk
  have h1 : 2 * (genusF Fq F : ℤ) - 1 ≤ ((2 * genusF Fq F - 1 : ℕ) : ℤ) := by omega
  rw [card_Pic0_eq_hcl hk h1]
  apply le_antisymm
  · exact hcl_le hk h1 ((-1 : ℤ) • D1) (by rw [deg_zsmul, hD1]; omega)
  · exact hcl_le' hk (by omega) D1 (by rw [hD1]; omega)

/-- Z2: `(q - 1) A_{2g-2} = h (q^(g-1) - 1) + q^g - q^(g-1)` for `g ≥ 1`, `h = #Pic⁰`. -/
theorem numEff_top' (hk : constField Fq F = ⊥) (hg : 1 ≤ genusF Fq F) :
    ((Fintype.card Fq : ℤ) - 1) * numEff Fq F (2 * genusF Fq F - 2) =
      Nat.card (Pic0 Fq F) * ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        ((Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)) := by
  classical
  obtain ⟨W, hW⟩ := exists_isCanonicalF (Fq := Fq) (F := F)
  rw [numEff_top hk hW hg]
  rcases Nat.lt_or_ge (genusF Fq F) 2 with h2 | h2
  · rw [show genusF Fq F - 1 = 0 by omega, pow_zero, sub_self, mul_zero, mul_zero]
  · rw [hcl_top hk h2]

/-- **Z2.** If `N_m = 1 + q^m - Σ c_i^m` for all `m ≥ 1` and `#c ≤ 2g`, then `#c = 2g`, `Π c_i = q^g`, and
`Π (1 - c_i X)` has integer coefficients. -/
theorem card_eq_two_genus (hk : constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (hcard : Multiset.card c ≤ 2 * genusF Fq F) :
    Multiset.card c = 2 * genusF Fq F ∧ c.prod = (Fintype.card Fq : ℂ) ^ genusF Fq F ∧
      ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  classical
  have hP := prod_eq_zeta_F hk c hc
  have hL : ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod :=
    exists_int_poly (fun k => (numEff Fq F k : ℤ)) (Fintype.card Fq : ℤ) c (by simpa using hP)
  rcases Nat.eq_zero_or_pos (genusF Fq F) with hg0 | hg1
  · have hc0 : c = 0 := Multiset.card_eq_zero.mp (by omega)
    subst hc0
    exact ⟨by simp [hg0], by simp [hg0], hL⟩
  have hq1 : 1 ≤ Fintype.card Fq := Fintype.card_pos
  have hp1 : ∀ e : ℕ, 1 ≤ Fintype.card Fq ^ e := fun e => Nat.one_le_pow _ _ Fintype.card_pos
  have hq : (Fintype.card Fq : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (Fintype.one_lt_card (α := Fq)).ne')
  have key : ∀ n : ℕ, 2 * (genusF Fq F : ℤ) - 1 ≤ n →
      (numEff Fq F n : ℂ) * ((Fintype.card Fq : ℂ) - 1) =
        (Nat.card (Pic0 Fq F) : ℂ) * ((Fintype.card Fq : ℂ) ^ (n + 1 - genusF Fq F) - 1) := by
    intro n hn
    have h := congrArg (Nat.cast : ℕ → ℂ) (card_Pic0_mul hk hn)
    push_cast [Nat.cast_sub hq1, Nat.cast_sub (hp1 _)] at h
    exact h
  obtain ⟨g', hg'⟩ : ∃ g', genusF Fq F = g' + 1 := ⟨genusF Fq F - 1, by omega⟩
  have e2 := key (2 * g' + 1 + 1) (by omega)
  have e1 := key (2 * g' + 1) (by omega)
  have e0 := congrArg (Int.cast : ℤ → ℂ) (numEff_top' hk (by omega))
  rw [hg', show 2 * (g' + 1) - 2 = 2 * g' by omega, show g' + 1 - 1 = g' by omega] at e0
  rw [hg', show 2 * g' + 1 + 1 + 1 - (g' + 1) = g' + 2 by omega] at e2
  rw [hg', show 2 * g' + 1 + 1 - (g' + 1) = g' + 1 by omega] at e1
  push_cast at e0
  set p : ℂ[X] := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  have hcoef : p.coeff (2 * g' + 1 + 1) = (Fintype.card Fq : ℂ) ^ (g' + 1) := by
    have h2 := congrArg (PowerSeries.coeff (2 * g' + 1 + 1)) hP
    rw [← coe_prod_one_sub, ← hpdef, Polynomial.coeff_coe, coeff_succ_one_sub_mul, coeff_succ_one_sub_mul,
      coeff_succ_one_sub_mul] at h2
    simp only [PowerSeries.coeff_mk] at h2
    rw [h2]
    apply mul_left_cancel₀ hq
    linear_combination e2 - (1 + (Fintype.card Fq : ℂ)) * e1 + (Fintype.card Fq : ℂ) * e0
  have hpdeg : p.natDegree ≤ Multiset.card c := natDegree_prod_one_sub_le c
  have hcard' : Multiset.card c = 2 * genusF Fq F := by
    by_contra hne
    have hlt : p.natDegree < 2 * g' + 1 + 1 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at hcoef
    exact (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hcoef.symm
  refine ⟨hcard', ?_, hL⟩
  have h3 := coeff_card_prod_one_sub c
  have hev : (-1 : ℂ) ^ (2 * g' + 1 + 1) = 1 := Even.neg_one_pow ⟨g' + 1, by ring⟩
  rw [← hpdef, hcard', hg', show 2 * (g' + 1) = 2 * g' + 1 + 1 by ring, hcoef, hev, one_mul] at h3
  rw [hg', h3]

end Concrete

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CP4a_FE =====
section

/-!
# S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius

* `zeta_RH_FE` (function fields with full constant field): the inverse zeta roots `c` (S3-ZetaSB `zeta_shape`)
  satisfy `#c = 2g`, `‖c_i‖ = √q` (RH equality, from `Π c_i = q^g` of CoreA `card_eq_two_genus`), `0 ∉ c`,
  `conj c = c`, the functional equation `{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic `P0 ∈ ℤ[X]`.
* `det_mul_charpolyRev_of_mul_eq`: `G M = q` gives `det M · det(1 - X G) = (-1)^d · χ_M(q X)`.
* `exists_trace_pow_frob` (review R4): if `χ_M = P0`, `P0 = Π (X - c_i)` over `ℂ`, `{q / c_i} = {c_i}` and
  `G M = q` with `q` a unit, then `tr(M^(k+1))`, `tr(G^(k+1))` and `Σ c_i^(k+1)` are one integer `s k`.
  (`M` = arithmetic Frobenius `π` on `T_l`, `G = q π⁻¹` = geometric Frobenius on `H^1`.)
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Alg

variable {K : Type*} [Field K]

end Alg

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

end Mat

section Concrete

open Places RR ZetaSB

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **RH equality + functional equation** for a function field with full constant field: the inverse zeta roots
`c` have `#c = 2g`, `‖c_i‖ = √q`, `Π c_i = q^g`, `N_m = 1 + q^m - Σ c_i^m`, `0 ∉ c`, `conj c = c`,
`{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic integer polynomial. -/
theorem zeta_RH_FE (hk : constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c = 2 * genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ = Real.sqrt (Fintype.card Fq)) ∧ c.prod = (Fintype.card Fq : ℂ) ^ genusF Fq F ∧
      (∀ m : ℕ, 1 ≤ m →
        (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) ∧
      (0 : ℂ) ∉ c ∧ c.map (starRingEnd ℂ) = c ∧ c.map (fun x => (Fintype.card Fq : ℂ) / x) = c ∧
      ∃ P0 : ℤ[X], P0.Monic ∧ P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod := by
  obtain ⟨c, hcard, hle, hN⟩ := ZetaSB.zeta_shape Fq F hk
  obtain ⟨hcard2, hprod, L, hL⟩ := CoreA.card_eq_two_genus hk c hN hcard
  have hq : (0 : ℝ) < Fintype.card Fq := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card Fq) := Real.sqrt_pos.mpr hq
  have hnorm : ∀ x ∈ c, ‖x‖ = Real.sqrt (Fintype.card Fq) := by
    refine norm_eq_of_norm_prod c _ hsq hle ?_
    rw [hprod, hcard2, norm_pow, Complex.norm_natCast, pow_mul, Real.sq_sqrt hq.le]
  have h0 : (0 : ℂ) ∉ c := by
    intro h
    have := hnorm 0 h
    rw [norm_zero] at this
    exact hsq.ne' this.symm
  have hconj := conj_stable c L hL h0
  have hfe : c.map (fun x => (Fintype.card Fq : ℂ) / x) = c := by
    have := fe_of_norm c (Fintype.card Fq) hq hnorm hconj
    simpa using this
  refine ⟨c, hcard2, hnorm, hprod, hN, h0, hconj, hfe, L.reflect (Multiset.card c), ?_, ?_⟩
  · have hmap : (L.reflect (Multiset.card c)).map (Int.castRingHom ℂ) =
        (c.map fun r => X - Polynomial.C r).prod := by
      rw [← reflect_map, hL, ← reflect_prod_X_sub_C, reflect_reflect]
    refine Polynomial.monic_of_injective (RingHom.injective_int (Int.castRingHom ℂ)) ?_
    rw [hmap]
    exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  · rw [← reflect_map, hL, ← reflect_prod_X_sub_C, reflect_reflect]

end Concrete

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_PicDescent_C2 =====
section

/-!
# S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`

`F_n = Fc Fq F Ω n` over `L_n = Lc Fq Ω n` (`Ω` algebraically closed, `#L_n = q ^ n`).
* `numPoints_Fc`: `N_k(F_n) = N_{nk}(F)`.
* `classNumber_Fc`: for any multiset `c` with `N_m(F) = 1 + q^m - Σ c_i^m` (`m ≥ 1`),
  `#Pic⁰(F_n) = Π (1 - c_i ^ n)`.
* `Lpoly c n = Π (1 - c_i^n t)`, the `L`-polynomial of `F_n`; `classNumber_Fc_zeta`: with the zeta multiset of
  `F` (`|c_i| ≤ √q`, at most `2g` roots), `h_n = #Pic⁰(F_n) = L_n(1) = Π (1 - c_i ^ n)` for every `n ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Polynomial

section ClassNumber

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]

variable {Fq F}

/-- **Class numbers of the constant field extensions**: `#Pic⁰(F_n) = Π (1 - c_i ^ n)`. -/
theorem classNumber_Fc (hk : Places.constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (n : ℕ) [NeZero n] :
    (Nat.card (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) : ℂ) = (c.map fun z => 1 - z ^ n).prod := by
  rw [classNumber_eq_prod (constField_Fc Fq F Ω hk n) (c.map (· ^ n))
    (numPoints_Fc_formula Ω hk c hc n), Multiset.map_map]
  rfl

/-- **`h_n = L_n(1) = Π (1 - ω_i ^ n)`** for all constant field extensions `F_n`, with the zeta multiset
`ω` of `F` (`|ω_i| ≤ √q`, at most `2g` of them, `N_m(F) = 1 + q^m - Σ ω_i^m`); `Pic⁰(F_n)` is finite and
`N_m(F_n) = 1 + (q^n)^m - Σ (ω_i^n)^m`. -/
theorem classNumber_Fc_zeta (hk : Places.constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * RR.genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) ∧
      ∀ (n : ℕ) [NeZero n], Finite (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) ∧
        (∀ m : ℕ, 1 ≤ m → (Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) m : ℂ) =
          1 + ((Fintype.card Fq : ℂ) ^ n) ^ m - (c.map fun z => (z ^ n) ^ m).sum) ∧
        (Nat.card (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) : ℂ) = (Lpoly c n).eval 1 ∧
        (Lpoly c n).eval 1 = (c.map fun z => 1 - z ^ n).prod := by
  obtain ⟨c, h1, h2, h3, -⟩ := classNumber_zeta hk
  refine ⟨c, h1, h2, h3, fun n _ => ⟨finite_Pic0 (constField_Fc Fq F Ω hk n), fun m hm => ?_, ?_,
    eval_one_Lpoly c n⟩⟩
  · rw [numPoints_Fc_formula Ω hk c h3 n m hm, card_Lc_fintype Fq Ω n, Multiset.map_map]
    push_cast
    rfl
  · rw [eval_one_Lpoly, classNumber_Fc Ω hk c h3 n]

end ClassNumber

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_E3 =====
section

/-!
# S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers

`X̄ = F̄ ⊗ K` is modelled inside `Ω` (algebraically closed) as the union of the constant field extensions
`F_n = Fc Fq F Ω n`; the levels `lev j = (j+1)!` are cofinal for divisibility.
* `PicBar Ω hk`: the direct limit of `Pic(F_{lev j})` along the conorm maps `tr` (= `conNN`), i.e. `Pic(X̄)`;
* `piBar`: the arithmetic Frobenius `π` (`x ↦ x ^ q` on the constants) acting on `Pic(X̄)`;
* `degBar`, `PicBar0 = ker degBar` (`Pic⁰(X̄)`);
* `toBar m : Pic(F_m) →+ Pic(X̄)`, injective, with image `fixedBar m = Pic(X̄)^(π^m)`:
  **`picBarEquiv m : Pic(F_m) ≃+ Pic(X̄)^(π^m)`**, **`pic0BarEquiv m : Pic⁰(F_m) ≃+ Pic⁰(X̄)^(π^m)`**;
* the base level: `picBaseEquiv : Pic(F) ≃+ Pic(X̄)^π`, `pic0BaseEquiv : Pic⁰(F) ≃+ Pic⁰(X̄)^π`;
* `classNumber_bar`: `#Pic⁰(X̄)^(π^m) = h_m = L_m(1) = Π (1 - ω_i ^ m)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Bar

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-! ### The arithmetic Frobenius on `Pic(X̄)` -/

/-! ### Degree and `Pic⁰(X̄)` -/

/-! ### `Pic(F_m) → Pic(X̄)` and descent -/

section Descent

variable [IsAlgClosed Ω]

/-- **Descent**: a class of `Pic(X̄)` fixed by `π ^ m` comes from `Pic(F_m)`. -/
theorem exists_toBar_eq (m : ℕ) [NeZero m] (z : PicBar Ω hk) (hz : z ∈ fixedBar Ω hk m) :
    ∃ x : Pic (Lc Fq Ω m) (Fc Fq F Ω m), toBar Ω hk m x = z := by
  revert hz
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  intro hz
  change ofBar Ω hk j y ∈ fixedBar Ω hk m at hz
  change ∃ x : Pic (Lc Fq Ω m) (Fc Fq F Ω m), toBar Ω hk m x = ofBar Ω hk j y
  have hjj : j ≤ max j m := le_max_left j m
  have hmj : m ≤ max j m := le_max_right j m
  have e : ofBar Ω hk j y = ofBar Ω hk (max j m) (tr Ω hk j (max j m) hjj y) :=
    (AddCommGroup.DirectLimit.of_f hjj y).symm
  rw [e] at hz ⊢
  generalize tr Ω hk j (max j m) hjj y = y' at hz ⊢
  rw [mem_fixedBar, piBar_iterate_of] at hz
  have hz' := ofBar_injective hk _ hz
  have : Fact (m ∣ lev (max j m)) := ⟨dvd_lev (NeZero.pos m) hmj⟩
  obtain ⟨x, hx⟩ := exists_conNN_eq hk y' hz'
  exact ⟨x, by rw [toBar_eq hk m hmj x, hx]⟩

variable (Ω) in
/-- **Galois descent for `Pic⁰` over `X̄`**: `Pic⁰(F_m) ≃+ Pic⁰(X̄)^(π^m)`. -/
noncomputable def pic0BarEquiv (m : ℕ) [NeZero m] :
    Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) ≃+ (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨toBar Ω hk m x.1,
          AddSubgroup.mem_inf.2 ⟨toBar_mem hk m x.1, (toBar_mem_PicBar0 hk m x.1).2 x.2⟩⟩
       map_zero' := Subtype.ext (map_zero (toBar Ω hk m))
       map_add' := fun x y => Subtype.ext (map_add (toBar Ω hk m) x.1 y.1) } :
      Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) →+ (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)))
    ⟨fun x y hxy => Subtype.ext (toBar_injective hk m (congrArg Subtype.val hxy)), fun z => by
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 z.2
      obtain ⟨x, hx⟩ := exists_toBar_eq hk m z.1 h1
      have hx0 : x ∈ Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) := by
        rw [← toBar_mem_PicBar0 hk m x, hx]
        exact h2
      exact ⟨⟨x, hx0⟩, Subtype.ext hx⟩⟩

theorem pic0BarEquiv_apply (m : ℕ) [NeZero m] (x : Pic0 (Lc Fq Ω m) (Fc Fq F Ω m)) :
    (pic0BarEquiv Ω hk m x : PicBar Ω hk) = toBar Ω hk m x := rfl

/-! ### The base level `m = 1` and class numbers -/

theorem card_fixedBar0 (m : ℕ) [NeZero m] :
    Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) =
      Nat.card (Pic0 (Lc Fq Ω m) (Fc Fq F Ω m)) :=
  (Nat.card_congr (pic0BarEquiv Ω hk m).toEquiv).symm

end Descent

end Bar

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_Kummer_PicMap =====
section

/-!
# S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

Session 10 (compiled). `Psi hk N α = [div(α ^ N) / N]`; parabolic radicals have `N ∣ ord` everywhere
(`dvd_ord_of_par`: finite places by Lev, infinite places by InfMain); `Psi_mul`, `Psi_congr` (depends only on the class),
`Psi_mem`, `mem_fixUnits_of_Psi_eq_zero` (kernel), `exists_Psi_eq` (surjective), `exists_kummerPicEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

end Generic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

section PsiMap

variable {p e : ℕ} [Fact p.Prime] [CharP F p]

variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} [NeZero N]
  (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

include hk hq he hNf hNi hDB hlift

theorem Psi_mul {α β : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβ : β ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    Psi hk N (α * β) = Psi hk N α + Psi hk N β := by
  obtain ⟨m1, hm1, h1⟩ := exists_Fc_of_rad hq he hα
  obtain ⟨m2, hm2, h2⟩ := exists_Fc_of_rad hq he hβ
  have : NeZero (m1 * m2) := ⟨(Nat.mul_pos hm1 hm2).ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) (m1 * m2),
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N :=
    ⟨⟨_, Fc_le (Fq := Fq) (F := F) (Ω := AlgebraicClosure F) (hnN := dvd_mul_right m1 m2) h1⟩, rfl⟩
  obtain ⟨b, hb_eq⟩ : ∃ b : Fc Fq F (AlgebraicClosure F) (m1 * m2),
      (b : AlgebraicClosure F) = ((β : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N :=
    ⟨⟨_, Fc_le (Fq := Fq) (F := F) (Ω := AlgebraicClosure F) (hnN := dvd_mul_left m2 m1) h2⟩, rfl⟩
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ (coe_unit_ne_zero α))
  have hb := kFc_ne_zero hb_eq (pow_ne_zero _ (coe_unit_ne_zero β))
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift (m1 * m2) ha hα ha_eq.symm hpar
  rw [Psi_eq hk (α * β) (a * b) ?_, Psi_eq hk α a ha_eq.symm, Psi_eq hk β b hb_eq.symm, psiAt_mul hk ha hb hdiv]
  simp only [Units.val_mul, MulMemClass.coe_mul, mul_pow]
  rw [ha_eq, hb_eq]

theorem Psi_congr {α β : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβ : β ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβpar : kclass hζ hζΓ hβ ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
    (h : kclass hζ hζΓ hα = kclass hζ hζΓ hβ) : Psi hk N α = Psi hk N β := by
  have hc : β⁻¹ * α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N := mul_mem (inv_mem hβ) hα
  have h1 : kclass hζ hζΓ hα = kclass hζ hζΓ hβ + kclass hζ hζΓ hc := by
    rw [← kclass_mul]
    exact kclass_congr hζ hζΓ (mul_inv_cancel_left β α).symm hα _
  have h0 : kclass hζ hζΓ hc = 0 := by
    have h2 : kclass hζ hζΓ hβ + kclass hζ hζΓ hc = kclass hζ hζΓ hβ + 0 := by rw [add_zero, ← h1, h]
    exact add_left_cancel h2
  have hfix := (kclass_eq_zero_iff hζ hζΓ hc).1 h0
  calc Psi hk N α = Psi hk N (β * (β⁻¹ * α)) := by rw [mul_inv_cancel_left]
    _ = Psi hk N β + Psi hk N (β⁻¹ * α) := Psi_mul hk hq he hNf hNi hζ hζΓ D hDB hlift hβ hc hβpar
    _ = Psi hk N β := by rw [Psi_eq_zero_of_mem_fixUnits hk hq he hfix, add_zero]

theorem Psi_mem_PicBar0N {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    Psi hk N α ∈ PicBar0N (AlgebraicClosure F) hk N := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) m,
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N := ⟨⟨_, h1⟩, rfl⟩
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ (coe_unit_ne_zero α))
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift m ha hα ha_eq.symm hpar
  rw [Psi_eq hk α a ha_eq.symm]
  exact ⟨psiAt_mem_PicBar0 hk ha hdiv, nsmul_psiAt hk ha hdiv⟩

include hNF in
/-- **Kernel**: a parabolic radical with `Ψ α = 0` is a `π₁^geo`-fixed unit (`α = u · b`, `u` constant, `b ∈ F_m`). -/
theorem mem_fixUnits_of_Psi_eq_zero {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
    (h0 : Psi hk N α = 0) : α ∈ fixUnits (pi1geo (Rfin Fq F) F (Fintype.card Fq)) := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) m,
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N := ⟨⟨_, h1⟩, rfl⟩
  have hα0 := coe_unit_ne_zero α
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ hα0)
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift m ha hα ha_eq.symm hpar
  rw [Psi_eq hk α a ha_eq.symm] at h0
  obtain ⟨b, hb, c, hc⟩ := exists_of_psiAt_eq_zero hk ha hdiv h0
  have hb0 : (b : AlgebraicClosure F) ≠ 0 := fun h => hb (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))
  have hcΩ : ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) =
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N / (b : AlgebraicClosure F) ^ N := by
    have h3 := congrArg Subtype.val hc
    rw [coe_algebraMap_LF, IntermediateField.coe_div, IntermediateField.coe_pow, ha_eq] at h3
    exact h3
  have hu : (((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) / (b : AlgebraicClosure F)) ^ N =
      ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) := by rw [div_pow, hcΩ]
  have hc0 : ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) ≠ 0 := by
    rw [hcΩ]; exact div_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hb0)
  have hrN : Nat.Coprime (Fintype.card Fq) N := by rw [hq]; exact coprime_q F p N hNF
  have hconst := isConst_of_pow_eq Fintype.one_lt_card hm hrN (mem_Lc.1 c.2) hc0 hu
  have hconst' : IsConst (p ^ e) (((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) / (b : AlgebraicClosure F)) := by
    rw [← hq]; exact hconst
  have huU := mem_maxUnram_of_isConst (Rfin Fq F) he hconst'
  have hFc : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]; exact le_sSup (Fc_mem_unramSet hq he m)
  have hbU := hFc b.2
  have hconstU : IsConst (Fintype.card Fq) (⟨_, huU⟩ : maxUnram (Rfin Fq F) F) := by
    obtain ⟨n, hn, hpow⟩ := hconst
    exact ⟨n, hn, Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hpow)⟩
  have hαeq : (α : maxUnram (Rfin Fq F) F) = ⟨_, huU⟩ * ⟨_, hbU⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact (div_mul_cancel₀ _ hb0).symm
  refine (mem_fixUnits _ α).2 fun σ hσ => ?_
  rw [hαeq, map_mul, (mem_pi1geo _ _ _ σ).1 hσ _ hconstU, fixed_of_mem_Fc hq he m σ hσ ⟨_, hbU⟩ b.2]

/-- **Surjectivity**: every `z ∈ Pic⁰(X̄)[N]` is `Ψ α` for a parabolic radical `α`. -/
theorem exists_Psi_eq {z : PicBar (AlgebraicClosure F) hk} (hz : z ∈ PicBar0N (AlgebraicClosure F) hk N) :
    ∃ α : (maxUnram (Rfin Fq F) F)ˣ, ∃ hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N,
      kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ∧ Psi hk N α = z := by
  obtain ⟨j, y, rfl⟩ := exists_lev_toBar hk z
  obtain ⟨a, ha, hdiv, hpsi⟩ := exists_psiAt_eq hk y hz.2
  have ha0 : (a : AlgebraicClosure F) ≠ 0 := fun h => ha (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure F) (NeZero.pos N)
  have hγU : γ ∈ maxUnram (Rfin Fq F) F :=
    (forall_dvd_ord_iff hk hq he (lev j) hNf ha).1 (fun v => hdiv (Sum.inl v)) γ hγ
  have hγ0 : (⟨γ, hγU⟩ : maxUnram (Rfin Fq F) F) ≠ 0 := by
    intro h
    have hγ' : γ = 0 := (congrArg Subtype.val h).trans (ZeroMemClass.coe_zero _)
    apply ha0
    rw [← hγ, hγ', zero_pow (NeZero.ne N)]
  have haα : (((Units.mk0 _ hγ0 : (maxUnram (Rfin Fq F) F)ˣ) : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N =
      a := hγ
  have hα : Units.mk0 _ hγ0 ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N := by
    refine (mem_rad _ _ _).2 fun σ hσ => fixed_of_mem_Fc hq he (lev j) σ hσ _ ?_
    rw [SubmonoidClass.coe_pow, haα]
    exact a.2
  refine ⟨_, hα, (kclass_mem_curveH1par_iff_ord hk hq he (lev j) hNi hζ hζΓ D hDB hlift ha hα haα).2.2
    (fun v => hdiv (Sum.inr v)), ?_⟩
  rw [Psi_eq hk _ a haα, hpsi]

include hNF in
/-- **K5d**: `H¹_par(π₁^geo, Z/N) ≃+ Pic⁰(X̄)[N]`, `[kchar α] ↦ [div(α ^ N) / N]`. -/
theorem exists_kummerPicEquiv :
    ∃ Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N,
      ∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α := by
  choose r hr hrx using fun x : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D =>
    kclass_surjective hζ hζΓ x.1
  have hrpar : ∀ x, kclass hζ hζΓ (hr x) ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D :=
    fun x => by rw [hrx x]; exact x.2
  let f : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D →+ PicBar0N (AlgebraicClosure F) hk N :=
    AddMonoidHom.mk'
      (fun x => ⟨Psi hk N (r x), Psi_mem_PicBar0N hk hq he hNf hNi hζ hζΓ D hDB hlift (hr x) (hrpar x)⟩)
      (fun x y => Subtype.ext (by
        show Psi hk N (r (x + y)) = Psi hk N (r x) + Psi hk N (r y)
        rw [← Psi_mul hk hq he hNf hNi hζ hζΓ D hDB hlift (hr x) (hr y) (hrpar x)]
        refine Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr (x + y)) (mul_mem (hr x) (hr y)) ?_ ?_
        · rw [kclass_mul hζ hζΓ (hr x) (hr y), hrx x, hrx y]; exact add_mem x.2 y.2
        · exact ((hrx (x + y)).trans (Submodule.coe_add x y)).trans
            ((congrArg₂ (· + ·) (hrx x) (hrx y)).symm.trans (kclass_mul hζ hζΓ (hr x) (hr y)).symm)))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : Psi hk N (r x) = 0 := congrArg Subtype.val hx
    have hfix := mem_fixUnits_of_Psi_eq_zero hk hq he hNf hNi hζ hζΓ D hDB hlift hNF (hr x) (hrpar x) h0
    exact Subtype.ext ((hrx x).symm.trans ((kclass_eq_zero_iff hζ hζΓ (hr x)).2 hfix))
  have hsurj : Function.Surjective f := by
    intro z
    have key := exists_Psi_eq hk hq he hNf hNi hζ hζΓ D hDB hlift z.2
    obtain ⟨α, hα, hpar, hΨ⟩ := key
    exact ⟨⟨kclass hζ hζΓ hα, hpar⟩, Subtype.ext
      ((Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr _) hα hpar (hrx _)).trans hΨ)⟩
  exact ⟨AddEquiv.ofBijective f ⟨hinj, hsurj⟩, fun α hα hpar =>
    Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr _) hα hpar (hrx _)⟩

end PsiMap

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConeComp =====
section

/-!
# S4-Lefschetz, L3a: composition law for the cone Frobenius

Generic (any topological group `G`, normal `Γ`, boundary subgroups `I`, any representation `ρ`):
* `conjMap_comp_eq`, `conjMap_one_eq`: `conjMap x ∘ conjMap y = conjMap (x y)`, `conjMap 1 = id`;
* `frob1_comp`, `frob2_comp`, `frobPC_comp`: the composite of two cone Frobenii is the cone Frobenius of the product,
  with the correcting elements `s ↦ ψ'⁻¹ h_s ψ' · h'_{t s}` of `FrobCong.twistc_comp`;
* `frobPC_pow`: `frobPC(ψ, t, h)^m = frobPC(ψ^m, t^[m], hpow m)` on every term of the perfect complex.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)

variable (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

/-- The cone Frobenius on `K¹` is `twistc` on the underlying pairs. -/
theorem frob1_val (ψ : G) (t : S → S) (h : S → Γ) (p : Z1 ρ Γ × (S → M)) :
    ((((frob1 ρ Γ ψ t h p).1 : Z1 ρ Γ) : Γ → M), (frob1 ρ Γ ψ t h p).2) =
      twistc ρ Γ ψ t h (((p.1 : Z1 ρ Γ) : Γ → M), p.2) := rfl

end Gen

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

end Model

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_JacLaw_Nu =====
section

/-!
# S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`

For choice data `D : NuData K F d` (`N = d + g`), `D.Rg = Sym^d(B)[1/good]` is the coordinate ring of the basic
open `D(good)`. At a point `x` of it with image `y = yOf x` in `Sym^d`, `A = liftTuple y` are `d` distinct
points, `s = sec y` spans `L(N P∞ - A)` and has `N` simple zeros `zeroFin s ⊇ A`; `ν(A) = Z(s) - A` is the
finset `nuSet x` of `g` points. The norms `N(w)(ν(A)) = ∏_{P ∈ ν(A)} w(P)` are the regular functions
`nrm w = (-1)^g coeff_0 ((Δ_1⁻¹ Δ_{X-w}) /ₘ ∏_{i}(X - w(a_i)))` on `D(good)` (`apply_nrm`), so the morphism
criterion (`liftPts`) gives `nuMap : Sym^g(B) →ₐ D.Rg` with points `nuPt x = ν(A)` (`comp_nuMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Nu

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ} (D : NuData K F d)

theorem apply_nrm (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) : x (D.nrm w) = ∏ φ ∈ D.nuSet x, φ w := by
  classical
  have hy := D.yOf_good x
  have h := apply_divByMonic_coeff x (D.isUnit_pres w).unit _ _ ((monic_monPoly w).map _) _ _ (injective_lift hy)
    (lift_mem_zeroFin hy) (fun φ => φ w) (D.map_det_Rg x w) (D.map_monPoly_Rg x w)
  have e : zeroFin (k := K) (D.sec (D.yOf x)) \ Finset.univ.image (liftTuple (D.yOf x)) = D.nuSet x := rfl
  rw [e, card_nuSet] at h
  rw [nrm]
  exact h

theorem exists_nrm (w : Places.Rfin K F) : ∃ r : D.Rg, ∀ x, x r = D.nuPt x (normS K w) :=
  ⟨D.nrm w, fun x => by rw [apply_nrm, nuPt_normS]⟩

/-- **The negation map** `ν : D(good) → Sym^g`, `A ↦ Z(s_A) - A`. -/
noncomputable def nuMap : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] D.Rg :=
  liftPts D.nuPt D.exists_nrm

theorem comp_nuMap (x : D.Rg →ₐ[K] K) : x.comp D.nuMap = D.nuPt x :=
  comp_liftPts _ _ x

end NuData

end Nu

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Step =====
section

/-!
# S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`

* `nuF D y = Z(sec y) \ A` for a point `y = A` of `Sym^d` (the negation `ν` as a finset); `card_nuF`,
  `zeroFin_eq_union`, `disjoint_nuF`.
* `swap_step`: if `A = P ⊔ Q` and `A' = P ∪ ν(A)` then `ν'(A') = Q` (any choice data with the same `Hn`): every law
  identity `r(a, m(a,b)) = b`, `m(a, r(a,c)) = c`, ... is two applications of it.
* `nuStep D ψ : Sym^g → T[1/ψ(good)]` for any `ψ : Sym^d → T` (`T` reduced f.g.): the composite of `ψ` and `ν`;
  `ptSet_nuStep` (its points are `nuF D (ψ x)`), `baseAway`, `exists_baseAway`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Away

variable {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T]

end Away

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ}

variable {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

end NuData

section Step

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

namespace NuData

variable {d : ℕ}

/-- **Step map** `Sym^g → T[1/ψ(good)]`: the composite `ν ∘ ψ` on the open where `ψ` lands in `D(good)`. -/
noncomputable def nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (ψ D.good) :=
  (Localization.awayMapₐ ψ D.good).comp D.nuMap

open Classical in
theorem ptSet_nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) :
    ptSet (x.comp (D.nuStep ψ)) = D.nuF ((baseAway (ψ D.good) x).comp ψ) := by
  rw [nuStep, ← AlgHom.comp_assoc, comp_nuMap, ptSet_nuPt, nuSet_eq_nuF, yOf_awayMap]

end NuData

end Step

end RamanujanPetersson.JacLaw


end


