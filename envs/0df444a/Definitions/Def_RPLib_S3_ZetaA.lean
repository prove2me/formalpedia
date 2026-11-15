-- Prove2me | Definitions.Def_RPLib_S3_ZetaA
-- name    : RPLib_S3_ZetaA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:36.602965+00:00
-- url     : https://prove2.me/theorems/86bf3991-c079-4d26-a4c3-c3b1f0873d54
-- title:
--   Weight-two Ramanujan-Petersson library: effective divisors and the Newton identity
-- statement:
--   Effective divisors and the Newton identity.
--
--   `A_n` = number of effective divisors of degree `n` (finite: they are supported on the places of degree `≤ n`).
--   Newton identity (the coefficientwise form of `t Z'(t) = Z(t) · Σ_m N_m t^m`):
--   `n A_n = Σ_{m=1}^n N_m A_{n-m}`, proved by the bijection `D ↦ D - k P` (no infinite products).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_PlacesC

/-!
# S3-ZetaSB, O5 part A: effective divisors and the Newton identity

`A_n` = number of effective divisors of degree `n` (finite: they are supported on the places of degree `≤ n`).
Newton identity (the coefficientwise form of `t Z'(t) = Z(t) · Σ_m N_m t^m`):
`n A_n = Σ_{m=1}^n N_m A_{n-m}`, proved by the bijection `D ↦ D - k P` (no infinite products).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.ZetaSB

open Places

section Eff

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem finite_place_deg_le (n : ℕ) : {P : Place Fq F | P.deg ≤ n}.Finite :=
  ((Finset.range (n + 1)).finite_toSet.biUnion fun d _ => finite_place_deg_eq Fq F d).subset fun _ hP =>
    Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hP))) rfl

/-- The places of degree `≤ n`. -/
noncomputable def lowPlaces (n : ℕ) : Finset (Place Fq F) := (finite_place_deg_le Fq F n).toFinset

/-- The effective divisors of degree `n`. -/
noncomputable def effDivs (n : ℕ) : Finset (Divisor Fq F) :=
  ((lowPlaces Fq F n).finsupp fun _ => Finset.Icc (0 : ℤ) n).filter fun D => Divisor.deg D = n

/-- `A_n`: the number of effective divisors of degree `n`. -/
noncomputable def numEff (n : ℕ) : ℕ := (effDivs Fq F n).card

variable {Fq F}

theorem mem_lowPlaces {n : ℕ} {P : Place Fq F} : P ∈ lowPlaces Fq F n ↔ P.deg ≤ n := by
  rw [lowPlaces, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem deg_eq_sum_of_subset (D : Divisor Fq F) {s : Finset (Place Fq F)} (hs : D.support ⊆ s) :
    Divisor.deg D = ∑ P ∈ s, D P * (P.deg : ℤ) :=
  Finsupp.sum_of_support_subset D hs (fun P n => n * (P.deg : ℤ)) (fun _ _ => zero_mul _)

theorem nonneg_apply {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) : 0 ≤ D P := by
  simpa using Finsupp.le_def.mp hD P

theorem term_le_deg {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) :
    D P * (P.deg : ℤ) ≤ Divisor.deg D := by
  classical
  rw [deg_eq_sum_of_subset D (Finset.subset_insert P D.support)]
  exact Finset.single_le_sum (f := fun Q => D Q * (Q.deg : ℤ))
    (fun Q _ => mul_nonneg (nonneg_apply hD Q) (Nat.cast_nonneg _)) (Finset.mem_insert_self P _)

theorem apply_le_deg {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) : D P ≤ Divisor.deg D := by
  have h1 := term_le_deg hD P
  have h2 : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  nlinarith [nonneg_apply hD P]

theorem deg_le_of_apply_ne {D : Divisor Fq F} (hD : 0 ≤ D) {P : Place Fq F} (hP : D P ≠ 0) :
    (P.deg : ℤ) ≤ Divisor.deg D := by
  have h1 := term_le_deg hD P
  have h2 : 1 ≤ D P := by have := nonneg_apply hD P; omega
  nlinarith [Nat.cast_nonneg (α := ℤ) P.deg]

theorem mem_effDivs {n : ℕ} {D : Divisor Fq F} : D ∈ effDivs Fq F n ↔ 0 ≤ D ∧ Divisor.deg D = n := by
  classical
  rw [effDivs, Finset.mem_filter, Finset.mem_finsupp_iff]
  constructor
  · rintro ⟨⟨hsupp, hval⟩, hdeg⟩
    refine ⟨Finsupp.le_def.mpr fun P => ?_, hdeg⟩
    by_cases hP : P ∈ lowPlaces Fq F n
    · simpa using (Finset.mem_Icc.mp (hval P hP)).1
    · have : P ∉ D.support := fun h => hP (hsupp h)
      simp [Finsupp.notMem_support_iff.mp this]
  · rintro ⟨hD, hdeg⟩
    refine ⟨⟨fun P hP => ?_, fun P _ => ?_⟩, hdeg⟩
    · rw [mem_lowPlaces]
      have := deg_le_of_apply_ne hD (Finsupp.mem_support_iff.mp hP)
      rw [hdeg] at this
      exact_mod_cast this
    · rw [Finset.mem_Icc, ← hdeg]
      exact ⟨nonneg_apply hD P, apply_le_deg hD P⟩

theorem support_subset_lowPlaces {n : ℕ} {D : Divisor Fq F} (hD : D ∈ effDivs Fq F n) :
    D.support ⊆ lowPlaces Fq F n := by
  classical
  rw [effDivs, Finset.mem_filter, Finset.mem_finsupp_iff] at hD
  exact hD.1.1

/-- `#{D ∈ Eff_n : k ≤ D(P)} = A_{n - k deg P}` (and `0` if `k deg P > n`). -/
theorem card_filter_le_eff (n k : ℕ) (P : Place Fq F) :
    ((effDivs Fq F n).filter fun D => (k : ℤ) ≤ D P).card =
      if k * P.deg ≤ n then numEff Fq F (n - k * P.deg) else 0 := by
  classical
  split_ifs with hk
  · rw [numEff]
    refine Finset.card_nbij' (fun D => D - Finsupp.single P (k : ℤ)) (fun D => D + Finsupp.single P (k : ℤ))
      ?_ ?_ ?_ ?_
    · intro D hD
      rw [Finset.mem_coe, Finset.mem_filter, mem_effDivs] at hD
      rw [Finset.mem_coe, mem_effDivs]
      refine ⟨Finsupp.le_def.mpr fun Q => ?_, ?_⟩
      · rw [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
        have := nonneg_apply hD.1.1 Q
        split_ifs with hQ
        · subst hQ; simp only [Finsupp.coe_zero, Pi.zero_apply]; linarith [hD.2]
        · simpa using this
      · rw [Divisor.deg_sub, Divisor.deg_single, hD.1.2]
        push_cast [Nat.cast_sub hk]; ring
    · intro D hD
      rw [Finset.mem_coe, mem_effDivs] at hD
      rw [Finset.mem_coe, Finset.mem_filter, mem_effDivs]
      refine ⟨⟨add_nonneg hD.1 (Finsupp.single_nonneg.mpr (Nat.cast_nonneg k)), ?_⟩, ?_⟩
      · rw [Divisor.deg_add, Divisor.deg_single, hD.2]
        push_cast [Nat.cast_sub hk]; ring
      · rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
        linarith [nonneg_apply hD.1 P]
    · intro D _; simp
    · intro D _; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro D hD hkD
    rw [mem_effDivs] at hD
    have h1 := term_le_deg hD.1 P
    rw [hD.2] at h1
    have : (k : ℤ) * P.deg ≤ n := le_trans (mul_le_mul_of_nonneg_right hkD (Nat.cast_nonneg _)) h1
    exact hk (by exact_mod_cast this)

/-- For `D ∈ Eff_n`: `n = Σ_{P, deg P ≤ n} Σ_{k=1}^n [k ≤ D(P)] deg P`. -/
theorem eq_sum_of_mem_effDivs {n : ℕ} {D : Divisor Fq F} (hD : D ∈ effDivs Fq F n) :
    n = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n, if (k : ℤ) ≤ D P then P.deg else 0 := by
  classical
  have hsupp := support_subset_lowPlaces hD
  rw [mem_effDivs] at hD
  have hin : ∀ P, ∑ k ∈ Finset.Icc 1 n, (if (k : ℤ) ≤ D P then P.deg else 0) = (D P).toNat * P.deg := by
    intro P
    have h0 := nonneg_apply hD.1 P
    have hle : D P ≤ n := hD.2 ▸ apply_le_deg hD.1 P
    set a := (D P).toNat with ha
    have ha' : (a : ℤ) = D P := Int.toNat_of_nonneg h0
    have han : a ≤ n := by exact_mod_cast (ha' ▸ hle)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have : (Finset.Icc 1 n).filter (fun k : ℕ => (k : ℤ) ≤ D P) = Finset.Icc 1 a := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, ← ha']
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by exact_mod_cast h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans han⟩, by exact_mod_cast h2⟩
    rw [this, Nat.card_Icc]; omega
  rw [Finset.sum_congr rfl fun P _ => hin P]
  have key : ((∑ P ∈ lowPlaces Fq F n, (D P).toNat * P.deg : ℕ) : ℤ) = Divisor.deg D := by
    rw [deg_eq_sum_of_subset D hsupp]
    push_cast
    exact Finset.sum_congr rfl fun P _ => by rw [Int.toNat_of_nonneg (nonneg_apply hD.1 P)]
  have := hD.2
  rw [← key] at this
  exact_mod_cast this.symm

theorem sum_reindex_mul (n d : ℕ) (hd : 0 < d) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (if k * d ≤ n then f (k * d) else 0) =
      ∑ m ∈ Finset.Icc 1 n, (if d ∣ m then f m else 0) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have himg : (Finset.Icc 1 n).filter (fun m => d ∣ m) =
      ((Finset.Icc 1 n).filter fun k => k * d ≤ n).image (· * d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, c, rfl⟩
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; omega
        · exact h
      exact ⟨c, ⟨⟨hc, le_trans (Nat.le_mul_of_pos_left c hd) h2⟩, by rw [mul_comm]; exact h2⟩,
        mul_comm c d⟩
    · rintro ⟨k, ⟨⟨h1, _⟩, h3⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), h3⟩, Dvd.intro_left k rfl⟩
  rw [himg, Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hd h]

theorem numPoints_eq_sum_low {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    numPoints Fq F m = ∑ P ∈ (lowPlaces Fq F n).filter (fun P => P.deg ∣ m), P.deg := by
  classical
  have hm : m ≠ 0 := by omega
  rw [numPoints, dif_neg hm]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, mem_lowPlaces]
  exact ⟨fun h => ⟨(Nat.le_of_dvd (by omega) h).trans hmn, h⟩, fun h => h.2⟩

/-- **Newton identity** `n A_n = Σ_{m=1}^n N_m A_{n-m}`. -/
theorem newton (n : ℕ) :
    n * numEff Fq F n = ∑ m ∈ Finset.Icc 1 n, numPoints Fq F m * numEff Fq F (n - m) := by
  classical
  calc n * numEff Fq F n = ∑ D ∈ effDivs Fq F n, n := by rw [numEff, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ D ∈ effDivs Fq F n, ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          (if (k : ℤ) ≤ D P then P.deg else 0) :=
        Finset.sum_congr rfl fun D hD => eq_sum_of_mem_effDivs hD
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          P.deg * ((effDivs Fq F n).filter fun D => (k : ℤ) ≤ D P).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          (if k * P.deg ≤ n then P.deg * numEff Fq F (n - k * P.deg) else 0) := by
        refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun k _ => ?_
        rw [card_filter_le_eff]
        split_ifs <;> simp
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ m ∈ Finset.Icc 1 n,
          (if P.deg ∣ m then P.deg * numEff Fq F (n - m) else 0) :=
        Finset.sum_congr rfl fun P _ =>
          sum_reindex_mul n P.deg P.deg_pos (fun m => P.deg * numEff Fq F (n - m))
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ P ∈ lowPlaces Fq F n,
          (if P.deg ∣ m then P.deg * numEff Fq F (n - m) else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m hm => by
        rw [Finset.mem_Icc] at hm
        rw [← Finset.sum_filter, ← Finset.sum_mul, numPoints_eq_sum_low hm.1 hm.2]

theorem numEff_zero : numEff Fq F 0 = 1 := by
  classical
  rw [numEff, Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_effDivs.mpr ⟨le_rfl, by simp [Divisor.deg]⟩,
    fun D hD => ?_⟩⟩
  rw [mem_effDivs] at hD
  ext P
  have h1 := apply_le_deg hD.1 P
  have h2 := nonneg_apply hD.1 P
  rw [hD.2] at h1
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  push_cast at h1
  omega

end Eff

end RamanujanPetersson.ZetaSB


