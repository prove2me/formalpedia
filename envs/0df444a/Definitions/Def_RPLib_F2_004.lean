-- Prove2me | Definitions.Def_RPLib_F2_004
-- name    : RPLib_F2_004
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T03:26:12.556365+00:00
-- url     : https://prove2.me/theorems/473bd229-e77f-416b-a9fc-b859122db4d5
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 004 of 70
-- statement:
--   File 004 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
--   * `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
--   * `S4.Def_RP_PicDescent_D4c`: S4-PicDescent, part D4c: conorm of divisors and the Galois action
--   * `S4.Def_RP_PicDescent_H90`: S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields
--   * `S4.Def_RP_PicDescent_D5`: S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension
--   * `S4.Def_RP_PicDescent_E1`: S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools
--   * `S4.Def_RP_PicDescent_E2`: S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius
--   * `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
--   * `S4.Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
--   * `S4.Def_RP_Kummer_InfMain`: S4-Kummer K5c: parabolic Kummer classes (main theorem)
--   * `S4.Def_RP_Kummer_PicA`: S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`
--   * `S4.Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--   * `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--   * `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
--   * `S4.Def_RP_CP4a_Lift`: S4-CP4a, part f4: inertia lifting (`BdryLift`) holds
--   * `S4.Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
--   * `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_003

/-!
# Ramanujan-Petersson curve library (flat edition), file 004 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
* `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
* `S4.Def_RP_PicDescent_D4c`: S4-PicDescent, part D4c: conorm of divisors and the Galois action
* `S4.Def_RP_PicDescent_H90`: S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields
* `S4.Def_RP_PicDescent_D5`: S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension
* `S4.Def_RP_PicDescent_E1`: S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools
* `S4.Def_RP_PicDescent_E2`: S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius
* `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
* `S4.Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
* `S4.Def_RP_Kummer_InfMain`: S4-Kummer K5c: parabolic Kummer classes (main theorem)
* `S4.Def_RP_Kummer_PicA`: S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`
* `S4.Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
* `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
* `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
* `S4.Def_RP_CP4a_Lift`: S4-CP4a, part f4: inertia lifting (`BdryLift`) holds
* `S4.Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
* `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreA_ValZ =====
section

/-!
# S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`

`K` an algebraically closed ultrametric normed field of characteristic `0` with `‖l‖ < 1` (e.g. `PadicAlgCl l`).
`c ⊆ ℂ` a multiset with `Π_i c_i = Q` (`l ∤ Q`) and `Π_i (1 - c_i X)` the image of an integer polynomial `L`.
Let `P := reflect (#c) L`, so `P ↦ Π_i (X - c_i)` in `ℂ[X]`; `P` is monic over `ℤ`. Its roots `β_i` in `K` satisfy
`‖β_i‖ = 1`, `‖β_i ^ M - 1‖ < 1` for some `M ≥ 1` (pigeonhole on `X ^ k %ₘ P` mod `l`), and
`Π_i (1 - β_i ^ N) = Res(P, 1 - X ^ N) = Π_i (1 - c_i ^ N)` (resultant transfer).
* **`valuation_growth`**: for `h : ℕ → ℕ` with `h N = Π_i (1 - c_i ^ N) ≠ 0` (`N ≥ 1`):
  `v_l(h N) ≤ C₀ + #c v_l(N)`, and `v_l(h (d l^j)) = C' + #c j` for all `d` divisible by some `d0 ≥ 1`.
* `valuation_growth_padic`: the same with `K = PadicAlgCl l` and `Q = q ^ g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CoreA

open Polynomial

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_multiset_prod_map {ι : Type*} (s : Multiset ι) (f : ι → K) :
    ‖(s.map f).prod‖ = (s.map fun i => ‖f i‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

theorem norm_eq_one_of_prod {B : Multiset K} (h1 : ∀ β ∈ B, ‖β‖ ≤ 1) (hp : ‖B.prod‖ = 1) :
    ∀ β ∈ B, ‖β‖ = 1 := by
  intro β hβ
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hβ
  rw [Multiset.prod_cons, norm_mul] at hp
  have ht : ‖t.prod‖ ≤ 1 := by
    have h2 := norm_multiset_prod_map t id
    rw [Multiset.map_id] at h2
    rw [h2]
    calc (t.map fun i => ‖id i‖).prod ≤ (t.map fun _ => (1 : ℝ)).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun i _ => norm_nonneg _)
            (fun i hi => h1 i (Multiset.mem_cons.mpr (Or.inr hi)))
      _ = 1 := by simp
  exact le_antisymm (h1 β hβ) (by nlinarith [mul_nonneg (norm_nonneg β) (sub_nonneg.mpr ht)])

end Ultra

section Res

theorem prod_roots_one_sub_pow {F : Type*} [Field F] {P : ℤ[X]} (hP : P.Monic)
    (hs : (P.map (Int.castRingHom F)).Splits) (N : ℕ) :
    ((P.map (Int.castRingHom F)).roots.map fun β => 1 - β ^ N).prod =
      ((resultant P (1 - X ^ N) P.natDegree N : ℤ) : F) := by
  have hdeg : ((1 : ℤ[X]) - X ^ N).natDegree ≤ N := (natDegree_sub_le _ _).trans (by simp)
  have h := resultant_eq_prod_eval (P.map (Int.castRingHom F)) (((1 : ℤ[X]) - X ^ N).map (Int.castRingHom F))
    N (natDegree_map_le.trans hdeg) hs
  rw [hP.natDegree_map, resultant_map_map, (hP.map _).leadingCoeff, one_pow, one_mul, eq_intCast] at h
  rw [h]
  congr 1
  refine Multiset.map_congr rfl (fun β _ => ?_)
  simp

theorem reflect_one_sub_C_mul_X {R : Type*} [CommRing R] (a : R) : reflect 1 (1 - C a * X) = X - C a := by
  rw [reflect_sub, show (1 : R[X]) = C 1 * X ^ 0 by simp, show C a * X = C a * X ^ 1 by simp,
    reflect_C_mul_X_pow, reflect_C_mul_X_pow, revAt_le (by norm_num), revAt_le (by norm_num)]
  simp

theorem reflect_prod_one_sub {R : Type*} [CommRing R] (c : Multiset R) :
    reflect (Multiset.card c) (c.map fun r => 1 - C r * X).prod = (c.map fun r => X - C r).prod ∧
      (c.map fun r => 1 - C r * X).prod.natDegree ≤ Multiset.card c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
    have h1 : (1 - C a * X : R[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine ⟨?_, ?_⟩
    · rw [show Multiset.card c + 1 = 1 + Multiset.card c by omega, reflect_mul _ _ h1 ih.2, ih.1,
        reflect_one_sub_C_mul_X]
    · have h2 := ih.2
      exact natDegree_mul_le.trans (by omega)

end Res

section Main

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] [CharZero K]

/-- **V2.** Valuation bounds and exact growth for `h N = Π_i (1 - c_i ^ N)`. -/
theorem valuation_growth {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {Q : ℕ} (hQ : ¬ l ∣ Q)
    (c : Multiset ℂ) (hprod : c.prod = (Q : ℂ)) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - C r * X).prod)
    (h : ℕ → ℕ) (hh : ∀ N, 0 < N → (h N : ℂ) = (c.map fun z => 1 - z ^ N).prod)
    (hh0 : ∀ N, 0 < N → h N ≠ 0) :
    (∃ C₀ : ℕ, ∀ N, 0 < N → padicValNat l (h N) ≤ C₀ + Multiset.card c * padicValNat l N) ∧
    (∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d →
      ∃ C', ∀ j, padicValNat l (h (d * l ^ j)) = C' + Multiset.card c * j) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : ℤ[X], P = reflect (Multiset.card c) L := ⟨_, rfl⟩
  have hPC : P.map (Int.castRingHom ℂ) = (c.map fun r => X - C r).prod := by
    rw [hPdef, ← reflect_map, hL, (reflect_prod_one_sub c).1]
  have hinjC : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hmonC : (P.map (Int.castRingHom ℂ)).Monic :=
    hPC ▸ monic_multiset_prod_of_monic _ _ (fun r _ => monic_X_sub_C r)
  have hP : P.Monic := by
    have h1 := (leadingCoeff_map_of_injective hinjC P).symm.trans hmonC.leadingCoeff
    exact hinjC (h1.trans (map_one _).symm)
  have hdeg : P.natDegree = Multiset.card c := by
    rw [← hP.natDegree_map (Int.castRingHom ℂ), hPC, natDegree_multiset_prod_X_sub_C_eq_card]
  have hrootsC : (P.map (Int.castRingHom ℂ)).roots = c := by rw [hPC, roots_multiset_prod_X_sub_C]
  have hZ : ∀ N, 0 < N → ((h N : ℕ) : ℤ) = resultant P (1 - X ^ N) P.natDegree N := by
    intro N hN
    have h1 := prod_roots_one_sub_pow (F := ℂ) hP (IsAlgClosed.splits _) N
    rw [hrootsC, ← hh N hN] at h1
    apply Int.cast_injective (α := ℂ)
    rw [← h1]
    simp
  obtain ⟨B, hB⟩ : ∃ B, B = (P.map (Int.castRingHom K)).roots := ⟨_, rfl⟩
  have hsK : (P.map (Int.castRingHom K)).Splits := IsAlgClosed.splits _
  have hcardB : Multiset.card B = Multiset.card c := by
    rw [hB, ← hsK.natDegree_eq_card_roots, hP.natDegree_map, hdeg]
  have htrans : ∀ N, 0 < N → (B.map fun β => 1 - β ^ N).prod = (h N : K) := by
    intro N hN
    rw [hB, prod_roots_one_sub_pow hP hsK N, ← hZ N hN]
    simp
  have haeval : ∀ β ∈ B, aeval β P = 0 := by
    intro β hβ
    rw [hB] at hβ
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
    exact (mem_roots (hP.map _).ne_zero).mp hβ
  have hC0 : ((P.eval 0 : ℤ) : ℂ) = (-1) ^ Multiset.card c * (Q : ℂ) := by
    have h1 := (IsAlgClosed.splits (P.map (Int.castRingHom ℂ))).eval_eq_prod_roots_of_monic (hP.map _) 0
    rw [eval_zero_map, hrootsC, eq_intCast] at h1
    rw [h1, ← hprod]
    simp
  have hP0 : P.eval 0 = (-1) ^ Multiset.card c * (Q : ℤ) :=
    Int.cast_injective (α := ℂ) (hC0.trans (by simp))
  have hBprod : B.prod = (Q : K) := by
    have h1 := hsK.eval_eq_prod_roots_of_monic (hP.map _) 0
    rw [eval_zero_map, eq_intCast, hP0, ← hB] at h1
    simp only [zero_sub, Multiset.prod_map_neg, hcardB, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast] at h1
    exact (mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h1).symm
  have hle1 : ∀ β ∈ B, ‖β‖ ≤ 1 := fun β hβ => norm_le_one_of_monic hP (haeval β hβ)
  have hQ1 : ‖(Q : K)‖ = 1 := norm_natCast_eq_one_of_not_dvd hl hl1 hQ
  have hnorm1 : ∀ β ∈ B, ‖β‖ = 1 := norm_eq_one_of_prod hle1 (by rw [hBprod, hQ1])
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpow : ∀ β ∈ B, ∀ N, 0 < N → β ^ N ≠ 1 := by
    intro β hβ N hN hβN
    have h1 := htrans N hN
    rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨β, hβ, by rw [hβN, sub_self]⟩)] at h1
    exact Nat.cast_ne_zero.mpr (hh0 N hN) h1.symm
  have hdata : ∀ β : K, ∃ d0 : ℕ, ∃ r : ℝ, β ∈ B → (0 < d0 ∧ 0 < r ∧
      (∀ n : ℕ, 0 < n → ‖β ^ (d0 * n) - 1‖ = r * ‖(n : K)‖) ∧
      (∀ N : ℕ, 0 < N → r * ‖(N : K)‖ ≤ ‖β ^ N - 1‖)) := by
    intro β
    by_cases hβ : β ∈ B
    · obtain ⟨M, hM, hM1⟩ := exists_norm_pow_sub_one_lt hl hl1 hP (haeval β hβ) (hnorm1 β hβ)
      obtain ⟨d0, hd0, r, hr, h1, h2⟩ := exists_norm_pow_sub_one_eq hl hl0 hl1 (hpow β hβ) hM hM1
      exact ⟨d0, r, fun _ => ⟨hd0, hr, h1, h2⟩⟩
    · exact ⟨1, 1, fun h' => absurd h' hβ⟩
  choose d0 r hdr using hdata
  have hρ0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hnormh : ∀ N, 0 < N →
      ‖(l : K)‖ ^ padicValNat l (h N) = (B.map fun β => ‖β ^ N - 1‖).prod := by
    intro N hN
    rw [← norm_natCast_eq_pow_padicValNat hl hl1 (hh0 N hN), ← htrans N hN, norm_multiset_prod_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl (fun β _ => norm_sub_rev _ _))
  refine ⟨?_, ?_⟩
  · have hR : 0 < (B.map r).prod := Multiset.prod_pos (fun a ha => by
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp ha
      exact (hdr β hβ).2.1)
    obtain ⟨C₀, hC₀⟩ := exists_pow_lt_of_lt_one hR hl1
    refine ⟨C₀, fun N hN => ?_⟩
    have hlow : (B.map r).prod * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c ≤
        ‖(l : K)‖ ^ padicValNat l (h N) := by
      rw [hnormh N hN, ← norm_natCast_eq_pow_padicValNat hl hl1 hN.ne', ← hcardB]
      calc (B.map r).prod * ‖(N : K)‖ ^ Multiset.card B
          = (B.map fun β => r β * ‖(N : K)‖).prod := by
            rw [Multiset.prod_map_mul]
            simp
        _ ≤ (B.map fun β => ‖β ^ N - 1‖).prod :=
            Multiset.prod_map_le_prod_map₀ _ _
              (fun β hβ => mul_nonneg (hdr β hβ).2.1.le (norm_nonneg _))
              (fun β hβ => (hdr β hβ).2.2.2 N hN)
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖(l : K)‖ ^ padicValNat l (h N) ≤
        ‖(l : K)‖ ^ (C₀ + Multiset.card c * padicValNat l N) :=
      pow_le_pow_of_le_one hρ0.le hl1.le hcon.le
    rw [pow_add, pow_mul'] at h1
    have h2 : ‖(l : K)‖ ^ C₀ * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c <
        (B.map r).prod * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c :=
      mul_lt_mul_of_pos_right hC₀ (pow_pos (pow_pos hρ0 _) _)
    linarith
  · refine ⟨(B.map d0).prod, Multiset.prod_pos (fun a ha => by
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp ha
      exact (hdr β hβ).1), fun d hd hdvd => ?_⟩
    have hdβ : ∀ β ∈ B, d0 β ∣ d := fun β hβ =>
      (Multiset.dvd_prod (Multiset.mem_map_of_mem d0 hβ)).trans hdvd
    have hkey : ∀ j : ℕ, ‖(l : K)‖ ^ padicValNat l (h (d * l ^ j)) =
        (B.map fun β => r β * ‖((d / d0 β : ℕ) : K)‖).prod * (‖(l : K)‖ ^ j) ^ Multiset.card c := by
      intro j
      have hpos : 0 < d * l ^ j := Nat.mul_pos hd (pow_pos hl.pos j)
      rw [hnormh _ hpos, ← hcardB]
      calc (B.map fun β => ‖β ^ (d * l ^ j) - 1‖).prod
          = (B.map fun β => r β * ‖((d / d0 β : ℕ) : K)‖ * ‖(l : K)‖ ^ j).prod := by
            refine congrArg Multiset.prod (Multiset.map_congr rfl (fun β hβ => ?_))
            have hn : 0 < d / d0 β * l ^ j :=
              Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hd (hdβ β hβ)) (hdr β hβ).1) (pow_pos hl.pos j)
            have he : d * l ^ j = d0 β * (d / d0 β * l ^ j) := by
              rw [← mul_assoc, Nat.mul_div_cancel' (hdβ β hβ)]
            rw [he, (hdr β hβ).2.2.1 _ hn, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, mul_assoc]
        _ = _ := by
            rw [Multiset.prod_map_mul]
            simp
    refine ⟨padicValNat l (h d), fun j => ?_⟩
    have h0 := hkey 0
    simp only [pow_zero, mul_one, one_pow] at h0
    have hj := hkey j
    rw [← h0, ← pow_mul, ← pow_add] at hj
    rw [pow_right_injective₀ hρ0 hl1.ne hj, mul_comm]

end Main

/-- `‖l‖ < 1` in `PadicAlgCl l`. -/
theorem norm_prime_padicAlgCl_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have h2 : ((1 / (l : NNReal) : NNReal) : ℝ) = 1 / (l : ℝ) := by simp
  rw [h2, div_lt_one (by linarith)]
  exact h1

/-- **V2** over `PadicAlgCl l`, with `Π_i c_i = q ^ g` and `l ∤ q`. -/
theorem valuation_growth_padic {l : ℕ} [hl : Fact l.Prime] {q : ℕ} (hq : ¬ l ∣ q) (g : ℕ)
    (c : Multiset ℂ) (hprod : c.prod = (q : ℂ) ^ g) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - C r * X).prod)
    (h : ℕ → ℕ) (hh : ∀ N, 0 < N → (h N : ℂ) = (c.map fun z => 1 - z ^ N).prod)
    (hh0 : ∀ N, 0 < N → h N ≠ 0) :
    (∃ C₀ : ℕ, ∀ N, 0 < N → padicValNat l (h N) ≤ C₀ + Multiset.card c * padicValNat l N) ∧
    (∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d →
      ∃ C', ∀ j, padicValNat l (h (d * l ^ j)) = C' + Multiset.card c * j) :=
  valuation_growth (K := PadicAlgCl l) hl.out (norm_prime_padicAlgCl_lt_one l) (Q := q ^ g)
    (fun hd => hq (hl.out.dvd_of_dvd_pow hd)) c (by rw [hprod, Nat.cast_pow]) L hL h hh hh0

end RamanujanPetersson.CoreA


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

theorem eval_one_Lpoly (c : Multiset ℂ) (n : ℕ) :
    (Lpoly c n).eval 1 = (c.map fun z => 1 - z ^ n).prod := by
  rw [Lpoly, eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun z _ => by simp

section ClassNumber

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]

theorem card_Lc_fintype (n : ℕ) [NeZero n] :
    Fintype.card (Lc Fq Ω n) = Fintype.card Fq ^ n := by
  rw [← Nat.card_eq_fintype_card, card_Lc Fq Ω (NeZero.ne n)]

/-- `N_k(F_n) = N_{nk}(F)`. -/
theorem numPoints_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] {k : ℕ} (hk0 : k ≠ 0) :
    Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) k = Places.numPoints Fq F (n * k) := by
  rw [numPoints_constExt (isConstExt_Fc Fq F Ω hk n) hk0, finrank_Lc Fq Ω (NeZero.ne n)]

variable {Fq F}

/-- The point counts of `F_n` in terms of a multiset `c` describing those of `F`. -/
theorem numPoints_Fc_formula (hk : Places.constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (n : ℕ) [NeZero n] (m : ℕ) (hm : 1 ≤ m) :
    (Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) m : ℂ) =
      1 + (Fintype.card (Lc Fq Ω n) : ℂ) ^ m - ((c.map (· ^ n)).map (· ^ m)).sum := by
  have e1 : c.map (· ^ (n * m)) = (c.map (· ^ n)).map (· ^ m) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun z _ => pow_mul z n m
  rw [numPoints_Fc Fq F Ω hk n (by omega),
    hc (n * m) (Nat.one_le_iff_ne_zero.2 (mul_ne_zero (NeZero.ne n) (by omega))),
    card_Lc_fintype Fq Ω n, e1]
  push_cast
  ring

end ClassNumber

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D4c =====
section

/-!
# S4-PicDescent, part D4c: conorm of divisors and the Galois action

For `h : RR.IsConstExt Fq F L F' c`:
* `conorm h : Divisor Fq F →+ Divisor L F'`, `conorm h D P' = D (P' ∩ F)`; `conorm_div` (`ι (div f) = div f'`),
  `deg_conorm` (`deg ι D = deg D`), `conorm_injective`.
* `actD h τ : Divisor L F' ≃+ Divisor L F'`, `(actD τ D) P' = D (τ⁻¹ P')`; `div_gal` (`div (gal τ f) = actD τ (div f)`),
  `actD_conorm` (conorms are invariant), `exists_conorm_eq` (invariant divisors are conorms).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Conorm

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

/-- **Conorm** `ι D (P') = D (P' ∩ F)`. -/
noncomputable def conorm : Divisor Fq F →+ Divisor L F' where
  toFun D := by
    classical
    exact Finsupp.onFinset (D.support.biUnion (fibre h)) (fun P' => D (contract h P')) (fun P' hP' =>
      Finset.mem_biUnion.2 ⟨contract h P', Finsupp.mem_support_iff.2 hP', (mem_fibre h _ _).2 rfl⟩)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

theorem conorm_apply (D : Divisor Fq F) (P' : Place L F') : conorm h D P' = D (contract h P') := by
  simp [conorm]

/-- **`ι (div f) = div f'`**. -/
theorem conorm_div (f : F) : conorm h (div f) = div (algebraMap F F' f) := by
  ext P'
  rw [conorm_apply, div_apply, div_apply, ord_contract]

theorem conorm_single (P : Place Fq F) (n : ℤ) :
    conorm h (Finsupp.single P n) = ∑ P' ∈ fibre h P, Finsupp.single P' n := by
  classical
  ext P'
  rw [conorm_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hc : contract h P' = P
  · rw [if_pos ((mem_fibre h P P').2 hc), if_pos hc.symm]
  · rw [if_neg (fun hm => hc ((mem_fibre h P P').1 hm)), if_neg (Ne.symm hc)]

/-- **`deg ι D = deg D`**. -/
theorem deg_conorm (D : Divisor Fq F) : Divisor.deg (conorm h D) = Divisor.deg D := by
  induction D using Finsupp.induction with
  | zero => simp [Divisor.deg]
  | single_add P n D _ _ ih =>
    rw [map_add, Divisor.deg_add, Divisor.deg_add, ih, conorm_single, Divisor.deg_single,
      ← sum_deg_fibre h P]
    have e := map_sum (degHom L F') (fun P' => Finsupp.single P' n) (fibre h P)
    simp only [degHom, AddMonoidHom.mk'_apply, Divisor.deg_single] at e
    rw [e, Nat.cast_sum, Finset.mul_sum]

/-- `Gal(L/Fq)` acting on divisors of `F'`. -/
noncomputable def actD (τ : L ≃ₐ[Fq] L) : Divisor L F' ≃+ Divisor L F' := Finsupp.domCongr (plE h τ).symm

theorem actD_apply (τ : L ≃ₐ[Fq] L) (D : Divisor L F') (P' : Place L F') : actD h τ D P' = D (plE h τ P') := by
  simp [actD]

/-- **`div (gal τ f) = actD τ (div f)`**. -/
theorem div_gal (τ : L ≃ₐ[Fq] L) (f : F') : div (gal h.linearIndependent h.span τ f) = actD h τ (div f) := by
  ext P'
  rw [actD_apply, div_apply, div_apply, ord_plE]

theorem actD_conorm (τ : L ≃ₐ[Fq] L) (D : Divisor Fq F) : actD h τ (conorm h D) = conorm h D := by
  ext P'
  rw [actD_apply, conorm_apply, conorm_apply, contract_plE]

/-- **Invariant divisors are conorms.** -/
theorem exists_conorm_eq (D' : Divisor L F') (hD : ∀ τ, actD h τ D' = D') : ∃ D, conorm h D = D' := by
  classical
  choose lift hlift using exists_contract_eq h
  refine ⟨Finsupp.onFinset (D'.support.image (contract h)) (fun P => D' (lift P)) (fun P hP =>
    Finset.mem_image.2 ⟨lift P, Finsupp.mem_support_iff.2 hP, hlift P⟩), ?_⟩
  ext P'
  rw [conorm_apply, Finsupp.onFinset_apply]
  obtain ⟨τ, hτ⟩ := exists_plE_of_contract_eq h (lift (contract h P')) P' (hlift _)
  calc D' (lift (contract h P')) = actD h τ D' (lift (contract h P')) := by rw [hD]
    _ = D' P' := by rw [actD_apply, ← hτ]

theorem conorm_injective : Function.Injective (conorm h) := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  ext P
  obtain ⟨P', hP'⟩ := exists_contract_eq h P
  have := DFunLike.congr_fun hD P'
  rw [conorm_apply, hP'] at this
  exact this

end Conorm

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_H90 =====
section

/-!
# S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields

* `pnorm τ u i = Π_{j<i} τ^j u` (partial norms); `pnorm τ u k` is the norm when `τ` has order `k`.
* `hilbert90_cyclic`: for an automorphism `τ` of order `k > 0` of a field `E`, `pnorm τ u k = 1` implies
  `u = τ g / g` for some `g ≠ 0` (Dedekind independence of the characters `τ^i`, `i < k`).
* `pnorm_frob_eq_norm`, `exists_pnorm_frob_eq`: for finite fields `L / K` with the arithmetic Frobenius
  `x ↦ x^q`, `pnorm` is the field norm, and it is surjective onto `K` (this is `Br(F_q) = 0` in the form
  the descent needs).
-/

set_option autoImplicit false

namespace RamanujanPetersson.PicDescent

section Hilbert90

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Partial norms `Π_{j<i} τ^j u`. -/
noncomputable def pnorm (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : E := ∏ j ∈ Finset.range i, (τ ^ j) u

theorem pnorm_zero (τ : E ≃ₐ[K] E) (u : E) : pnorm τ u 0 = 1 := by
  simp [pnorm]

theorem pnorm_succ (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : pnorm τ u (i + 1) = u * τ (pnorm τ u i) := by
  unfold pnorm
  rw [Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply, map_prod, mul_comm _ u]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]

theorem pnorm_mul (τ : E ≃ₐ[K] E) (u v : E) (i : ℕ) :
    pnorm τ (u * v) i = pnorm τ u i * pnorm τ v i := by
  unfold pnorm
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => map_mul _ _ _

theorem pnorm_inv (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : pnorm τ u⁻¹ i = (pnorm τ u i)⁻¹ := by
  unfold pnorm
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun j _ => map_inv₀ _ _

theorem pnorm_ne_zero (τ : E ≃ₐ[K] E) {u : E} (hu : u ≠ 0) (i : ℕ) : pnorm τ u i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => (map_ne_zero _).2 hu

/-- The norm is fixed by `τ` when `τ ^ k = 1`. -/
theorem pnorm_fixed (τ : E ≃ₐ[K] E) {k : ℕ} (hk : τ ^ k = 1) {u : E} (hu : u ≠ 0) :
    τ (pnorm τ u k) = pnorm τ u k := by
  have h1 := pnorm_succ τ u k
  have h2 : pnorm τ u (k + 1) = u * pnorm τ u k := by
    unfold pnorm
    rw [Finset.prod_range_succ, hk, AlgEquiv.one_apply, mul_comm]
  exact mul_left_cancel₀ hu (h1.symm.trans h2)

theorem hilbert90_aux (τ : E ≃ₐ[K] E) {k : ℕ} (hk : orderOf τ = k) (hk0 : 0 < k) {u : E}
    (hu : pnorm τ u k = 1) : ∃ b : E, b ≠ 0 ∧ u * τ b = b := by
  have hinj : Function.Injective fun i : Fin k => ((τ ^ (i : ℕ) : E ≃ₐ[K] E) : E →* E) := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hk]; exact i.isLt)
      (by rw [Set.mem_Iio, hk]; exact j.isLt) h1)
  have hli := (linearIndependent_monoidHom E E).comp _ hinj
  have hex : ∃ θ : E, (∑ i : Fin k, pnorm τ u i * (τ ^ (i : ℕ)) θ) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 := Fintype.linearIndependent_iff.1 hli (fun i => pnorm τ u i) (funext fun θ => by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcon θ)
    have := h0 ⟨0, hk0⟩
    simp [pnorm] at this
  obtain ⟨θ, hθ⟩ := hex
  rw [Fin.sum_univ_eq_sum_range (fun i => pnorm τ u i * (τ ^ i) θ)] at hθ
  have hτk : τ ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one τ
  set f : ℕ → E := fun i => pnorm τ u i * (τ ^ i) θ with hf
  refine ⟨∑ i ∈ Finset.range k, f i, hθ, ?_⟩
  have hshift : ∀ i, u * τ (f i) = f (i + 1) := by
    intro i
    simp only [hf, map_mul, pnorm_succ, pow_succ', AlgEquiv.mul_apply]
    ring
  have hfk : f k = f 0 := by
    simp only [hf, hu, hτk, pnorm_zero, pow_zero, AlgEquiv.one_apply]
  rw [map_sum, Finset.mul_sum]
  simp only [hshift]
  have h1 := Finset.sum_range_succ' f k
  have h2 := Finset.sum_range_succ f k
  rw [hfk] at h2
  exact add_right_cancel (h1.symm.trans h2)

/-- **Hilbert 90 (cyclic form).** -/
theorem hilbert90_cyclic (τ : E ≃ₐ[K] E) {k : ℕ} (hk : orderOf τ = k) (hk0 : 0 < k) {u : E}
    (hu : pnorm τ u k = 1) : ∃ g : E, g ≠ 0 ∧ u = τ g / g := by
  obtain ⟨b, hb, hub⟩ := hilbert90_aux τ hk hk0 hu
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  refine ⟨b⁻¹, inv_ne_zero hb, ?_⟩
  rw [map_inv₀, inv_div_inv, eq_div_iff hτb]
  exact hub

end Hilbert90

section FiniteNorm

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Finite L] [Algebra K L]

theorem pnorm_frob_eq_norm (x : L) :
    pnorm (FiniteField.frobeniusAlgEquivOfAlgebraic K L) x (Module.finrank K L) =
      algebraMap K L (Algebra.norm K x) := by
  have := Fintype.ofFinite L
  rw [Algebra.norm_eq_prod_automorphisms,
    ← (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).prod_comp, pnorm,
    Fin.prod_univ_eq_prod_range (fun j => (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ j) x)]

theorem orderOf_frob : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L :=
  FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K L

/-- **Norms of finite fields are surjective.** -/
theorem exists_pnorm_frob_eq (a : K) :
    ∃ b : L, pnorm (FiniteField.frobeniusAlgEquivOfAlgebraic K L) b (Module.finrank K L) = algebraMap K L a := by
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective K L a
  exact ⟨b, by rw [pnorm_frob_eq_norm, hb]⟩

end FiniteNorm

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D5 =====
section

/-!
# S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension

For `h : RR.IsConstExt Fq F L F' c` with `constField Fq F = ⊥`, `π = frobL Fq L` the ARITHMETIC Frobenius `x ↦ x ^ q`
of `L / Fq` (review R4), acting on `F' = L ⊗ F` by `frobF h = π ⊗ id`, on divisors by `actD h π` and on classes by
`actPic h π`:
* `conormPic h : Pic Fq F →+ Pic L F'`, `degPic_conormPic` (degree preserved), `actPic_conormPic` (image is fixed);
* `conormPic_injective` (Hilbert 90 for `L / Fq`, `hilbert90_cyclic`);
* `exists_conormPic_eq`: every `π`-fixed class comes from `F` (Hilbert 90 for `F' / F` plus surjectivity of the norm
  `L^× → Fq^×`, i.e. `Br(Fq) = 0`, `exists_pnorm_frob_eq`);
* **`picEquiv h hk : Pic Fq F ≃+ fixedPic h`** (`Pic(F) = Pic(F')^π`) and
  **`pic0Equiv h hk : Pic0 Fq F ≃+ (fixedPic h ⊓ Pic0 L F')`** (`Pic⁰(F) = Pic⁰(F')^π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Toolkit

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem pow_apply_of_fixed (σ : E ≃ₐ[K] E) {x : E} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rw [pow_zero, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hx]

/-- Telescoping: `N_n(σ g / g) = σ^n g / g`. -/
theorem pnorm_div_self (σ : E ≃ₐ[K] E) {g : E} (hg : g ≠ 0) (n : ℕ) :
    pnorm σ (σ g / g) n = (σ ^ n) g / g := by
  induction n with
  | zero => rw [pnorm_zero, pow_zero, AlgEquiv.one_apply, div_self hg]
  | succ n ih =>
    have h1 : σ g ≠ 0 := (_root_.map_ne_zero σ).2 hg
    rw [pnorm_succ, ih, map_div₀, pow_succ', AlgEquiv.mul_apply, div_mul_div_comm,
      mul_comm (σ g) (σ ((σ ^ n) g)), mul_div_mul_right _ _ h1]

end Toolkit

section Frob

variable (Fq L : Type*) [Field Fq] [Fintype Fq] [Field L] [Fintype L] [Algebra Fq L]

/-- The arithmetic Frobenius `x ↦ x ^ q` of `L / Fq`. -/
noncomputable abbrev frobL : L ≃ₐ[Fq] L := FiniteField.frobeniusAlgEquivOfAlgebraic Fq L

theorem frobL_pow_finrank : frobL Fq L ^ Module.finrank Fq L = 1 := by
  rw [← orderOf_frob Fq L]
  exact pow_orderOf_eq_one _

theorem finrank_pos' : 0 < Module.finrank Fq L := Module.finrank_pos

variable {Fq L} in
/-- `Gal(L/Fq)` is generated by the Frobenius. -/
theorem exists_frobL_pow (τ : L ≃ₐ[Fq] L) : ∃ n : ℕ, frobL Fq L ^ n = τ := by
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow Fq L).2 τ
  exact ⟨n.1, hn⟩

end Frob

section Descent

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

/-! ### Places and divisors -/

theorem plE_plE (τ1 τ2 : L ≃ₐ[Fq] L) (P' : Place L F') : plE h τ1 (plE h τ2 P') = plE h (τ2 * τ1) P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (pullH_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ1 τ2 w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (pullH_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ1 τ2 w)

theorem plE_one (P' : Place L F') : plE h 1 P' = P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (pullH_one h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (pullH_one h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w)

theorem actD_mul (τ1 τ2 : L ≃ₐ[Fq] L) (D : Divisor L F') :
    actD h (τ1 * τ2) D = actD h τ1 (actD h τ2 D) := by
  ext P'
  simp only [actD_apply, plE_plE]

theorem actD_one (D : Divisor L F') : actD h 1 D = D := by
  ext P'
  simp only [actD_apply, plE_one]

theorem actD_pow_of_fixed (τ : L ≃ₐ[Fq] L) {D : Divisor L F'} (hD : actD h τ D = D) (n : ℕ) :
    actD h (τ ^ n) D = D := by
  induction n with
  | zero => rw [pow_zero, actD_one]
  | succ n ih => rw [pow_succ', actD_mul, ih, hD]

/-- A Frobenius-fixed divisor is fixed by all of `Gal(L/Fq)`. -/
theorem actD_forall_of_frob {D : Divisor L F'} (hD : actD h (frobL Fq L) D = D) (τ : L ≃ₐ[Fq] L) :
    actD h τ D = D := by
  obtain ⟨n, rfl⟩ := exists_frobL_pow τ
  exact actD_pow_of_fixed h _ hD n

/-! ### The Frobenius on `F'` -/

/-- The arithmetic Frobenius `π ⊗ id` on `F' = L ⊗ F`. -/
noncomputable def frobF : F' ≃ₐ[F] F' := gal h.linearIndependent h.span (frobL Fq L)

theorem frobF_apply (x : F') : frobF h x = gal h.linearIndependent h.span (frobL Fq L) x := rfl

theorem gal_pow (τ : L ≃ₐ[Fq] L) (n : ℕ) :
    gal h.linearIndependent h.span (τ ^ n) = gal h.linearIndependent h.span τ ^ n :=
  map_pow (galHom h.linearIndependent h.span) τ n

theorem frobF_pow : frobF h ^ Module.finrank Fq L = 1 := by
  unfold frobF
  rw [← gal_pow h, frobL_pow_finrank]
  exact map_one (galHom h.linearIndependent h.span)

theorem orderOf_frobF : orderOf (frobF h) = Module.finrank Fq L := by
  rw [← orderOf_frob Fq L]
  exact orderOf_injective (galHom h.linearIndependent h.span) (galHom_injective _ _) (frobL Fq L)

/-- A Frobenius-fixed element of `F'` is fixed by all of `Gal(L/Fq)`. -/
theorem gal_fixed_of_frob {x : F'} (hx : frobF h x = x) (τ : L ≃ₐ[Fq] L) :
    gal h.linearIndependent h.span τ x = x := by
  obtain ⟨n, rfl⟩ := exists_frobL_pow τ
  rw [gal_pow h]
  exact pow_apply_of_fixed _ hx n

theorem frobF_algebraMap_L (l : L) : frobF h (algebraMap L F' l) = algebraMap L F' (frobL Fq L l) :=
  gal_algebraMap_L h.linearIndependent h.span (frobL Fq L) l

theorem pnorm_frobF_algebraMap (l : L) (n : ℕ) :
    pnorm (frobF h) (algebraMap L F' l) n = algebraMap L F' (pnorm (frobL Fq L) l n) := by
  induction n with
  | zero => rw [pnorm_zero, pnorm_zero, map_one]
  | succ n ih => rw [pnorm_succ, pnorm_succ, ih, map_mul, frobF_algebraMap_L]

theorem div_frobF (f : F') : (div (frobF h f) : Divisor L F') = actD h (frobL Fq L) (div f) :=
  div_gal h (frobL Fq L) f

theorem div_algebraMap_L {l : L} (hl : l ≠ 0) : (div (algebraMap L F' l) : Divisor L F') = 0 :=
  ZetaSB.div_algebraMap L hl

include h in
/-- `div f = 0` in `F'` forces `f ∈ L`. -/
theorem exists_const_of_div_eq_zero (hk : constField Fq F = ⊥) {f : F'} (hf : f ≠ 0)
    (h0 : (div f : Divisor L F') = 0) : ∃ l : L, algebraMap L F' l = f := by
  have hm := (Places.div_eq_zero_iff L F' hf).1 h0
  rw [h.constField_eq_bot hk, IntermediateField.mem_bot] at hm
  exact hm

/-! ### `Pic` -/

/-- **Conorm on classes** `Pic(F) → Pic(F')`. -/
noncomputable def conormPic : Pic Fq F →+ Pic L F' :=
  QuotientAddGroup.map (princ Fq F) (princ L F') (conorm h) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact (mem_princ L F').2 ⟨algebraMap F F' f, (_root_.map_ne_zero _).2 hf, (conorm_div h f).symm⟩)

theorem conormPic_mk (D : Divisor Fq F) :
    conormPic h (QuotientAddGroup.mk D) = (QuotientAddGroup.mk (conorm h D) : Pic L F') := rfl

/-- `Gal(L/Fq)` acting on `Pic(F')`. -/
noncomputable def actPic (τ : L ≃ₐ[Fq] L) : Pic L F' →+ Pic L F' :=
  QuotientAddGroup.map (princ L F') (princ L F') (actD h τ).toAddMonoidHom (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact (mem_princ L F').2 ⟨gal h.linearIndependent h.span τ f, (_root_.map_ne_zero _).2 hf, div_gal h τ f⟩)

theorem actPic_mk (τ : L ≃ₐ[Fq] L) (D : Divisor L F') :
    actPic h τ (QuotientAddGroup.mk D) = (QuotientAddGroup.mk (actD h τ D) : Pic L F') := rfl

theorem actPic_conormPic (τ : L ≃ₐ[Fq] L) (x : Pic Fq F) : actPic h τ (conormPic h x) = conormPic h x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, actPic_mk, actD_conorm]

theorem degPic_conormPic (x : Pic Fq F) : degPic L F' (conormPic h x) = degPic Fq F x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, degPic_mk, degPic_mk, deg_conorm]

/-- **Injectivity** (Hilbert 90 for `L / Fq`). -/
theorem conormPic_injective (hk : constField Fq F = ⊥) : Function.Injective (conormPic h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, QuotientAddGroup.eq_zero_iff] at hx
  obtain ⟨g, hg, hgD⟩ := (mem_princ L F').1 hx
  have hσg : frobF h g ≠ 0 := (_root_.map_ne_zero _).2 hg
  have hu0 : frobF h g / g ≠ 0 := div_ne_zero hσg hg
  have hdiv : (div (frobF h g / g) : Divisor L F') = 0 := by
    rw [Places.div_div hσg hg, div_frobF, hgD, actD_conorm, sub_self]
  obtain ⟨u, hu⟩ := exists_const_of_div_eq_zero h hk hu0 hdiv
  have hk0 := finrank_pos' Fq L
  have hnu : pnorm (frobL Fq L) u (Module.finrank Fq L) = 1 := by
    apply (algebraMap L F').injective
    rw [← pnorm_frobF_algebraMap h, hu, pnorm_div_self (frobF h) hg, frobF_pow, AlgEquiv.one_apply,
      div_self hg, map_one]
  obtain ⟨b, hb, hub⟩ := hilbert90_cyclic (frobL Fq L) (orderOf_frob Fq L) hk0 hnu
  have hb' : algebraMap L F' b ≠ 0 := (_root_.map_ne_zero _).2 hb
  have hfb : algebraMap L F' (frobL Fq L b) ≠ 0 := (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hb)
  have e2 : frobF h g = algebraMap L F' u * g := by
    rw [hu]
    field_simp
  have hfix : frobF h (g / algebraMap L F' b) = g / algebraMap L F' b := by
    rw [map_div₀, frobF_algebraMap_L, e2, hub, map_div₀]
    field_simp
  obtain ⟨f, hf⟩ := RingHom.mem_range.1
    (mem_range_of_forall_gal h.linearIndependent h.span _ (gal_fixed_of_frob h hfix))
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact div_ne_zero hg hb' hf.symm
  rw [QuotientAddGroup.eq_zero_iff]
  refine (mem_princ Fq F).2 ⟨f, hf0, conorm_injective h ?_⟩
  rw [conorm_div, hf, Places.div_div hg hb', div_algebraMap_L (F' := F') hb, sub_zero, hgD]

/-- **Fixed classes descend** (Hilbert 90 for `F' / F` and `Br(Fq) = 0`). -/
theorem exists_conormPic_eq (hk : constField Fq F = ⊥) (x' : Pic L F') (hx : actPic h (frobL Fq L) x' = x') :
    ∃ x, conormPic h x = x' := by
  obtain ⟨D', rfl⟩ := QuotientAddGroup.mk_surjective x'
  rw [actPic_mk, QuotientAddGroup.eq] at hx
  obtain ⟨g, hg, hgD⟩ := (mem_princ L F').1 hx
  have hstep : actD h (frobL Fq L) D' = D' - div g := by
    rw [hgD]
    abel
  have hiter : ∀ n : ℕ, actD h (frobL Fq L ^ n) D' = D' - div (pnorm (frobF h) g n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, actD_one, pnorm_zero, div_one' L F', sub_zero]
    | succ n ih =>
      rw [pow_succ', actD_mul, ih, map_sub, hstep, ← div_frobF, pnorm_succ,
        Places.div_mul hg ((_root_.map_ne_zero (frobF h)).2 (pnorm_ne_zero (frobF h) hg n))]
      abel
  have hN0 : pnorm (frobF h) g (Module.finrank Fq L) ≠ 0 := pnorm_ne_zero _ hg _
  have hN : (div (pnorm (frobF h) g (Module.finrank Fq L)) : Divisor L F') = 0 := by
    have e := hiter (Module.finrank Fq L)
    rw [frobL_pow_finrank, actD_one] at e
    exact sub_eq_self.1 e.symm
  -- the norm `N = N_{F'/F}(g)` lies in `F`, has divisor `0`, hence is a constant of `Fq`
  have hNfix : frobF h (pnorm (frobF h) g (Module.finrank Fq L)) = pnorm (frobF h) g (Module.finrank Fq L) :=
    pnorm_fixed (frobF h) (frobF_pow h) hg
  obtain ⟨f0, hf0⟩ := RingHom.mem_range.1
    (mem_range_of_forall_gal h.linearIndependent h.span _ (gal_fixed_of_frob h hNfix))
  have hf00 : f0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf0
    exact hN0 hf0.symm
  have hdf0 : (div f0 : Divisor Fq F) = 0 := by
    apply conorm_injective h
    rw [conorm_div, hf0, hN, map_zero]
  have hm := (Places.div_eq_zero_iff Fq F hf00).1 hdf0
  rw [hk, IntermediateField.mem_bot] at hm
  obtain ⟨a0, ha0⟩ := hm
  have hNa : pnorm (frobF h) g (Module.finrank Fq L) = algebraMap L F' (algebraMap Fq L a0) := by
    rw [← hf0, ← ha0, ← IsScalarTower.algebraMap_apply Fq F F', IsScalarTower.algebraMap_apply Fq L F']
  have hk0 := finrank_pos' Fq L
  have hz : pnorm (frobL Fq L) (0 : L) (Module.finrank Fq L) = 0 := by
    rw [pnorm]
    exact Finset.prod_eq_zero (Finset.mem_range.2 hk0) (by simp)
  obtain ⟨b, hb⟩ := exists_pnorm_frob_eq Fq L a0
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hN0
    rw [hNa, ← hb]
    erw [hz]
    rw [map_zero]
  have hb' : algebraMap L F' b ≠ 0 := (_root_.map_ne_zero _).2 hb0
  have hw : pnorm (frobF h) (g / algebraMap L F' b) (Module.finrank Fq L) = 1 := by
    rw [div_eq_mul_inv, pnorm_mul, pnorm_inv, pnorm_frobF_algebraMap h]
    erw [hb]
    rw [← hNa, mul_inv_cancel₀ hN0]
  obtain ⟨e, he, hwe⟩ := hilbert90_cyclic (frobF h) (orderOf_frobF h) hk0 hw
  have hσe : frobF h e ≠ 0 := (_root_.map_ne_zero _).2 he
  have hg' : g = frobF h e / e * algebraMap L F' b := by
    rw [← hwe]
    field_simp
  have hdivg : (div g : Divisor L F') = actD h (frobL Fq L) (div e) - div e := by
    rw [hg', Places.div_mul (div_ne_zero hσe he) hb', Places.div_div hσe he, div_frobF,
      div_algebraMap_L (F' := F') hb0, add_zero]
  have hfixD : actD h (frobL Fq L) (D' + div e) = D' + div e := by
    rw [map_add, hstep, hdivg]
    abel
  obtain ⟨D, hD⟩ := exists_conorm_eq h _ (actD_forall_of_frob h hfixD)
  refine ⟨QuotientAddGroup.mk D, ?_⟩
  rw [conormPic_mk, hD, QuotientAddGroup.eq]
  refine (mem_princ L F').2 ⟨e⁻¹, inv_ne_zero he, ?_⟩
  rw [div_inv' L he]
  abel

end Descent

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_E1 =====
section

/-!
# S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools

* `hos_ext_ord`, `place_ext_ord`: a place is determined by its order function (and its side);
* `ringHom_ext_of_constExt`: a ring map out of `F' = L ⊗ F` is determined on `F` and on `L`;
* for `n ∣ N` (instance `Fact (n ∣ N)`): `Lc_le`, `Fc_le`, the inclusion algebras `L_n → L_N`, `F_n → F_N`,
  `L_n → F_N` with their towers, `pbLL : PowerBasis L_n L_N`, and
  **`isConstExt_pair hk : RR.IsConstExt L_n F_n L_N F_N (pbLL ..).basis`** (`F_N / F_n` is again a constant
  field extension, so all of parts C and D apply to it);
* Frobenius bookkeeping: `frobL_LL_apply` (`x ↦ x ^ (q ^ n)`), `frobL_pow_apply`, `frobL_algebraMap_LL`.
-/

set_option autoImplicit false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section ExtTools

/-- A height-one prime is determined by its order function. -/
theorem hos_ext_ord {S K : Type*} [CommRing S] [IsDedekindDomain S] [Places.FiniteQuot S] [Field K] [Algebra S K]
    [IsFractionRing S K] {P1 P2 : HeightOneSpectrum S}
    (h : ∀ f : K, Places.ord P1 f = Places.ord P2 f) : P1 = P2 := by
  have key : ∀ (P : HeightOneSpectrum S) (r : S), r ≠ 0 →
      (r ∈ P.asIdeal ↔ 0 < Places.ord P (algebraMap S K r)) := by
    intro P r hr
    have hs : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [Places.ord_algebraMap P hr, Nat.cast_pos, Places.cnt, Nat.pos_iff_ne_zero,
      Associates.count_ne_zero_iff_dvd hs P.irreducible, Ideal.dvd_span_singleton]
  ext r
  by_cases hr : r = 0
  · simp [hr]
  · rw [key P1 r hr, key P2 r hr, h]

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- A place is determined by its side and its order function. -/
theorem place_ext_ord {P1 P2 : Place Fq F} (hs : P1.isLeft = P2.isLeft)
    (h : ∀ f : F, P1.ord f = P2.ord f) : P1 = P2 := by
  rcases P1 with P1 | P1 <;> rcases P2 with P2 | P2
  · exact congrArg Sum.inl (hos_ext_ord (K := F) h)
  · simp at hs
  · simp at hs
  · exact congrArg Sum.inr (hos_ext_ord (K := F) h)

variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

/-- A ring map out of `F'` is determined by its values on `F` and on `L`. -/
theorem ringHom_ext_of_constExt (h : RR.IsConstExt Fq F L F' c) {R : Type*} [Semiring R] {φ ψ : F' →+* R}
    (hF : ∀ a : F, φ (algebraMap F F' a) = ψ (algebraMap F F' a))
    (hL : ∀ l : L, φ (algebraMap L F' l) = ψ (algebraMap L F' l)) : φ = ψ := by
  ext f
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (h.span (Submodule.mem_top (x := f)))
  simp only [map_sum, Algebra.smul_def, map_mul, hF, hL]

end ExtTools

section Pair

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable {n N : ℕ}

variable {Fq Ω} in
theorem Lc_le (hnN : n ∣ N) : Lc Fq Ω n ≤ Lc Fq Ω N := by
  intro x hx
  rw [mem_Lc] at hx ⊢
  obtain ⟨k, rfl⟩ := hnN
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul x (Fintype.card Fq ^ (n * k)) (Fintype.card Fq ^ n), ih, hx]

variable {Fq F Ω} in
theorem Fc_le (hnN : n ∣ N) : Fc Fq F Ω n ≤ Fc Fq F Ω N :=
  IntermediateField.adjoin_le_iff.2 fun _ hx => mem_Fc_of_mem_Lc (Lc_le hnN hx)

noncomputable instance algLL [Fact (n ∣ N)] : Algebra (Lc Fq Ω n) (Lc Fq Ω N) :=
  (IntermediateField.inclusion (Lc_le (Fact.out : n ∣ N))).toRingHom.toAlgebra

noncomputable instance algFF [Fact (n ∣ N)] : Algebra (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  (IntermediateField.inclusion (Fc_le (Fact.out : n ∣ N))).toRingHom.toAlgebra

noncomputable instance algLF [Fact (n ∣ N)] : Algebra (Lc Fq Ω n) (Fc Fq F Ω N) :=
  ((algebraMap (Lc Fq Ω N) (Fc Fq F Ω N)).comp (algebraMap (Lc Fq Ω n) (Lc Fq Ω N))).toAlgebra

variable [Fact (n ∣ N)]

theorem coe_algebraMap_LL (x : Lc Fq Ω n) : ((algebraMap (Lc Fq Ω n) (Lc Fq Ω N) x : Lc Fq Ω N) : Ω) = x :=
  rfl

instance tower_LFF : IsScalarTower (Lc Fq Ω n) (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_LLF : IsScalarTower (Lc Fq Ω n) (Lc Fq Ω N) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_FFF : IsScalarTower F (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_qLL : IsScalarTower Fq (Lc Fq Ω n) (Lc Fq Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

variable (n N) in
/-- A power basis of `L_N` over `L_n`. -/
noncomputable def pbLL [NeZero n] [NeZero N] : PowerBasis (Lc Fq Ω n) (Lc Fq Ω N) :=
  Field.powerBasisOfFiniteOfSeparable (Lc Fq Ω n) (Lc Fq Ω N)

/-- `L_n` has `q ^ n` elements, so its Frobenius over `L_n` on `L_N` is `x ↦ x ^ (q ^ n)`. -/
theorem frobL_LL_apply [IsAlgClosed Ω] [NeZero n] [NeZero N] (x : Lc Fq Ω N) :
    frobL (Lc Fq Ω n) (Lc Fq Ω N) x = x ^ Fintype.card Fq ^ n := by
  rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  show x ^ Fintype.card (Lc Fq Ω n) = _
  rw [← Nat.card_eq_fintype_card, card_Lc Fq Ω (NeZero.ne n)]

theorem frobL_pow_apply {K : Type*} [Field K] [Fintype K] [Algebra Fq K] (m : ℕ) (x : K) :
    (frobL Fq K ^ m) x = x ^ Fintype.card Fq ^ m := by
  rw [AlgEquiv.coe_pow, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- The Frobenius of `L_N / Fq` restricts to the Frobenius of `L_n / Fq`. -/
theorem frobL_algebraMap_LL [NeZero n] [NeZero N] (x : Lc Fq Ω n) :
    frobL Fq (Lc Fq Ω N) (algebraMap (Lc Fq Ω n) (Lc Fq Ω N) x) =
      algebraMap (Lc Fq Ω n) (Lc Fq Ω N) (frobL Fq (Lc Fq Ω n) x) := by
  rw [frobL, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, map_pow]

end Pair

section PairFF

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem finrank_pair (hk : constField Fq F = ⊥) :
    Module.finrank (Fc Fq F Ω n) (Fc Fq F Ω N) = Module.finrank (Lc Fq Ω n) (Lc Fq Ω N) := by
  have h1 := Module.finrank_mul_finrank F (Fc Fq F Ω n) (Fc Fq F Ω N)
  have h2 := Module.finrank_mul_finrank Fq (Lc Fq Ω n) (Lc Fq Ω N)
  rw [finrank_Fc Fq F Ω hk n, finrank_Fc Fq F Ω hk N, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem hx_pair : algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) (RR.xF (Lc Fq Ω n) (Fc Fq F Ω n)) =
    RR.xF (Lc Fq Ω N) (Fc Fq F Ω N) := by
  rw [← hx_Fc Fq F Ω n, ← hx_Fc Fq F Ω N]
  exact Subtype.ext rfl

/-- **`F_N / F_n` is a constant field extension** (for `n ∣ N`). -/
theorem isConstExt_pair (hk : constField Fq F = ⊥) :
    RR.IsConstExt (Lc Fq Ω n) (Fc Fq F Ω n) (Lc Fq Ω N) (Fc Fq F Ω N) (pbLL Fq Ω n N).basis :=
  isConstExt (pbLL Fq Ω n N) (constField_Fc Fq F Ω hk n) (finrank_pair Fq F Ω hk) (hx_pair Fq F Ω)

end PairFF

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_E2 =====
section

/-!
# S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius

Wrappers over parts D and E1 whose only instance binders are `NeZero` and `Fact (n ∣ N)`, so that part E3 can use
them at `n = N` without instance diamonds (never apply a generic part-D lemma to a pair with `n = N`):
* `contractNN`, `conormNN`, `conNN` (conorm on `Pic`), `conNN_trans`, `conNN_self`, `conNN_injective`, `degPic_conNN`;
* `frobN N`: the arithmetic Frobenius of `L_N / Fq` acting on `Pic(F_N)`; `frobN_conNN` (compatibility);
* `actPic_rel`: the Frobenius of `L_N / L_n` acts on `Pic(F_N)` as `(frobN N)^[n]`;
  `exists_conNN_eq` (descent from level `N` to level `n`), `frobN_iterate_conNN`.
-/

set_option autoImplicit false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

theorem isLeft_contract (P : Place L F') : (contract h P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem isLeft_plE (τ : L ≃ₐ[Fq] L) (P : Place L F') : (plE h τ P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem actPic_one (x : Pic L F') : actPic h 1 x = x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [actPic_mk, actD_one]

theorem actPic_pow (τ : L ≃ₐ[Fq] L) (k : ℕ) (x : Pic L F') : actPic h (τ ^ k) x = (actPic h τ)^[k] x := by
  induction k generalizing x with
  | zero => rw [pow_zero, actPic_one, Function.iterate_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← ih, pow_succ]
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [actPic_mk, actPic_mk, actPic_mk, actD_mul]

end Generic

section Levels

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-! ### Inclusions `F_n → F_N` -/

theorem coe_algebraMap_FF {n N : ℕ} [Fact (n ∣ N)] (x : Fc Fq F Ω n) :
    ((algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) x : Fc Fq F Ω N) : Ω) = x :=
  IntermediateField.coe_inclusion (Fc_le (Fact.out : n ∣ N)) x

theorem algebraMap_FFF {n N M : ℕ} [Fact (n ∣ N)] [Fact (N ∣ M)] [Fact (n ∣ M)] (x : Fc Fq F Ω n) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) x) =
      algebraMap (Fc Fq F Ω n) (Fc Fq F Ω M) x :=
  Subtype.ext (by rw [coe_algebraMap_FF, coe_algebraMap_FF, coe_algebraMap_FF])

theorem algebraMap_FF_F {N M : ℕ} [Fact (N ∣ M)] (a : F) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap F (Fc Fq F Ω N) a) = algebraMap F (Fc Fq F Ω M) a :=
  (IsScalarTower.algebraMap_apply F (Fc Fq F Ω N) (Fc Fq F Ω M) a).symm

theorem algebraMap_FF_L {N M : ℕ} [Fact (N ∣ M)] (l : Lc Fq Ω N) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) =
      algebraMap (Lc Fq Ω M) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Lc Fq Ω M) l) :=
  (IsScalarTower.algebraMap_apply (Lc Fq Ω N) (Fc Fq F Ω N) (Fc Fq F Ω M) l).symm.trans
    (IsScalarTower.algebraMap_apply (Lc Fq Ω N) (Lc Fq Ω M) (Fc Fq F Ω M) l)

variable (Ω) in
/-- Places of one level `F_N` are determined by side and orders (instance binders: `NeZero` only). -/
theorem placeN_ext (N : ℕ) [NeZero N] {P1 P2 : Place (Lc Fq Ω N) (Fc Fq F Ω N)}
    (hs : P1.isLeft = P2.isLeft) (ho : ∀ f, P1.ord f = P2.ord f) : P1 = P2 :=
  place_ext_ord hs ho

/-! ### Wrappers -/

variable (Ω) in
/-- Contraction of places from level `N` to level `n` (`n ∣ N`). -/
noncomputable def contractNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Place (Lc Fq Ω N) (Fc Fq F Ω N) → Place (Lc Fq Ω n) (Fc Fq F Ω n) :=
  contract (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- Conorm of divisors from level `n` to level `N` (`n ∣ N`). -/
noncomputable def conormNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Divisor (Lc Fq Ω n) (Fc Fq F Ω n) →+ Divisor (Lc Fq Ω N) (Fc Fq F Ω N) :=
  conorm (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- **Conorm of classes** `Pic(F_n) → Pic(F_N)` (`n ∣ N`). -/
noncomputable def conNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Pic (Lc Fq Ω n) (Fc Fq F Ω n) →+ Pic (Lc Fq Ω N) (Fc Fq F Ω N) :=
  conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- **The arithmetic Frobenius** of `L_N / Fq` acting on `Pic(F_N)`. -/
noncomputable def frobN (N : ℕ) [NeZero N] : Pic (Lc Fq Ω N) (Fc Fq F Ω N) →+ Pic (Lc Fq Ω N) (Fc Fq F Ω N) :=
  actPic (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N))

section Pair

variable {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem isLeft_contractNN (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    (contractNN Ω hk n N P).isLeft = P.isLeft :=
  isLeft_contract (isConstExt_pair Fq F Ω hk (n := n) (N := N)) P

theorem ord_contractNN (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) (f : Fc Fq F Ω n) :
    (contractNN Ω hk n N P).ord f = P.ord (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) f) :=
  ord_contract (isConstExt_pair Fq F Ω hk (n := n) (N := N)) P f

theorem conormNN_apply (D : Divisor (Lc Fq Ω n) (Fc Fq F Ω n)) (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    conormNN Ω hk n N D P = D (contractNN Ω hk n N P) :=
  conorm_apply (isConstExt_pair Fq F Ω hk (n := n) (N := N)) D P

theorem conNN_mk (D : Divisor (Lc Fq Ω n) (Fc Fq F Ω n)) :
    conNN Ω hk n N (QuotientAddGroup.mk D) =
      (QuotientAddGroup.mk (conormNN Ω hk n N D) : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) := rfl

theorem conNN_injective : Function.Injective (conNN Ω hk n N) :=
  conormPic_injective (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (constField_Fc Fq F Ω hk n)

theorem degPic_conNN (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    degPic (Lc Fq Ω N) (Fc Fq F Ω N) (conNN Ω hk n N x) = degPic (Lc Fq Ω n) (Fc Fq F Ω n) x :=
  degPic_conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) x

end Pair

theorem frobN_mk (N : ℕ) [NeZero N] (D : Divisor (Lc Fq Ω N) (Fc Fq F Ω N)) :
    frobN Ω hk N (QuotientAddGroup.mk D) =
      (QuotientAddGroup.mk (actD (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N)) D) :
        Pic (Lc Fq Ω N) (Fc Fq F Ω N)) := rfl

/-! ### Transitivity and the identity -/

theorem contractNN_trans {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M] [Fact (n ∣ N)] [Fact (N ∣ M)]
    [Fact (n ∣ M)] (P : Place (Lc Fq Ω M) (Fc Fq F Ω M)) :
    contractNN Ω hk n N (contractNN Ω hk N M P) = contractNN Ω hk n M P := by
  refine placeN_ext Ω n ?_ fun f => ?_
  · simp only [isLeft_contractNN]
  · rw [ord_contractNN, ord_contractNN, ord_contractNN, algebraMap_FFF]

/-- **Transitivity of conorm** for `n ∣ N ∣ M`. -/
theorem conNN_trans {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M] [Fact (n ∣ N)] [Fact (N ∣ M)]
    [Fact (n ∣ M)] (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    conNN Ω hk N M (conNN Ω hk n N x) = conNN Ω hk n M x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk, conNN_mk, conNN_mk]
  congr 1
  ext P
  rw [conormNN_apply, conormNN_apply, conormNN_apply, contractNN_trans]

/-- (The `Fact` binder comes after `P`, so that the type of `P` is elaborated without it.) -/
theorem contractNN_self (N : ℕ) [NeZero N] (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) [Fact (N ∣ N)] :
    contractNN Ω hk N N P = P := by
  refine placeN_ext Ω N (isLeft_contractNN hk P) fun f => ?_
  rw [ord_contractNN]
  congr 1

/-- **Conorm to the same level is the identity.** -/
theorem conNN_self (N : ℕ) [NeZero N] (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) [Fact (N ∣ N)] :
    conNN Ω hk N N x = x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk]
  congr 1
  ext P
  rw [conormNN_apply, contractNN_self]

/-! ### Frobenius compatibility -/

theorem frobF_conNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (f : Fc Fq F Ω N) :
    frobF (isConstExt_Fc Fq F Ω hk M) (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) f) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (frobF (isConstExt_Fc Fq F Ω hk N) f) := by
  have hF : ∀ a : F, frobF (isConstExt_Fc Fq F Ω hk M)
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap F (Fc Fq F Ω N) a)) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (frobF (isConstExt_Fc Fq F Ω hk N) (algebraMap F (Fc Fq F Ω N) a)) :=
    fun a => by rw [algebraMap_FF_F, AlgEquiv.commutes, AlgEquiv.commutes, algebraMap_FF_F]
  have hL : ∀ l : Lc Fq Ω N, frobF (isConstExt_Fc Fq F Ω hk M)
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l)) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)
        (frobF (isConstExt_Fc Fq F Ω hk N) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l)) :=
    fun l => by
      rw [algebraMap_FF_L, frobF_algebraMap_L, frobF_algebraMap_L, frobL_algebraMap_LL, algebraMap_FF_L]
  have key := ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk N)
    (φ := (frobF (isConstExt_Fc Fq F Ω hk M) : Fc Fq F Ω M →+* Fc Fq F Ω M).comp
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)))
    (ψ := (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)).comp
      (frobF (isConstExt_Fc Fq F Ω hk N) : Fc Fq F Ω N →+* Fc Fq F Ω N)) hF hL
  exact RingHom.congr_fun key f

theorem plE_contractNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (P : Place (Lc Fq Ω M) (Fc Fq F Ω M)) :
    contractNN Ω hk N M (plE (isConstExt_Fc Fq F Ω hk M) (frobL Fq (Lc Fq Ω M)) P) =
      plE (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N)) (contractNN Ω hk N M P) := by
  refine placeN_ext Ω N ?_ fun f => ?_
  · simp only [isLeft_contractNN, isLeft_plE]
  · rw [ord_contractNN, ord_plE, ord_plE, ord_contractNN]
    exact congrArg P.ord (frobF_conNN hk f)

/-- **Frobenius commutes with conorm.** -/
theorem frobN_conNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) :
    frobN Ω hk M (conNN Ω hk N M x) = conNN Ω hk N M (frobN Ω hk N x) := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk, frobN_mk, frobN_mk, conNN_mk]
  congr 1
  ext P
  rw [actD_apply, conormNN_apply, conormNN_apply, actD_apply, plE_contractNN]

/-! ### The Frobenius of `L_N / L_n` and descent -/

section Rel

variable [IsAlgClosed Ω] {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem gal_rel (f : Fc Fq F Ω N) :
    gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N)) f =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) f := by
  have hF : ∀ a : F, gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N))
        (algebraMap F (Fc Fq F Ω N) a) =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) (algebraMap F (Fc Fq F Ω N) a) := fun a => by
    rw [IsScalarTower.algebraMap_apply F (Fc Fq F Ω n) (Fc Fq F Ω N) a, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply F (Fc Fq F Ω n) (Fc Fq F Ω N) a, AlgEquiv.commutes]
  have hL : ∀ l : Lc Fq Ω N, gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N))
        (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) := fun l => by
    rw [gal_algebraMap_L, gal_algebraMap_L, frobL_LL_apply, frobL_pow_apply]
  have key := ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk N)
    (φ := (gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N)) :
          Fc Fq F Ω N →+* Fc Fq F Ω N))
    (ψ := (gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) : Fc Fq F Ω N →+* Fc Fq F Ω N)) hF hL
  exact RingHom.congr_fun key f

theorem plE_rel (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    plE (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (frobL (Lc Fq Ω n) (Lc Fq Ω N)) P =
      plE (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N) ^ n) P := by
  refine placeN_ext Ω N ?_ fun f => ?_
  · simp only [isLeft_plE]
  · rw [ord_plE, ord_plE, gal_rel hk f]

/-- **The Frobenius of `L_N / L_n` is the `n`-th power of the Frobenius of `L_N / Fq`.** -/
theorem actPic_rel (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) :
    actPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (frobL (Lc Fq Ω n) (Lc Fq Ω N)) x =
      (frobN Ω hk N)^[n] x := by
  rw [frobN, ← actPic_pow]
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [actPic_mk, actPic_mk]
  congr 1
  ext P
  rw [actD_apply, actD_apply, plE_rel hk]

/-- **Descent** from level `N` to level `n`: a class fixed by `π ^ n` comes from `Pic(F_n)`. -/
theorem exists_conNN_eq (x' : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) (hx : (frobN Ω hk N)^[n] x' = x') :
    ∃ x, conNN Ω hk n N x = x' :=
  exists_conormPic_eq (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (constField_Fc Fq F Ω hk n) x'
    (by rw [actPic_rel]; exact hx)

theorem frobN_iterate_conNN (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    (frobN Ω hk N)^[n] (conNN Ω hk n N x) = conNN Ω hk n N x := by
  rw [← actPic_rel]
  exact actPic_conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) _ x

end Rel

end Levels

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

/-- The levels `(j+1)!`, cofinal for divisibility. -/
def lev (j : ℕ) : ℕ := Nat.factorial (j + 1)

instance neZero_lev (j : ℕ) : NeZero (lev j) := ⟨Nat.factorial_ne_zero _⟩

theorem lev_dvd {i j : ℕ} (h : i ≤ j) : lev i ∣ lev j :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ h)

theorem dvd_lev {m j : ℕ} (hm : 0 < m) (h : m ≤ j) : m ∣ lev j :=
  Nat.dvd_factorial hm (Nat.le_succ_of_le h)

section Bar

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

variable (Fq F Ω) in
/-- `Pic(F_{(j+1)!})`. -/
abbrev PicL (j : ℕ) : Type _ := Pic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))

variable (Ω) in
/-- The transition maps (conorm) of the directed system `j ↦ Pic(F_{(j+1)!})`. -/
noncomputable def tr (i j : ℕ) (h : i ≤ j) : PicL Fq F Ω i →+ PicL Fq F Ω j :=
  haveI : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
  conNN Ω hk (lev i) (lev j)

theorem tr_apply {i j : ℕ} (h : i ≤ j) (x : PicL Fq F Ω i) [Fact (lev i ∣ lev j)] :
    tr Ω hk i j h x = conNN Ω hk (lev i) (lev j) x := rfl

theorem tr_injective {i j : ℕ} (h : i ≤ j) : Function.Injective (tr Ω hk i j h) := by
  have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
  intro x y hxy
  rw [tr_apply hk h x, tr_apply hk h y] at hxy
  exact conNN_injective hk hxy

instance directedSystem_tr : DirectedSystem (PicL Fq F Ω) (fun i j h => tr Ω hk i j h) where
  map_self i x := by
    have : Fact (lev i ∣ lev i) := ⟨dvd_rfl⟩
    rw [tr_apply hk le_rfl x]
    exact conNN_self hk (lev i) x
  map_map k j i hij hjk x := by
    have : Fact (lev i ∣ lev j) := ⟨lev_dvd hij⟩
    have : Fact (lev j ∣ lev k) := ⟨lev_dvd hjk⟩
    have : Fact (lev i ∣ lev k) := ⟨lev_dvd (hij.trans hjk)⟩
    rw [tr_apply hk hij x, tr_apply hk hjk, tr_apply hk (hij.trans hjk) x]
    exact conNN_trans hk x

variable (Ω) in
/-- **`Pic(X̄)`**, `X̄ = F̄ ⊗ K`: the direct limit of `Pic(F_n)` along the conorm maps. -/
abbrev PicBar : Type _ := AddCommGroup.DirectLimit (PicL Fq F Ω) (tr Ω hk)

variable (Ω) in
/-- The class of a level-`(j+1)!` divisor class in `Pic(X̄)`. -/
noncomputable abbrev ofBar (j : ℕ) : PicL Fq F Ω j →+ PicBar Ω hk :=
  AddCommGroup.DirectLimit.of (PicL Fq F Ω) (tr Ω hk) j

theorem ofBar_injective (j : ℕ) : Function.Injective (ofBar Ω hk j) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨k, hjk, h0⟩ := AddCommGroup.DirectLimit.of.zero_exact j x hx
  exact tr_injective hk hjk (h0.trans (map_zero _).symm)

/-! ### The arithmetic Frobenius on `Pic(X̄)` -/

variable (Ω) in
/-- **The arithmetic Frobenius `π`** (`x ↦ x ^ q` on the constants) acting on `Pic(X̄)`. -/
noncomputable def piBar : PicBar Ω hk →+ PicBar Ω hk :=
  AddCommGroup.DirectLimit.map (fun j => frobN Ω hk (lev j)) fun i j h => by
    refine AddMonoidHom.ext fun x => ?_
    have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
    show frobN Ω hk (lev j) (tr Ω hk i j h x) = tr Ω hk i j h (frobN Ω hk (lev i) x)
    rw [tr_apply hk h x, tr_apply hk h]
    exact frobN_conNN hk x

theorem piBar_of (j : ℕ) (y : PicL Fq F Ω j) :
    piBar Ω hk (ofBar Ω hk j y) = ofBar Ω hk j (frobN Ω hk (lev j) y) :=
  AddCommGroup.DirectLimit.map_apply_of _ _ y

theorem piBar_iterate_of (k j : ℕ) (y : PicL Fq F Ω j) :
    (piBar Ω hk)^[k] (ofBar Ω hk j y) = ofBar Ω hk j ((frobN Ω hk (lev j))^[k] y) :=
  (Function.Semiconj.iterate_right (f := ofBar Ω hk j) (ga := frobN Ω hk (lev j)) (gb := piBar Ω hk)
    (fun y => (piBar_of hk j y).symm) k y).symm

variable (Ω) in
/-- `Pic(X̄)^(π^m)`. -/
noncomputable def fixedBar (m : ℕ) : AddSubgroup (PicBar Ω hk) where
  carrier := {x | (piBar Ω hk)^[m] x = x}
  add_mem' := fun {a b} (ha : (piBar Ω hk)^[m] a = a) (hb : (piBar Ω hk)^[m] b = b) => by
    show (piBar Ω hk)^[m] (a + b) = a + b
    rw [iterate_map_add, ha, hb]
  zero_mem' := by
    show (piBar Ω hk)^[m] 0 = 0
    exact iterate_map_zero _ _
  neg_mem' := fun {a} (ha : (piBar Ω hk)^[m] a = a) => by
    show (piBar Ω hk)^[m] (-a) = -a
    rw [iterate_map_neg, ha]

theorem mem_fixedBar (m : ℕ) (x : PicBar Ω hk) : x ∈ fixedBar Ω hk m ↔ (piBar Ω hk)^[m] x = x := Iff.rfl

/-! ### Degree and `Pic⁰(X̄)` -/

variable (Ω) in
/-- The degree on `Pic(X̄)`. -/
noncomputable def degBar : PicBar Ω hk →+ ℤ :=
  AddCommGroup.DirectLimit.lift (PicL Fq F Ω) (tr Ω hk) ℤ
    (fun j => degPic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) fun i j h x => by
      have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
      rw [tr_apply hk h x]
      exact degPic_conNN hk x

theorem degBar_of (j : ℕ) (y : PicL Fq F Ω j) :
    degBar Ω hk (ofBar Ω hk j y) = degPic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ j y

variable (Ω) in
/-- **`Pic⁰(X̄)`**. -/
noncomputable def PicBar0 : AddSubgroup (PicBar Ω hk) := (degBar Ω hk).ker

theorem mem_PicBar0 (z : PicBar Ω hk) : z ∈ PicBar0 Ω hk ↔ degBar Ω hk z = 0 := AddMonoidHom.mem_ker

/-! ### `Pic(F_m) → Pic(X̄)` and descent -/

variable (Ω) in
/-- `Pic(F_m) →+ Pic(X̄)`: conorm to level `(m+1)!`, then into the limit. -/
noncomputable def toBar (m : ℕ) [NeZero m] : Pic (Lc Fq Ω m) (Fc Fq F Ω m) →+ PicBar Ω hk :=
  haveI : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  (ofBar Ω hk m).comp (conNN Ω hk m (lev m))

theorem toBar_apply (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) [Fact (m ∣ lev m)] :
    toBar Ω hk m x = ofBar Ω hk m (conNN Ω hk m (lev m) x) := rfl

/-- `toBar` computed at any level `j ≥ m`. -/
theorem toBar_eq (m : ℕ) [NeZero m] {j : ℕ} (hj : m ≤ j) (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m))
    [Fact (m ∣ lev j)] : toBar Ω hk m x = ofBar Ω hk j (conNN Ω hk m (lev j) x) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  have : Fact (lev m ∣ lev j) := ⟨lev_dvd hj⟩
  rw [toBar_apply hk m x, ← conNN_trans (N := lev m) (M := lev j) hk x, ← tr_apply hk hj]
  exact (AddCommGroup.DirectLimit.of_f hj _).symm

theorem toBar_injective (m : ℕ) [NeZero m] : Function.Injective (toBar Ω hk m) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  intro x y hxy
  rw [toBar_apply hk m x, toBar_apply hk m y] at hxy
  exact conNN_injective hk (ofBar_injective hk m hxy)

theorem degBar_toBar (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    degBar Ω hk (toBar Ω hk m x) = degPic (Lc Fq Ω m) (Fc Fq F Ω m) x := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [toBar_apply hk m x, degBar_of, degPic_conNN hk x]

theorem toBar_mem_PicBar0 (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    toBar Ω hk m x ∈ PicBar0 Ω hk ↔ x ∈ Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) := by
  rw [mem_PicBar0, degBar_toBar]
  exact AddMonoidHom.mem_ker.symm

section Descent

variable [IsAlgClosed Ω]

theorem toBar_mem (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    toBar Ω hk m x ∈ fixedBar Ω hk m := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [mem_fixedBar, toBar_apply hk m x, piBar_iterate_of, frobN_iterate_conNN hk x]

/-! ### The base level `m = 1` and class numbers -/

end Descent

end Bar

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_CoreA_Pic =====
section

/-!
# S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`

`A = Pic(X̄)[l^∞]` (`AddCommGroup.primaryComponent`, automatically inside `Pic⁰(X̄)`: `primary_le_PicBar0`),
`π = piBar` restricted to it (`piA`). The fixed points of `π ^ m` on `A` are the `l`-primary part of
`Pic⁰(X̄)^(π^m) = Pic⁰(X_m)`, of order `l ^ v_l(h_m)` (`card_fix_piA`, from `card_primaryComponent`).
With `card c = 2g`, `Π c_i = q^g` (`card_eq_two_genus`) and the valuation growth of `h_m = Π (1 - c_i^m)`
(`valuation_growth_padic`), the abstract `tate_rank` gives **`tate_rank_Pic`**: `T_l` of the divisible part of
`A` is free of rank `2g` over `ℤ_[l]`, with the Frobenius matrix `M`, `v det (1 - M^n)` equal to `v_l(h_n)` up to the
bounded contribution of the finite part `Phi = A ⧸ D`, and `Phi = 0 ↔ A` divisible `↔ #A[l] = l ^ 2g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial Matrix

namespace RamanujanPetersson.CoreA

/-- The `l`-primary part of a finite abelian group has order `l ^ v_l(#G)`. -/
theorem card_primaryComponent {G : Type*} [AddCommGroup G] [Finite G] (l : ℕ) [hl : Fact l.Prime] :
    Nat.card (AddCommGroup.primaryComponent G l) = l ^ padicValNat l (Nat.card G) := by
  set T := AddCommGroup.primaryComponent G l
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hT := Nat.eq_prime_pow_of_unique_prime_dvd hT0 (p := l) fun {d} hd hdvd => by
    have := Fact.mk hd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
    have h1 : l ^ k • y = 0 := Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hk)
    have h2 := addOrderOf_dvd_of_nsmul_eq_zero h1
    rw [hy] at h2
    exact (Nat.prime_dvd_prime_iff_eq hd hl.out).mp (hd.dvd_of_dvd_pow h2)
  obtain ⟨a, ha⟩ : ∃ a, Nat.card T = l ^ a := ⟨_, hT⟩
  have hQ : ¬ l ∣ Nat.card (G ⧸ T) := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' l h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    have h1 : ((l • y : G) : G ⧸ T) = 0 := by
      rw [QuotientAddGroup.mk_nsmul, ← hz]
      exact addOrderOf_nsmul_eq_zero _
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp ((QuotientAddGroup.eq_zero_iff _).mp h1)
    have h2 : (y : G ⧸ T) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr
      (AddCommGroup.mem_primaryComponent.mpr ⟨k + 1, by rw [pow_succ, mul_smul, hk]⟩)
    rw [h2, addOrderOf_zero] at hz
    exact hl.out.one_lt.ne hz
  have hQ0 : Nat.card (G ⧸ T) ≠ 0 := Nat.card_pos.ne'
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T, padicValNat.mul hQ0 hT0,
    padicValNat.eq_zero_of_not_dvd hQ, zero_add, ha, padicValNat.prime_pow]

open Places ZetaSB PicDescent RR

section Pic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

variable (Ω) in
/-- **`A = Pic(X̄)[l^∞]`**, the `l`-primary torsion of `Pic(X̄)` (inside `Pic⁰(X̄)`). -/
abbrev Aℓ (l : ℕ) : Type _ := AddCommGroup.primaryComponent (PicBar Ω hk) l

theorem primary_le_PicBar0 {l : ℕ} (hl : l ≠ 0) :
    AddCommGroup.primaryComponent (PicBar Ω hk) l ≤ PicBar0 Ω hk := by
  intro x hx
  obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp hx
  rw [mem_PicBar0]
  have h := congrArg (degBar Ω hk) hx
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (pow_ne_zero k hl))

variable (Ω) in
/-- The Frobenius `π` on `A = Pic(X̄)[l^∞]`. -/
noncomputable def piA (l : ℕ) : Aℓ Ω hk l →+ Aℓ Ω hk l :=
  ((piBar Ω hk).comp (AddCommGroup.primaryComponent (PicBar Ω hk) l).subtype).codRestrict _ fun x => by
    obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.2
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by
      rw [AddMonoidHom.comp_apply, ← map_nsmul, AddSubgroup.coe_subtype, hx, map_zero]⟩

theorem piA_iterate_coe (l m : ℕ) (x : Aℓ Ω hk l) :
    (((piA Ω hk l)^[m] x : Aℓ Ω hk l) : PicBar Ω hk) = (piBar Ω hk)^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

section Descent

variable [IsAlgClosed Ω]

/-- Every class of `Pic(X̄)` is fixed by some power of `π` (it is defined over some `F_(q^n)`). -/
theorem exists_piBar_iterate_eq (z : PicBar Ω hk) : ∃ m, 0 < m ∧ (piBar Ω hk)^[m] z = z := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ⟨lev j, NeZero.pos _, ?_⟩
  show (piBar Ω hk)^[lev j] (ofBar Ω hk j y) = ofBar Ω hk j y
  have : Fact (lev j ∣ lev j) := ⟨dvd_rfl⟩
  have h1 := frobN_iterate_conNN (Ω := Ω) hk (n := lev j) (N := lev j) y
  rw [conNN_self] at h1
  rw [piBar_iterate_of, h1]

/-- **`A^(π^m)` is the `l`-primary part of `Pic⁰(X_m)`**, of order `l ^ v_l(h_m)`. -/
theorem card_fix_piA (l : ℕ) [hl : Fact l.Prime] (m : ℕ) [NeZero m]
    [Finite (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))] :
    Nat.card {x : Aℓ Ω hk l // (piA Ω hk l)^[m] x = x} =
      l ^ padicValNat l (Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))) := by
  rw [← card_primaryComponent]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_inf.mpr ⟨?_, primary_le_PicBar0 hk hl.out.ne_zero x.1.2⟩⟩, ?_⟩
      invFun := fun y => ⟨⟨y.1.1, ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · rw [mem_fixedBar, ← piA_iterate_coe, x.2]
  · obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.1.2
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hx)⟩
  · obtain ⟨k, hy⟩ := AddCommGroup.mem_primaryComponent.mp y.2
    have := congrArg Subtype.val hy
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, this⟩
  · exact Subtype.ext (by rw [piA_iterate_coe]; exact (AddSubgroup.mem_inf.mp y.1.2).1)

variable (Ω) in
/-- `h_n = #Pic⁰(X̄)^(π^n) = #Pic⁰(X_n)`. -/
noncomputable def hBar (n : ℕ) : ℕ := Nat.card (fixedBar Ω hk n ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))

end Descent

end Pic

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_Kummer_InfMain =====
section

/-!
# S4-Kummer K5c: parabolic Kummer classes (main theorem)

Generic chart `R0` (Dedekind, fraction field `K`), boundary data `D` whose `B` is "nonzero prime of the pro-chart".
* `forall_dvd_congr_range`: the divisibility condition `N ∣ v(a)` does not depend on the Dedekind model of the integral
  closure of `R0` in `M`.
* `fixed_of_dvd`: `N ∣ v(a)` at all primes over `R0` ⇒ boundary inertia fixing `M` fixes every `N`-th root of `a`.
* `dvd_of_mem_maxUnram`: an `N`-th root of `a` unramified over `R0` ⇒ `N ∣ v(a)` at all primes over `R0`.
* `fixed_of_mem_curveH1par`: a parabolic Kummer class is fixed by the inertia of EVERY boundary prime.
* **`kclass_mem_curveH1par_iff`**: `kclass α ∈ H¹_par ↔ α ∈ maxUnram R0 K ↔ ∀ v over R0, N ∣ v(α ^ N)`.
* Curve instance (`R0 = Rinf`): `isIntegral_iff_mem_Rinf`, `perfect_Rinf`, `Fc_mem_unramSet_inf`, `fixed_of_mem_Fc`,
  **`kclass_mem_curveH1par_iff_ord`** (orders at the infinite places of the constant level `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

section GenericInf

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0] [IsDedekindDomain R0]
  [Algebra R0 K] [IsFractionRing R0 K]

/-- The divisibility condition is independent of the Dedekind model `B` of the integral closure of `R0` in `M`. -/
theorem forall_dvd_congr_range {M : IntermediateField K (AlgebraicClosure K)}
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range) (n : ℤ) (a : M) :
    (∀ v : HeightOneSpectrum B, n ∣ WithZero.log (v.valuation M a)) ↔
      ∀ v : HeightOneSpectrum (integralClosure R0 M), n ∣ WithZero.log (v.valuation M a) := by
  have hBinj : Function.Injective (algebraMap B M) := IsFractionRing.injective B M
  have hrange : (integralClosure R0 M).toSubring = (algebraMap B M).range :=
    Subring.ext fun x => hB x
  let e1 : integralClosure R0 M ≃+* (algebraMap B M).range := RingEquiv.subringCongr hrange
  let e2 : B ≃+* (algebraMap B M).range := RingEquiv.ofBijective (algebraMap B M).rangeRestrict
    ⟨fun x y hxy => hBinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  let eR : integralClosure R0 M ≃+* B := e1.trans e2.symm
  have heR : ∀ x, algebraMap B M (eR x) = algebraMap (integralClosure R0 M) M x := fun x =>
    congrArg Subtype.val (e2.apply_symm_apply (e1 x))
  have heR' : ∀ b, algebraMap (integralClosure R0 M) M (eR.symm b) = algebraMap B M b := fun b => by
    rw [← heR, RingEquiv.apply_symm_apply]
  constructor
  · intro hv v
    have h1 := hv (HeightOneSpectrum.comap (eR.symm : B →+* integralClosure R0 M) eR.symm.surjective v)
    rwa [valuation_comap eR.symm heR' v] at h1
  · intro hv v
    have h1 := hv (HeightOneSpectrum.comap (eR : integralClosure R0 M →+* B) eR.surjective v)
    rwa [valuation_comap eR heR v] at h1

/-- **(b)** `N ∣ v(a)` at every prime over `R0` (in any Dedekind model `B`) ⇒ a pro-chart inertia element fixing the
finite level `M ∈ unramSet A K` fixes every `N`-th root of `a`. -/
theorem fixed_of_dvd {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K) {N : ℕ} [NeZero N]
    (hN : IsUnit (N : R0)) {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M]
    [IsFractionRing B M] (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    (hv : ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a))
    {P : Ideal (proChart A K R0)} [P.IsPrime] {g : Pi1 A K} (hg : g ∈ P.inertia (Pi1 A K))
    (hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x)
    (α : maxUnram A K) (hα : (α : AlgebraicClosure K) ^ N = a) : g α = α := by
  haveI : FiniteDimensional K M := hM.1
  haveI : IsGalois K M := hM.2.1
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  obtain ⟨I, hI⟩ := exists_pow_mul_spanSingleton_eq_one ha ((forall_dvd_congr_range R0 hB (N : ℤ) a).1 hv)
  exact fixed_of_bdry_inertia hM hN hg hgM I hI α hα

/-- **(c)** An `N`-th root of `a ∈ M` unramified over `R0` ⇒ `N ∣ v(a)` at every prime over `R0`. -/
theorem dvd_of_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hMR : M ∈ unramSet R0 K)
    (hperf : ∀ (p : Ideal R0) [p.IsMaximal], PerfectField p.ResidueField)
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    {N : ℕ} {α : AlgebraicClosure K} (hαU : α ∈ maxUnram R0 K) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    (v : HeightOneSpectrum B) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  haveI : FiniteDimensional K M := hMR.1
  haveI : IsGalois K M := hMR.2.1
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  exact (forall_dvd_congr_range R0 hB (N : ℤ) a).2 (dvd_log_valuation_of_mem_maxUnram R0 hMR hperf hαU hα) v

variable {q N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ) {S : Type} (D : BdryData A K q R0 S)

include hζ hζΓ in
/-- A parabolic Kummer class is fixed by the inertia of EVERY boundary prime (not only the representatives `D.P s`):
conjugate into `D.P s` by `h ∈ π₁^geo` and use that `kchar α` is a homomorphism to an abelian group. -/
theorem fixed_of_mem_curveH1par {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e) (hq : q = p ^ e)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D) :
    ∀ P : Ideal (proChart A K R0), IsBdryPrime A K R0 P → ∀ g ∈ P.inertia (Pi1 A K),
      g (α : maxUnram A K) = α := by
  intro P hP g hg
  haveI := hP.1
  have hgΓ : g ∈ pi1geo A K q := inertia_le_pi1geo he hq hg
  obtain ⟨s, h, hh, hPs⟩ := D.cover P ((hDB P).2 hP)
  have hg' : h⁻¹ * g * h ∈ D.inertia s := inv_conj_mem_inertia A K R0 hPs hg
  have hΓ' : h⁻¹ * g * h ∈ pi1geo A K q := mul_mem (mul_mem (inv_mem hh) hgΓ) hh
  have h0 := ((mem_curveH1par_iff hζ hζΓ D hα).1 hpar) s _ hΓ' hg'
  have hk : kchar hζ α (⟨h⁻¹ * g * h, hΓ'⟩ : pi1geo A K q) = 0 :=
    (kchar_eq_iff hζ hα _ 0).2 (by rw [epow_zero, one_mul]; exact h0)
  have e1 := kchar_mul hζ hζΓ hα ((⟨h, hh⟩ : pi1geo A K q)⁻¹ * ⟨g, hgΓ⟩) ⟨h, hh⟩
  have e2 := kchar_mul hζ hζΓ hα (⟨h, hh⟩ : pi1geo A K q)⁻¹ ⟨g, hgΓ⟩
  have e3 := kchar_mul hζ hζΓ hα (⟨h, hh⟩ : pi1geo A K q)⁻¹ ⟨h, hh⟩
  rw [inv_mul_cancel, kchar_one hζ hζΓ hα] at e3
  have e0 : (⟨h, hh⟩ : pi1geo A K q)⁻¹ * ⟨g, hgΓ⟩ * ⟨h, hh⟩ = ⟨h⁻¹ * g * h, hΓ'⟩ := Subtype.ext rfl
  rw [e0, hk, e2] at e1
  have hg0 : kchar hζ α (⟨g, hgΓ⟩ : pi1geo A K q) = 0 := by linear_combination -e1 + e3
  have h1 := (kchar_eq_iff hζ hα (⟨g, hgΓ⟩ : pi1geo A K q) 0).1 hg0
  rw [epow_zero, one_mul] at h1
  exact h1

include hζ hζΓ in
/-- **K5c MAIN (generic chart)**: for `α` with `α ^ N = a ∈ M` (`M` a finite level of constants, unramified over `A`
and over `R0`), the Kummer class of `α` is parabolic iff `α` is unramified over `R0` iff `N` divides the valuation of
`a` at every prime of `M` over `R0`. -/
theorem kclass_mem_curveH1par_iff {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e) (hq : q = p ^ e)
    (hlift : BdryLift A K R0) (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q)
    {M : IntermediateField K (AlgebraicClosure K)} (hMA : M ∈ unramSet A K) (hMR : M ∈ unramSet R0 K)
    (hperf : ∀ (p : Ideal R0) [p.IsMaximal], PerfectField p.ResidueField) (hN : IsUnit (N : R0))
    (hMfix : ∀ g ∈ pi1geo A K q, ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x)
    {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N)
    (haα : ((α : maxUnram A K) : AlgebraicClosure K) ^ N = a) :
    (kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D ↔
        ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K) ∧
      (kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D ↔
        ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) := by
  have h1 : kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D →
      ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K := fun hpar =>
    mem_maxUnram_of_fixed hlift _ (fixed_of_mem_curveH1par R0 hζ hζΓ D he hq hDB hα hpar)
  have h2 : ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K →
      ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a) := fun hU =>
    dvd_of_mem_maxUnram R0 hMR hperf hB hU haα
  have h3 : (∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) →
      kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D := fun hv => by
    rw [mem_curveH1par_iff hζ hζΓ D hα]
    intro s g hgΓ hgs
    haveI : (D.P s).IsPrime := ((hDB _).1 (D.mem s)).1
    exact fixed_of_dvd R0 hMA hN ha hB hv (P := D.P s) hgs (hMfix g hgΓ) _ haα
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end GenericInf

/-! ## The curve instance: `R0 = Rinf` -/

section GenericC

open PicDescent Places

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

/-- In a constant field extension `F'/F`, the integral closure of `Rinf(F)` in `F'` is `Rinf(F')`. -/
theorem isIntegral_iff_mem_Rinf (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rinf Fq F) x ↔ IsIntegral (Oinf L) x := by
  constructor
  · intro hx
    letI := algInf h
    haveI := towerInf h
    refine isIntegral_of_forall_algebraMap (A := Rinf Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F']
    exact (algebraMap (Rinf Fq F) (Rinf L F') a).2
  · intro hx
    letI := algInf h
    haveI := towerInf h
    haveI := isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
    exact (Algebra.IsIntegral.isIntegral (R := Rinf Fq F) (⟨x, hx⟩ : Rinf L F')).algebraMap

end GenericC

section InfC

open PicDescent Places

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Residue fields of `Rinf(F)` at maximal ideals are finite, hence perfect. -/
theorem perfect_Rinf : ∀ (P : Ideal (Rinf Fq F)) [P.IsMaximal], PerfectField P.ResidueField := by
  intro P hP
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (not_isField_Rinf Fq F)
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  haveI := Places.FiniteQuot.finite (S := Rinf Fq F) a ha0
  haveI : Finite (Rinf Fq F ⧸ P) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))
  haveI : Finite P.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField P).2
  infer_instance

variable {Fq F} {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- Constant levels are unramified over `Rinf` too. -/
theorem Fc_mem_unramSet_inf (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    Fc Fq F (AlgebraicClosure F) m ∈ unramSet (Rinf Fq F) F := by
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))]
  exact constLevel_mem_unramSet (Rinf Fq F) (Nat.mul_pos he (NeZero.pos m))

/-- `π₁^geo` fixes the constant level `F_m`. -/
theorem fixed_of_mem_Fc (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    ∀ g ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), ∀ x : maxUnram (Rfin Fq F) F,
      (x : AlgebraicClosure F) ∈ Fc Fq F (AlgebraicClosure F) m → g x = x := by
  intro g hg x hx
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))] at hx
  rw [hq] at hg
  exact fixed_of_mem_constLevel he (Nat.mul_pos he (NeZero.pos m)) hx g hg

/-- **K5c MAIN (curves, boundary at infinity)**: for `α ∈ K_U^×` with `α ^ N = a ∈ F_m^×` (`α` in `rad π₁^geo`), the
Kummer class of `α` is parabolic iff `α` is unramified over `Rinf` iff `N ∣ ord_v a` at every infinite place `v` of
`F_m`. -/
theorem kclass_mem_curveH1par_iff_ord (hk : constField Fq F = ⊥) (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (m : ℕ) [NeZero m] {N : ℕ} [NeZero N] (hN : IsUnit (N : Rinf Fq F))
    {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
    (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
    {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a) :
    (kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ↔
        ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ∈ maxUnram (Rinf Fq F) F) ∧
      (kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ↔
        ∀ v : HeightOneSpectrum (Rinf (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m)),
          (N : ℤ) ∣ Places.ord v a) := by
  have hB : ∀ x : Fc Fq F (AlgebraicClosure F) m, IsIntegral (Rinf Fq F) x ↔
      x ∈ (algebraMap (Rinf (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m))
        (Fc Fq F (AlgebraicClosure F) m)).range := by
    intro x
    refine (isIntegral_iff_mem_Rinf (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) x).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact y.2
  have hmain := kclass_mem_curveH1par_iff (Rinf Fq F) hζ hζΓ D he hq hlift hDB
    (Fc_mem_unramSet hq he m) (Fc_mem_unramSet_inf hq he m) (perfect_Rinf Fq F) hN
    (fixed_of_mem_Fc hq he m) ha hB hα haα
  refine ⟨hmain.1, hmain.2.trans (forall_congr' fun v => ?_)⟩
  rw [Places.ord]
  exact dvd_neg.symm

end InfC

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_PicA =====
section

/-!
# S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`

Generic function field `F / Fq` (PicDescent setting), any `Ω` with `F ⊆ Ω`.
* `divN Fq N f`: the divisor `div(f) / N` (integer division of every order); `zsmul_divN` (`N • div(f)/N = div f` when
  `N` divides every order), `divN_pow` (`div(f^N)/N = div f`), `divN_mul`, `div_pow_eq`.
* `conormNN_divN`, `toBar_conNN` (level independence), `psiAt Ω hk N m a = [div(a)/N] ∈ Pic(X̄)`, `psiAt_algebraMap`,
  `psiAt_congr` (only the element of `Ω` matters), `psiAt_mul`, `nsmul_psiAt` (`N`-torsion), `psiAt_mem_PicBar0`.
* `PicBar0N Ω hk N = Pic⁰(X̄)[N]`; `ofBar_eq_toBar`, `exists_lev_toBar`; `exists_psiAt_eq` (every `N`-torsion class of
  `Pic(F_m)` is `[div(a)/N]`), `exists_of_psiAt_eq_zero` (`[div(a)/N] = 0` ⇒ `a / b ^ N` is a constant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open PicDescent Places ZetaSB
open scoped Polynomial

noncomputable section

section DivN

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq) in
/-- `div(f) / N`: integer division of every order by `N`. -/
def divN (N : ℕ) (f : F) : Divisor Fq F :=
  (Places.div f : Divisor Fq F).mapRange (fun z => z / (N : ℤ)) (by simp)

theorem divN_apply (N : ℕ) (f : F) (P : Place Fq F) : divN Fq N f P = P.ord f / N := by
  rw [divN, Finsupp.mapRange_apply, Places.div_apply]

/-- `N • (div(f) / N) = div f` when `N` divides every order of `f`. -/
theorem zsmul_divN {N : ℕ} {f : F} (h : ∀ P : Place Fq F, (N : ℤ) ∣ P.ord f) :
    (N : ℤ) • divN Fq N f = Places.div f := by
  ext P
  rw [Finsupp.smul_apply, smul_eq_mul, divN_apply, Places.div_apply, Int.mul_ediv_cancel' (h P)]

theorem ord_pow_place (P : Place Fq F) {f : F} (hf : f ≠ 0) (k : ℕ) : P.ord (f ^ k) = k * P.ord f := by
  induction k with
  | zero => rw [pow_zero, P.ord_one, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, P.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem div_pow_eq {f : F} (hf : f ≠ 0) (k : ℕ) :
    (Places.div (f ^ k) : Divisor Fq F) = (k : ℤ) • Places.div f := by
  ext P
  rw [Finsupp.smul_apply, smul_eq_mul, Places.div_apply, Places.div_apply, ord_pow_place P hf]

theorem divN_pow {N : ℕ} [NeZero N] {f : F} (hf : f ≠ 0) : divN Fq N (f ^ N) = Places.div f := by
  ext P
  rw [divN_apply, ord_pow_place P hf, Places.div_apply,
    Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.2 (NeZero.ne N))]

theorem divN_mul {N : ℕ} {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : ∀ P : Place Fq F, (N : ℤ) ∣ P.ord f) :
    divN Fq N (f * g) = divN Fq N f + divN Fq N g := by
  ext P
  rw [Finsupp.add_apply, divN_apply, divN_apply, divN_apply, P.ord_mul hf hg, Int.add_ediv_of_dvd_left (h P)]

end DivN

section Lev

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

theorem conormNN_divN {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (N : ℕ) (f : Fc Fq F Ω n) :
    conormNN Ω hk n n' (divN (Lc Fq Ω n) N f) =
      divN (Lc Fq Ω n') N (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω n') f) := by
  ext P
  rw [conormNN_apply, divN_apply, divN_apply, ord_contractNN]

/-- `toBar` is compatible with conorm (level independence). -/
theorem toBar_conNN {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    toBar Ω hk n' (conNN Ω hk n n' x) = toBar Ω hk n x := by
  have hle : n ≤ n' := Nat.le_of_dvd (NeZero.pos n') Fact.out
  have : Fact (n' ∣ lev n') := ⟨dvd_lev (NeZero.pos n') le_rfl⟩
  have : Fact (n ∣ lev n') := ⟨dvd_trans (Fact.out : n ∣ n') (dvd_lev (NeZero.pos n') le_rfl)⟩
  rw [toBar_eq hk n' le_rfl, toBar_eq hk n hle, conNN_trans]

variable (Ω) in
/-- `[div(a) / N] ∈ Pic(X̄)` for `a ∈ F_m`. -/
def psiAt (N m : ℕ) [NeZero m] (a : Fc Fq F Ω m) : PicBar Ω hk :=
  toBar Ω hk m (QuotientAddGroup.mk (divN (Lc Fq Ω m) N a))

theorem psiAt_algebraMap (N : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (a : Fc Fq F Ω n) :
    psiAt Ω hk N n' (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω n') a) = psiAt Ω hk N n a := by
  rw [psiAt, psiAt, ← conormNN_divN hk, ← conNN_mk, toBar_conNN]

/-- `psiAt` depends only on the element of `Ω`. -/
theorem psiAt_congr (N : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] (a : Fc Fq F Ω n) (a' : Fc Fq F Ω n')
    (h : (a : Ω) = a') : psiAt Ω hk N n a = psiAt Ω hk N n' a' := by
  have : NeZero (n * n') := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n')⟩
  have : Fact (n ∣ n * n') := ⟨dvd_mul_right n n'⟩
  have : Fact (n' ∣ n * n') := ⟨dvd_mul_left n' n⟩
  rw [← psiAt_algebraMap hk N (n' := n * n') a, ← psiAt_algebraMap hk N (n' := n * n') a']
  exact congrArg _ (Subtype.ext (by rw [coe_algebraMap_FF, coe_algebraMap_FF, h]))

theorem psiAt_mul {N m : ℕ} [NeZero m] {a b : Fc Fq F Ω m} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) :
    psiAt Ω hk N m (a * b) = psiAt Ω hk N m a + psiAt Ω hk N m b := by
  rw [psiAt, divN_mul ha hb h, QuotientAddGroup.mk_add, map_add]
  rfl

theorem nsmul_psiAt {N m : ℕ} [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) : N • psiAt Ω hk N m a = 0 := by
  have h0 : (QuotientAddGroup.mk (Places.div a : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) :
      Pic (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨a, ha, rfl⟩
  rw [psiAt, ← map_nsmul, ← QuotientAddGroup.mk_nsmul, ← natCast_zsmul, zsmul_divN h, h0, map_zero]

theorem psiAt_pow {N m : ℕ} [NeZero N] [NeZero m] {b : Fc Fq F Ω m} (hb : b ≠ 0) :
    psiAt Ω hk N m (b ^ N) = 0 := by
  have h0 : (QuotientAddGroup.mk (Places.div b : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) :
      Pic (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨b, hb, rfl⟩
  rw [psiAt, divN_pow hb, h0, map_zero]

theorem psiAt_mem_PicBar0 {N m : ℕ} [NeZero N] [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) : psiAt Ω hk N m a ∈ PicBar0 Ω hk := by
  rw [psiAt, toBar_mem_PicBar0, mem_Pic0, degPic_mk]
  have h1 := congrArg Divisor.deg (zsmul_divN h)
  rw [deg_zsmul, deg_div ha] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (NeZero.ne N))

variable (Ω) in
/-- `Pic⁰(X̄)[N]`. -/
def PicBar0N (N : ℕ) : AddSubgroup (PicBar Ω hk) where
  carrier := {z | z ∈ PicBar0 Ω hk ∧ N • z = 0}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by rw [nsmul_add, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, nsmul_zero N⟩
  neg_mem' := fun {x} hx => ⟨neg_mem hx.1, by rw [smul_neg, hx.2, neg_zero]⟩

theorem mem_PicBar0N (N : ℕ) (z : PicBar Ω hk) : z ∈ PicBar0N Ω hk N ↔ z ∈ PicBar0 Ω hk ∧ N • z = 0 := Iff.rfl

theorem ofBar_eq_toBar (j : ℕ) (y : PicL Fq F Ω j) : ofBar Ω hk j y = toBar Ω hk (lev j) y := by
  have : Fact (lev j ∣ lev (lev j)) := ⟨dvd_lev (NeZero.pos _) le_rfl⟩
  have hj : j ≤ lev j := by
    unfold lev
    exact (Nat.le_succ j).trans (Nat.self_le_factorial _)
  rw [toBar_apply hk (lev j) y, ← tr_apply hk hj]
  exact (AddCommGroup.DirectLimit.of_f hj y).symm

/-- Every class of `Pic(X̄)` comes from a finite level. -/
theorem exists_lev_toBar (z : PicBar Ω hk) : ∃ j : ℕ, ∃ y : PicL Fq F Ω j, toBar Ω hk (lev j) y = z :=
  AddCommGroup.DirectLimit.induction_on z fun j y => ⟨j, y, (ofBar_eq_toBar hk j y).symm⟩

/-- An `N`-torsion class of `Pic(F_m)` (in `Pic(X̄)`) is `[div(a) / N]` with `N ∣ div a`. -/
theorem exists_psiAt_eq {N m : ℕ} [NeZero N] [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m))
    (hx : N • toBar Ω hk m x = 0) : ∃ a : Fc Fq F Ω m, a ≠ 0 ∧
      (∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) ∧ psiAt Ω hk N m a = toBar Ω hk m x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← map_nsmul, ← QuotientAddGroup.mk_nsmul, ← map_zero (toBar Ω hk m)] at hx
  obtain ⟨a, ha, haD⟩ := (QuotientAddGroup.eq_zero_iff _).1 (toBar_injective hk m hx)
  have hord : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), P.ord a = N * D P := fun P => by
    rw [← Places.div_apply, haD, Finsupp.smul_apply, nsmul_eq_mul]
  have hD : divN (Lc Fq Ω m) N a = D := by
    ext P
    rw [divN_apply, hord, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.2 (NeZero.ne N))]
  exact ⟨a, ha, fun P => ⟨D P, hord P⟩, by rw [psiAt, hD]⟩

/-- `[div(a) / N] = 0` ⇒ `a = c · b ^ N` with `c` a constant. -/
theorem exists_of_psiAt_eq_zero {N m : ℕ} [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) (h0 : psiAt Ω hk N m a = 0) :
    ∃ b : Fc Fq F Ω m, b ≠ 0 ∧ ∃ c : Lc Fq Ω m, algebraMap (Lc Fq Ω m) (Fc Fq F Ω m) c = a / b ^ N := by
  rw [psiAt, ← map_zero (toBar Ω hk m)] at h0
  obtain ⟨b, hb, hbD⟩ := (QuotientAddGroup.eq_zero_iff _).1 (toBar_injective hk m h0)
  refine ⟨b, hb, ?_⟩
  have hdiv : (Places.div (a / b ^ N) : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := by
    rw [Places.div_div ha (pow_ne_zero _ hb), div_pow_eq hb, hbD, zsmul_divN h, sub_self]
  have hc := (Places.div_eq_zero_iff _ _ (div_ne_zero ha (pow_ne_zero _ hb))).1 hdiv
  rw [constField_Fc Fq F Ω hk m] at hc
  exact IntermediateField.mem_bot.1 hc

end Lev

end

end Kummer
end RamanujanPetersson


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

theorem pow_mod_eq_of_pow_eq_one {L : Type*} [Monoid L] {u : L} {M : ℕ} (hM : u ^ M = 1) (k : ℕ) :
    u ^ (k % M) = u ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k M]
  rw [pow_add, pow_mul, hM, one_pow, mul_one]

theorem coprime_pow_sub_one {r m : ℕ} (hr : 0 < r) (hm : 0 < m) : Nat.Coprime r (r ^ m - 1) := by
  have h1 : 1 ≤ r ^ m := Nat.one_le_pow _ _ hr
  have h2 : Nat.Coprime (r ^ m - 1) (r ^ m - 1 + 1) :=
    Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
  rw [Nat.sub_add_cancel h1] at h2
  exact (h2.coprime_dvd_right (dvd_pow_self r hm.ne')).symm

/-- An `N`-th root (`N` prime to `r`) of a nonzero `c` with `c ^ (r ^ m) = c` is a constant. -/
theorem isConst_of_pow_eq {L : Type} [Field L] {r N m : ℕ} [NeZero N] (hr : 1 < r) (hm : 0 < m)
    (hrN : Nat.Coprime r N) {c u : L} (hc : c ^ (r ^ m) = c) (hc0 : c ≠ 0) (hu : u ^ N = c) : IsConst r u := by
  have hQ : 1 ≤ r ^ m := Nat.one_le_pow _ _ (by omega)
  have hM : u ^ (N * (r ^ m - 1)) = 1 := by rw [pow_mul, hu, pow_pred_eq_one hQ hc hc0]
  have hcop : Nat.Coprime r (N * (r ^ m - 1)) := Nat.Coprime.mul_right hrN (coprime_pow_sub_one (by omega) hm)
  have hpos : 0 < N * (r ^ m - 1) :=
    Nat.mul_pos (NeZero.pos N) (by have := Nat.one_lt_pow hm.ne' hr; omega)
  refine ⟨Nat.totient (N * (r ^ m - 1)), Nat.totient_pos.2 hpos, ?_⟩
  have h := Nat.ModEq.pow_totient hcop
  unfold Nat.ModEq at h
  rw [← pow_mod_eq_of_pow_eq_one hM, h, pow_mod_eq_of_pow_eq_one hM, pow_one]

theorem coe_unit_ne_zero {A K : Type} [CommRing A] [Field K] [Algebra A K] (α : (maxUnram A K)ˣ) :
    ((α : maxUnram A K) : AlgebraicClosure K) ≠ 0 := by
  exact_mod_cast α.ne_zero

/-- Every `N`-th root of `α ^ N` (`α ∈ K_U`) lies in `K_U` (`μ_N ⊆ K_U`). -/
theorem mem_maxUnram_of_pow_eq {A K : Type} [CommRing A] [Field K] [Algebra A K] {N : ℕ} [NeZero N]
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) (α : (maxUnram A K)ˣ) {γ : AlgebraicClosure K}
    (hγ : γ ^ N = ((α : maxUnram A K) : AlgebraicClosure K) ^ N) : γ ∈ maxUnram A K := by
  have hα0 := coe_unit_ne_zero α
  have hζ' : IsPrimitiveRoot ((maxUnram A K).val ζ) N :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (maxUnram A K).val) Subtype.val_injective).2 hζ
  have h1 : (γ / ((α : maxUnram A K) : AlgebraicClosure K)) ^ N = 1 := by
    rw [div_pow, hγ, div_self (pow_ne_zero _ hα0)]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
  have hγ' : γ = (maxUnram A K).val ζ ^ i * ((α : maxUnram A K) : AlgebraicClosure K) := by
    rw [hi, div_mul_cancel₀ _ hα0]
  rw [hγ']
  exact mul_mem (pow_mem ζ.2 i) (α : maxUnram A K).2

theorem kclass_congr {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
    {Γ : Subgroup (E ≃ₐ[K] E)} {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) {α β : Eˣ}
    (h : α = β) (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) : kclass hζ hζΓ hα = kclass hζ hζΓ hβ := by
  subst h
  rfl

end Generic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

open Classical in
/-- **Ψ**: `α ↦ [div(α ^ N) / N] ∈ Pic(X̄)` at any constant level `F_m ∋ α ^ N` (`0` if there is none). -/
def Psi (N : ℕ) (α : (maxUnram (Rfin Fq F) F)ˣ) : PicBar (AlgebraicClosure F) hk :=
  if h : ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m then
    haveI : NeZero h.choose := ⟨h.choose_spec.1.ne'⟩
    psiAt (AlgebraicClosure F) hk N h.choose ⟨_, h.choose_spec.2⟩
  else 0

theorem Psi_eq {N m : ℕ} [NeZero m] (α : (maxUnram (Rfin Fq F) F)ˣ) (a : Fc Fq F (AlgebraicClosure F) m)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a) :
    Psi hk N α = psiAt (AlgebraicClosure F) hk N m a := by
  have h : ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m :=
    ⟨m, NeZero.pos m, by rw [haα]; exact a.2⟩
  have : NeZero h.choose := ⟨h.choose_spec.1.ne'⟩
  rw [Psi, dif_pos h]
  exact psiAt_congr hk N _ a haα

theorem Psi_of_mem_Fc {N m : ℕ} [NeZero N] [NeZero m] (α : (maxUnram (Rfin Fq F) F)ˣ)
    (b : Fc Fq F (AlgebraicClosure F) m) (hb : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) = b) :
    Psi hk N α = 0 := by
  have hb0 : b ≠ 0 := by
    have := coe_unit_ne_zero α
    rw [hb] at this
    exact_mod_cast this
  rw [Psi_eq hk α (b ^ N) (by rw [hb, SubmonoidClass.coe_pow]), psiAt_pow hk hb0]

theorem kFc_ne_zero {m : ℕ} {a : Fc Fq F (AlgebraicClosure F) m} {x : AlgebraicClosure F}
    (h : (a : AlgebraicClosure F) = x) (hx : x ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact hx (h.symm.trans (ZeroMemClass.coe_zero _))

section PsiMap

variable {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- `π₁^geo`-fixed elements of `K_U` lie in a constant level `F_m`. -/
theorem exists_Fc_of_fixed (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {x : maxUnram (Rfin Fq F) F}
    (hx : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ x = x) :
    ∃ m : ℕ, 0 < m ∧ (x : AlgebraicClosure F) ∈ Fc Fq F (AlgebraicClosure F) m := by
  rw [hq] at hx
  obtain ⟨k, hk0, hkx⟩ := exists_constLevel_of_fixed he hx
  exact ⟨k, hk0, by rw [Fc_eq_constLevel hq (Nat.mul_pos he hk0)]; exact hkx⟩

theorem exists_Fc_of_rad (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m := by
  obtain ⟨m, hm, h⟩ := exists_Fc_of_fixed hq he ((mem_rad _ _ α).1 hα)
  rw [SubmonoidClass.coe_pow] at h
  exact ⟨m, hm, h⟩

theorem Psi_eq_zero_of_mem_fixUnits (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} [NeZero N]
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ fixUnits (pi1geo (Rfin Fq F) F (Fintype.card Fq))) :
    Psi hk N α = 0 := by
  obtain ⟨m, hm, h⟩ := exists_Fc_of_fixed hq he ((mem_fixUnits _ α).1 hα)
  have : NeZero m := ⟨hm.ne'⟩
  exact Psi_of_mem_Fc hk α ⟨_, h⟩ rfl

variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} [NeZero N]
  (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

include hk hq he hNf hNi hDB hlift

/-- A parabolic radical: `N ∣ ord_P (α ^ N)` at every place `P` of a constant level containing `α ^ N`. -/
theorem dvd_ord_of_par (m : ℕ) [NeZero m] {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    ∀ P : Place (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m), (N : ℤ) ∣ P.ord a := by
  rintro (v | v)
  · exact (forall_dvd_ord_iff hk hq he m hNf ha).2
      (fun γ hγ => mem_maxUnram_of_pow_eq hζ α (hγ.trans haα.symm)) v
  · exact ((kclass_mem_curveH1par_iff_ord hk hq he m hNi hζ hζΓ D hDB hlift ha hα haα).2.1 hpar) v

end PsiMap

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Frob =====
section

/-!
# S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

* `geomFrobH1_mem_curveH1par`: the geometric Frobenius preserves `H¹_par`.
* `piBar_toBar`, `divN_frobF`, `psiAt_frobF`: the arithmetic Frobenius `π` on `Pic(X̄)` and `[div(a)/N]`.
* `frobLift_Fc`: an arithmetic Frobenius lift `φ ∈ π₁(U)` restricts to `frobF` on every constant level `F_m`.
* `Psi_frob`: `Ψ(φ α) = π Ψ(α)`.
* `exists_kummerPicEquiv_frob` (**K5e**): `Φ : H¹_par ≃+ Pic⁰(X̄)[N]` with `Φ[kchar α] = Ψ α` and
  `π (Φ (F x)) = q • Φ x` for the geometric Frobenius `F` (the `μ_N⁻¹` twist, review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

end Generic

section ParFrob

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ} {R0 : Type} [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)
  (D : BdryData A K q R0 S)

end ParFrob

section DivFrob

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

end DivFrob

section FrobPic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

end FrobPic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
theorem Fc_le_maxUnram (m : ℕ) [NeZero m] : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := by
  rw [maxUnram_eq_sSup]; exact le_sSup (Fc_mem_unramSet hq he m)

section PsiFrob

variable {N : ℕ} [NeZero N]

variable (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

end PsiFrob

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_Bridge =====
section

/-!
# S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)

* `tatePicN`: the CoreA Tate coordinates at level `n` as a map `(ℤ/l^n)^s → Pic⁰(X̄)[l^n]`; bijective when
  `A = Pic(X̄)[l^∞]` is divisible (CB1), and `π` acts by `M mod l^n` (`tatePic_frob`).
* `CoreBHyp`: Core B (CB1 + CB2) as an explicit `Prop`: `A` is `l`-divisible, and every CoreA Tate matrix of `π`
  has characteristic polynomial `Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`.
* `trace_of_picEquiv`: for any `ZMod (l^n)`-module `H` with an additive `Φ : H ≃ Pic⁰(X̄)[l^n]` such that
  `π (Φ (f x)) = q Φ x`, `Tr(f^m | H) = 1 + q^m - N_m` (via `exists_tateEquivN`, `coords_key`, `trace_pow_of_coords`).
* `trace_frobPar` (review R4): with the F-equivariant Kummer isomorphism `H¹_par ≃ Pic⁰(X̄)[l^n]` (S4-Kummer),
  `Tr(F^m | H¹_par(Ū, ℤ/l^n)) = 1 + q^m - N_m` for the geometric Frobenius `F`, all `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section LinAlg

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

end LinAlg

section Abstract

variable {H : Type*} [AddCommGroup H] {L : ℕ} [Module (ZMod L) H] {s : ℕ}

end Abstract

section Tate

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)
variable {l : ℕ} [Fact l.Prime] {k0 : ℕ}
  (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y) {s : ℕ}
  (b1 : Fin s → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)

/-- The level-`n` Tate coordinates, as a map into `Pic(X̄)`. -/
noncomputable def tatePic (n : ℕ) : (Fin s → ZMod (l ^ n)) →+ PicBar Ω hk :=
  (AddCommGroup.primaryComponent (PicBar Ω hk) l).subtype.comp
    (((smulHom (Aℓ Ω hk l) (l ^ k0)).range.subtype).comp (tateMap hdiv b1 hb1 n))

theorem tatePic_mem (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    tatePic hk hdiv b1 hb1 n cb ∈ PicBar0N Ω hk (l ^ n) := by
  refine ⟨primary_le_PicBar0 hk (Fact.out : l.Prime).ne_zero (tateMap hdiv b1 hb1 n cb : Aℓ Ω hk l).2, ?_⟩
  have h := congrArg (fun y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range => ((y : Aℓ Ω hk l) : PicBar Ω hk))
    (tateMap_smul_eq_zero hdiv b1 hb1 n cb)
  simpa [tatePic] using h

/-- Level-`n` Tate coordinates of `Pic⁰(X̄)[l^n]`. -/
noncomputable def tatePicN (n : ℕ) : (Fin s → ZMod (l ^ n)) →+ PicBar0N Ω hk (l ^ n) :=
  (tatePic hk hdiv b1 hb1 n).codRestrict _ (tatePic_mem hk hdiv b1 hb1 n)

theorem coe_tatePicN (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    (tatePicN hk hdiv b1 hb1 n cb : PicBar Ω hk) = tatePic hk hdiv b1 hb1 n cb := rfl

/-- With `A` divisible (`D = A`), the Tate coordinates give `(ℤ/l^n)^s ≅ Pic⁰(X̄)[l^n]`. -/
theorem tatePicN_bijective (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) (n : ℕ) :
    Function.Bijective (tatePicN hk hdiv b1 hb1 n) := by
  refine ⟨fun a b hab => hinj n ?_, fun z => ?_⟩
  · have h := congrArg (fun z : PicBar0N Ω hk (l ^ n) => (z : PicBar Ω hk)) hab
    exact Subtype.ext (Subtype.ext h)
  · obtain ⟨-, hzn⟩ : (z : PicBar Ω hk) ∈ PicBar0 Ω hk ∧ l ^ n • (z : PicBar Ω hk) = 0 := z.2
    have hA : (z : PicBar Ω hk) ∈ AddCommGroup.primaryComponent (PicBar Ω hk) l := ⟨n, hzn⟩
    have hy : (⟨z, hA⟩ : Aℓ Ω hk l) ∈ (smulHom (Aℓ Ω hk l) (l ^ k0)).range := htop ▸ AddSubgroup.mem_top _
    obtain ⟨cb, hcb⟩ := hsurj n ⟨⟨z, hA⟩, hy⟩ (Subtype.ext (Subtype.ext (by simpa using hzn)))
    refine ⟨cb, Subtype.ext ?_⟩
    rw [coe_tatePicN]
    simp only [tatePic, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, hcb]

end Tate

section Frob

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

end Frob

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Lift =====
section

/-!
# S4-CP4a, part f4: inertia lifting (`BdryLift`) holds

* `exists_mul_mem_inertia` (abstract, profinite): if `H` acts on `B` with invariants `A'` and `g₁` acts trivially on
  `A' / (P ∩ A')`, then some `g₁ h` (`h ∈ H`) lies in the inertia group of `P`.
* `exists_prime_comap_eq`: lying over along an injective integral algebra map.
* `bdryLift`: `BdryLift A K R0` for every chart ring `R0`: inertia groups of finite levels `L ≤ K_U` at nonzero primes
  are restrictions of inertia groups of boundary primes of the pro-chart.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section AbsLift

variable {G B A' : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CommRing A'] [Algebra A' B] [SMulCommClass H A' B] [Algebra.IsInvariant A' B H]
  [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

end AbsLift

section AbsLiftFix

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

end AbsLiftFix

section Concrete

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

theorem inclU_injective {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) :
    Function.Injective (inclU R0 hLU) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : proChart A K R0 => ((z : maxUnram A K) : AlgebraicClosure K)) h

end Concrete

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_JacRRFam_A =====
section

/-!
# Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)

The abstract repartition calculus of `RamanujanPetersson.RR` (lib/S3/RR_A, RR_B) counts with
`AddSubgroup.relIndex` over a FINITE field.  Here the counting layer is redone over an ARBITRARY
field `K` (for instance a non-perfect function field `K = k(V)`) with the `ℕ∞`-valued codimension
`cd H H' = dim_K H' / (H ∩ H')`.  The definitions of part A of S3 (`Data`, `ball`, `AD`, `adeles`,
`Fs`, `LD`, `ell`, `div`, `degD`) are reused unchanged.

Main results: the codimension calculus (`cd_add`, `cd_split`, `cd_comap`, `cd_map_of_injective`,
`cd_eq_zero_iff`, `cd_of_le_fd`, `fd_of_cd`), the axioms `Data.AxiomsK0` / `Data.AxiomsK`
(local index `cd (ball i n) (ball i (n+1)) = deg i`), and the global index computation
`cd_AD_le`, `finite_LDK`, `ell_sub_leK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero Module

namespace RamanujanPetersson.RR

/-! ### The codimension of two subspaces -/

section Codim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The codimension of `H ∩ H'` in `H'`, as an element of `ℕ∞` (`⊤` when infinite). -/
noncomputable def cd (H H' : Submodule K V) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (H' ⧸ H.comap H'.subtype))

theorem cd_inf_right (H H' : Submodule K V) : cd (H ⊓ H') H' = cd H H' := by
  unfold cd
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]

end Codim

/-! ### The axioms over an arbitrary field and the global index -/

namespace Data

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F] (d : Data K F ι)

variable {d}

end Data

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_PerfectCx_Z1Ex =====
section

/-!
# S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`

For a subgroup `Γ` of a topological group `G` and representations `ρ`, `σ` of `G`, an equivariant linear map
`q : M → N` induces `z1Map : Z¹(Γ, M) → Z¹(Γ, N)` (locally constant cocycles, the `S4-CurveCoh` convention).

* `H2Van ρ Γ K`: locally constant 2-cocycles with values in the submodule `K` are coboundaries of locally constant
  `K`-valued cochains (cochains on `Γ`, the `h2_eq_zero` shape);
* `z1Map_surjective`: if `q` is surjective and `H2Van` holds for `ker q`, then `z1Map` is surjective
  (lift a cocycle along a set-theoretic section, its coboundary lies in `ker q`, correct by a `ker q`-valued cochain);
* `H2All k G Γ l n`: `H² = 0` for every finite `lⁿ`-torsion representation with open kernel (the output shape of
  `h2_pi1geo_eq_zero` / `h2_closed_eq_zero`); `h2Van_of_all` passes it to subrepresentations, and
  `z1Map_surjective_of_all` is the exactness statement used for `E_Γ = Z¹(Γ; A)` and `E_s = Z¹(I_s; A)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

/-- `Γ` acts locally constantly on `M` through `ρ`. -/
def LcRep : Prop := ∀ m : M, IsLocallyConstant fun g : Γ => ρ g m

theorem toRep_val (K : Subrepresentation ρ) (g : G) (v : K.toSubmodule) :
    ((K.toRepresentation g v : K.toSubmodule) : M) = ρ g v := rfl

end

end PerfectCx
end RamanujanPetersson


end


