-- Prove2me | Definitions.Def_RPLib_S4_PicDescentA
-- name    : RPLib_S4_PicDescentA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:02:01.70045+00:00
-- url     : https://prove2.me/theorems/8c26048e-f149-4a4b-ac08-96fe602bcab8
-- title:
--   The divisor class group $\mathrm{Pic}^0$ of a function field and the class number $h = L(1)$
-- statement:
--   For a function field $F/\mathbb{F}_q$ with full constant field, the file defines $\mathrm{Pic}(F) = \mathrm{Div}(F)/\mathrm{Princ}(F)$, the degree map and $\mathrm{Pic}^0(F)$ its kernel. It proves F. K. Schmidt's theorem that there is a divisor of degree $1$, that $\mathrm{Pic}^0$ is finite with $h = \#\mathrm{Pic}^0$ equal to the number of classes of any degree $N \ge 2g - 1$, that $A_N (q - 1) = h (q^{N + 1 - g} - 1)$, and that for every multiset $(c_i)$ of complex numbers with $N_m = 1 + q^m - \sum_i c_i^m$ for all $m \ge 1$ $$h = \#\mathrm{Pic}^0(F) = \prod_i (1 - c_i),$$ i.e. $h = L(1)$, together with the shape of the zeta function ($\#\{c_i\} \le 2g$, $|c_i| \le \sqrt q$).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Chapter 5; M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 5

import Definitions.Def_RPLib_S3_HasseWeilB

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

/-- Uniqueness for the linear differential equation `W' = W · H` over `ℂ`. -/
theorem eq_of_derivative_eq_mul (W1 W2 H : PowerSeries ℂ) (h1 : derivative ℂ W1 = W1 * H)
    (h2 : derivative ℂ W2 = W2 * H) (h0 : coeff 0 W1 = coeff 0 W2) : W1 = W2 := by
  obtain ⟨D, hD⟩ : ∃ D : PowerSeries ℂ, D = W1 - W2 := ⟨_, rfl⟩
  have hDd : derivative ℂ D = D * H := by
    rw [hD, map_sub, h1, h2]
    ring
  have hc : ∀ n, coeff n D = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [hD, map_sub, h0, sub_self]
      · have h := congrArg (coeff n) hDd
        rw [coeff_derivative, coeff_mul, Finset.sum_eq_zero (fun p hp => by
          rw [ih p.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega), zero_mul])] at h
        have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        exact (mul_eq_zero.mp h).resolve_right hn
  have : D = 0 := PowerSeries.ext fun n => by rw [hc n, map_zero]
  rw [hD] at this
  exact sub_eq_zero.mp this

theorem natDegree_prod_one_sub_le (c : Multiset ℂ) :
    (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod.natDegree ≤ Multiset.card c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (1 - Polynomial.C r * Polynomial.X).natDegree ≤ 1 := by compute_degree
    omega

theorem coeff_zero_prod_one_sub (c : Multiset ℂ) :
    coeff 0 ((c.map fun r => 1 - C r * X).prod : PowerSeries ℂ) = 1 := by
  rw [← coe_prod_one_sub, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_multiset_prod, Multiset.map_map]
  simp

/-- **Abstract class-number lemma.** Let `a 0 = 1`, `(k+1) a_{k+1} = Σ_{j ≤ k} b_{j+1} a_{k-j}` (Newton),
`b_k = 1 + Q^k - Σ_i c_i^k` for `k ≥ 1`, and `a_{n+1} - Q a_n = h` for `n ≥ M`. Then `Π_i (1 - c_i) = h`. -/
theorem prod_eq_of_newton (a b : ℕ → ℂ) (Q h : ℂ) (c : Multiset ℂ) (M : ℕ) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hb : ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum)
    (hh : ∀ n : ℕ, M ≤ n → a (n + 1) - Q * a n = h) :
    (c.map fun z => 1 - z).prod = h := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  have hG' : G = PowerSeries.mk (fun i => (1 : ℂ) ^ (i + 1)) + PowerSeries.mk (fun i => Q ^ (i + 1)) -
      psumSeries c := by
    ext n
    simp only [hG, psumSeries, map_add, map_sub, coeff_mk, hb, one_pow]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℂ, V = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C 1 * X) * V := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : PowerSeries ℂ, P = (c.map fun r => 1 - C r * X).prod := ⟨_, rfl⟩
  have hWd : derivative ℂ W = W * -psumSeries c := by
    have g1 := one_sub_mul_geom 1
    have gQ := one_sub_mul_geom Q
    rw [hW, hV, Derivation.leibniz, Derivation.leibniz, hdZ, deriv_one_sub, deriv_one_sub, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hG']
    linear_combination ((1 - C Q * X) * Z) * g1 + ((1 - C 1 * X) * Z) * gQ
  have hPd : derivative ℂ P = P * -psumSeries c := by
    rw [hP, deriv_prod]
    ring
  have hV0 : coeff 0 V = a 0 := by rw [hV, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hW0 : coeff 0 W = 1 := by rw [hW, coeff_zero_one_sub_mul, hV0, ha0]
  have hWP : W = P := eq_of_derivative_eq_mul W P _ hWd hPd (by rw [hW0, hP, coeff_zero_prod_one_sub])
  have hVs : ∀ n, coeff (n + 1) V = a (n + 1) - Q * a n := by
    intro n
    rw [hV, coeff_succ_one_sub_mul, hZ, coeff_mk, coeff_mk]
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1), coeff i W = coeff n V := by
    intro n
    induction n with
    | zero => rw [Finset.sum_range_one, hW, coeff_zero_one_sub_mul]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hW, coeff_succ_one_sub_mul]
      ring
  set p : Polynomial ℂ := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  have hpP : (p : PowerSeries ℂ) = P := by rw [hpdef, coe_prod_one_sub, hP]
  have hev : (c.map fun z => 1 - z).prod = p.eval 1 := by
    rw [hpdef, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp
  set N := M + Multiset.card c with hN
  have hlt : p.natDegree < N + 1 + 1 := by
    have := natDegree_prod_one_sub_le c
    rw [← hpdef] at this
    omega
  rw [hev, Polynomial.eval_eq_sum_range' hlt]
  have hcoef : ∀ i, p.coeff i * (1 : ℂ) ^ i = coeff i W := by
    intro i
    rw [one_pow, mul_one, hWP, ← hpP, Polynomial.coeff_coe]
  rw [Finset.sum_congr rfl fun i _ => hcoef i, hsum, hVs]
  exact hh N (by omega)

end PS

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The divisor class group `Pic(F) = Div(F) / Princ(F)`. -/
abbrev Pic : Type _ := Divisor Fq F ⧸ princ Fq F

/-- The degree of a divisor class. -/
noncomputable def degPic : Pic Fq F →+ ℤ :=
  QuotientAddGroup.lift (princ Fq F) (degHom Fq F) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact deg_div hf)

theorem degPic_mk (D : Divisor Fq F) : degPic Fq F (QuotientAddGroup.mk D) = Divisor.deg D := rfl

/-- `Pic⁰(F)`: the divisor classes of degree `0`. -/
noncomputable def Pic0 : AddSubgroup (Pic Fq F) := (degPic Fq F).ker

theorem mem_Pic0 {x : Pic Fq F} : x ∈ Pic0 Fq F ↔ degPic Fq F x = 0 := AddMonoidHom.mem_ker

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


