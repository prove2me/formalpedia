-- Prove2me | Definitions.Def_RPLib_S3_ZetaC
-- name    : RPLib_S3_ZetaC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:29:54.719668+00:00
-- url     : https://prove2.me/theorems/624da5e0-509f-456d-9c27-1a0a265e4828
-- title:
--   Weight-two Ramanujan-Petersson library: the power-series argument
-- statement:
--   The power-series argument.
--
--   * `powerSum_of_newton` (abstract): a sequence `a` with `a 0 = 1`, the Newton identity
--     `(k + 1) a_{k+1} = Σ_{j=0}^{k} b_{j+1} a_{k-j}` and the recurrence `a_{k+2} + Q a_k = (1 + Q) a_{k+1}` for
--     `k + 2 ≥ K` has `b_k = 1 + Q^k - Σ_i c_i^k` (`k ≥ 1`) for a multiset `c ⊆ ℂ` with at most `K - 1` elements.
--     Proof: `P := (1 - X)(1 - Q X) Σ a_k X^k` is a polynomial of degree `< K` with `P(0) = 1`, so
--     `P = Π (1 - c_i X)` over `ℂ`; compare the logarithmic derivatives `P' = P · G` (no logarithms, no inverses).
--   * `numPoints_powerSum`: for a function field with full constant field, with `δ = delta Fq F`,
--     `N_{δk} = δ (1 + q^{δk} - Σ_i c_i^k)` for all `k ≥ 1`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_ZetaB

/-!
# S3-ZetaSB, O5 part C: the power-series argument

* `powerSum_of_newton` (abstract): a sequence `a` with `a 0 = 1`, the Newton identity
  `(k + 1) a_{k+1} = Σ_{j=0}^{k} b_{j+1} a_{k-j}` and the recurrence `a_{k+2} + Q a_k = (1 + Q) a_{k+1}` for
  `k + 2 ≥ K` has `b_k = 1 + Q^k - Σ_i c_i^k` (`k ≥ 1`) for a multiset `c ⊆ ℂ` with at most `K - 1` elements.
  Proof: `P := (1 - X)(1 - Q X) Σ a_k X^k` is a polynomial of degree `< K` with `P(0) = 1`, so
  `P = Π (1 - c_i X)` over `ℂ`; compare the logarithmic derivatives `P' = P · G` (no logarithms, no inverses).
* `numPoints_powerSum`: for a function field with full constant field, with `δ = delta Fq F`,
  `N_{δk} = δ (1 + q^{δk} - Σ_i c_i^k)` for all `k ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.ZetaSB

section PS

open PowerSeries

/-- The power series `Σ_{i ≥ 0} (Σ_j c_j^{i+1}) X^i`. -/
noncomputable def psumSeries (c : Multiset ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => (c.map (· ^ (i + 1))).sum

theorem coeff_succ_one_sub_mul (r : ℂ) (f : PowerSeries ℂ) (n : ℕ) :
    coeff (n + 1) ((1 - C r * X) * f) = coeff (n + 1) f - r * coeff n f := by
  rw [show (1 - C r * X) * f = f - C r * (X * f) by ring, map_sub, coeff_C_mul, coeff_succ_X_mul]

theorem coeff_zero_one_sub_mul (r : ℂ) (f : PowerSeries ℂ) :
    coeff 0 ((1 - C r * X) * f) = coeff 0 f := by
  rw [show (1 - C r * X) * f = f - C r * (X * f) by ring, map_sub, coeff_C_mul, coeff_zero_X_mul, mul_zero,
    sub_zero]

theorem one_sub_mul_geom (r : ℂ) : (1 - C r * X) * PowerSeries.mk (fun i => r ^ (i + 1)) = C r := by
  ext n
  cases n with
  | zero => rw [coeff_zero_one_sub_mul, coeff_mk, coeff_zero_C, zero_add, pow_one]
  | succ n =>
    rw [coeff_succ_one_sub_mul, coeff_mk, coeff_mk, coeff_C, if_neg (Nat.succ_ne_zero n)]
    ring

theorem deriv_one_sub (r : ℂ) : derivative ℂ (1 - C r * X) = -C r := by
  rw [map_sub, Derivation.leibniz, derivative_X, derivative_C, Derivation.map_one_eq_zero, smul_zero, add_zero,
    smul_eq_mul, mul_one, zero_sub]

theorem psumSeries_zero : psumSeries 0 = 0 := by
  ext n
  simp [psumSeries]

theorem psumSeries_cons (r : ℂ) (c : Multiset ℂ) :
    psumSeries (r ::ₘ c) = PowerSeries.mk (fun i => r ^ (i + 1)) + psumSeries c := by
  ext n
  simp [psumSeries, coeff_mk]

/-- Logarithmic derivative of `Π (1 - c_i X)`. -/
theorem deriv_prod (c : Multiset ℂ) :
    derivative ℂ (c.map fun r => 1 - C r * X).prod =
      -((c.map fun r => 1 - C r * X).prod * psumSeries c) := by
  induction c using Multiset.induction_on with
  | empty => simp [psumSeries_zero, Derivation.map_one_eq_zero]
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, deriv_one_sub, smul_eq_mul, smul_eq_mul,
      psumSeries_cons]
    have hg := one_sub_mul_geom r
    linear_combination (c.map fun r => 1 - C r * X).prod * hg

theorem coe_prod_one_sub (c : Multiset ℂ) :
    (((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod : Polynomial ℂ) : PowerSeries ℂ) =
      (c.map fun r => 1 - C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul, ih, Multiset.map_cons, Multiset.prod_cons]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sub, map_one, map_mul,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.coe_X]

/-- Over `ℂ`, a polynomial with constant coefficient `1` is `Π (1 - c_i X)`. -/
theorem exists_factor (p : Polynomial ℂ) (hp : p.coeff 0 = 1) :
    ∃ c : Multiset ℂ, Multiset.card c = p.natDegree ∧
      p = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  have hroots : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hne : p ≠ 0 := by
    rintro rfl
    simp at hp
  have h0 : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr h
    subst h
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hp] at hr
    exact one_ne_zero hr
  refine ⟨p.roots.map (·⁻¹), by rw [Multiset.card_map, hroots], ?_⟩
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hX : ∀ r ∈ p.roots, (Polynomial.X - Polynomial.C r) =
      Polynomial.C (-r) * (1 - Polynomial.C r⁻¹ * Polynomial.X) := by
    intro r hr
    rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ (h0 r hr)]
    simp only [Polynomial.C_neg, Polynomial.C_1]
    ring
  rw [Multiset.map_congr rfl hX, Multiset.prod_map_mul] at hfac
  have hC : (p.roots.map fun r => Polynomial.C (-r)).prod = Polynomial.C (p.roots.map fun r => -r).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [hC] at hfac
  set R := (p.roots.map fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X).prod with hRdef
  have hR0 : R.coeff 0 = 1 := by
    rw [hRdef, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hlc : p.leadingCoeff * (p.roots.map fun r => -r).prod = 1 := by
    have h := congrArg (fun q : Polynomial ℂ => q.coeff 0) hfac
    simp only [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, hR0, hp, mul_one] at h
    exact h
  rw [Multiset.map_map]
  calc p = Polynomial.C p.leadingCoeff * (Polynomial.C (p.roots.map fun r => -r).prod * R) := hfac.symm
    _ = R := by rw [← mul_assoc, ← Polynomial.C_mul, hlc, Polynomial.C_1, one_mul]
    _ = _ := by rw [hRdef]; rfl

/-- **Abstract zeta lemma.** -/
theorem powerSum_of_newton (a b : ℕ → ℂ) (Q : ℂ) (K : ℕ) (hK : 1 ≤ K) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hrec : ∀ k : ℕ, K ≤ k + 2 → a (k + 2) + Q * a k = (1 + Q) * a (k + 1))
    (h1 : K ≤ 1 → a 1 = (1 + Q) * a 0) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ K - 1 ∧
      ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : PowerSeries ℂ, P = (1 - C 1 * X) * W := ⟨_, rfl⟩
  have hWc : ∀ n, coeff (n + 1) W = a (n + 1) - Q * a n := by
    intro n
    rw [hW, coeff_succ_one_sub_mul, hZ, coeff_mk, coeff_mk]
  have hW0 : coeff 0 W = a 0 := by rw [hW, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hP0 : coeff 0 P = 1 := by rw [hPdef, coeff_zero_one_sub_mul, hW0, ha0]
  have hPv : ∀ n, K ≤ n → coeff n P = 0 := by
    intro n hn
    rcases n with _ | _ | k
    · omega
    · rw [hPdef, coeff_succ_one_sub_mul, hWc, hW0, h1 hn]
      ring
    · have h : a (k + 1 + 1) + Q * a k = (1 + Q) * a (k + 1) := hrec k hn
      rw [hPdef, coeff_succ_one_sub_mul, hWc, hWc]
      linear_combination h
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set p := trunc (K' + 1) P with hpdef
  have hp : (p : PowerSeries ℂ) = P := by
    ext n
    rw [Polynomial.coeff_coe, hpdef, coeff_trunc]
    split_ifs with h
    · rfl
    · exact (hPv n (by omega)).symm
  have hpc0 : p.coeff 0 = 1 := by rw [hpdef, coeff_trunc, if_pos (Nat.succ_pos K'), hP0]
  obtain ⟨c, hcard, hpc⟩ := exists_factor p hpc0
  refine ⟨c, ?_, ?_⟩
  · rw [hcard, Nat.add_sub_cancel]
    exact Nat.lt_succ_iff.mp (natDegree_trunc_lt P K')
  have hPc : P = (c.map fun r => 1 - C r * X).prod := by
    rw [← hp, hpc, coe_prod_one_sub]
  have h2 : P = ((1 ::ₘ {Q} : Multiset ℂ).map fun r => 1 - C r * X).prod * Z := by
    rw [hPdef, hW, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton, Multiset.prod_singleton, mul_assoc]
  have hne : P ≠ 0 := by
    intro h
    rw [h, map_zero] at hP0
    exact zero_ne_one hP0
  have hd1 : derivative ℂ P = -(P * psumSeries c) := by rw [hPc, deriv_prod]
  have hd2 : derivative ℂ P = P * (G - psumSeries (1 ::ₘ {Q})) := by
    rw [h2, Derivation.leibniz, hdZ, deriv_prod, smul_eq_mul, smul_eq_mul]
    ring
  have hGeq : G - psumSeries (1 ::ₘ {Q}) = -psumSeries c := by
    apply mul_left_cancel₀ hne
    rw [← hd2, hd1]
    ring
  intro k
  have hk := congrArg (coeff k) hGeq
  rw [map_sub, map_neg, hG, coeff_mk] at hk
  simp only [psumSeries, coeff_mk, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, one_pow] at hk
  linear_combination hk

end PS

section Concrete

open Polynomial Places RR

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- `newton_delta` re-indexed over `range`. -/
theorem newton_delta' (k : ℕ) :
    delta Fq F * (k + 1) * numEff Fq F (delta Fq F * (k + 1)) =
      ∑ i ∈ Finset.range (k + 1), numPoints Fq F (delta Fq F * (i + 1)) * numEff Fq F (delta Fq F * (k - i)) := by
  rw [newton_delta]
  refine Finset.sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro j _
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [show j - 1 + 1 = j by omega, show k + 1 - j = k - (j - 1) by omega]

/-- **Point counts as power sums.** With `δ = delta Fq F` and full constant field, there is a multiset
`c ⊆ ℂ` with at most `K - 1` elements such that `N_{δk} = δ (1 + q^{δk} - Σ_i c_i^k)` for all `k ≥ 1`. -/
theorem numPoints_powerSum (hk : constField Fq F = ⊥) (K : ℕ) (hK : 1 ≤ K)
    (hKg : ∀ k : ℕ, K ≤ k + 2 → 2 * (genusF Fq F : ℤ) - 1 ≤ ((delta Fq F * k : ℕ) : ℤ))
    (h1 : K ≤ 1 → numEff Fq F (delta Fq F) = 1 + Fintype.card Fq ^ delta Fq F) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ K - 1 ∧ ∀ k : ℕ, 1 ≤ k →
      (numPoints Fq F (delta Fq F * k) : ℂ) =
        delta Fq F * (1 + (Fintype.card Fq : ℂ) ^ (delta Fq F * k) - (c.map (· ^ k)).sum) := by
  have hδ : (delta Fq F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (delta_pos Fq F).ne'
  obtain ⟨c, hc, hb⟩ := powerSum_of_newton (fun k => (numEff Fq F (delta Fq F * k) : ℂ))
    (fun j => (numPoints Fq F (delta Fq F * j) : ℂ) / delta Fq F) ((Fintype.card Fq : ℂ) ^ delta Fq F) K hK
    (by simp [numEff_zero])
    (by
      intro k
      have h := congrArg (Nat.cast : ℕ → ℂ) (newton_delta' Fq F k)
      push_cast at h
      rw [Finset.sum_congr rfl (fun j _ => div_mul_eq_mul_div _ _ _), ← Finset.sum_div, eq_div_iff hδ]
      linear_combination h)
    (by
      intro k hk2
      have h := congrArg (Int.cast : ℤ → ℂ) (numEff_rec hk (dvd_mul_right (delta Fq F) k) (hKg k hk2))
      push_cast at h
      rw [show delta Fq F * (k + 2) = delta Fq F * k + 2 * delta Fq F by ring,
        show delta Fq F * (k + 1) = delta Fq F * k + delta Fq F by ring]
      linear_combination h)
    (by
      intro hK1
      simp only [mul_one, mul_zero, numEff_zero, h1 hK1]
      push_cast
      ring)
  refine ⟨c, hc, fun k hk1 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := hb k
  rw [div_eq_iff hδ] at h
  rw [h, pow_mul]
  ring

end Concrete

end RamanujanPetersson.ZetaSB


