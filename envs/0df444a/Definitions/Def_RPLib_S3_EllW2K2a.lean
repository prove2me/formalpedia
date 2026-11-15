-- Prove2me | Definitions.Def_RPLib_S3_EllW2K2a
-- name    : RPLib_S3_EllW2K2a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:26.748563+00:00
-- url     : https://prove2.me/theorems/5ff381e5-e4ae-4afe-afb5-764a68aa96c4
-- title:
--   The Eichler-Selberg trace formula in weight two: generic tools for the Fourier coefficients of `WcF`
-- statement:
--   Generic tools for the Fourier coefficients of `WcF`.
--
--   * `sum_range_mul_of_periodic`: `Σ_{a < C K} G a = K Σ_{a < C} G a` for `C`-periodic `G`.
--   * `liftVal`, `liftVal_eq`, `norm_liftVal_le`: the value of `lam` at a lift satisfying `P`.
--   * **`sum_factor`**: a double sum over `X ≅ XA × XB` whose condition, weight and character split
--     (the weight depending only on the `XA`-coordinates) factors as a product; `norm_sum_factor_le`.
--   * `sum_ite_isUnit`, **`sum_hyperbola_eq_kl`**: `Σ_{x(y-x) = n} e(m y / B) = S(m, m n; B)` for a unit `n`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_KloostermanA

/-!
# S3-ES-Wt2 (O6, file K2a): generic tools for the Fourier coefficients of `WcF`

* `sum_range_mul_of_periodic`: `Σ_{a < C K} G a = K Σ_{a < C} G a` for `C`-periodic `G`.
* `liftVal`, `liftVal_eq`, `norm_liftVal_le`: the value of `lam` at a lift satisfying `P`.
* **`sum_factor`**: a double sum over `X ≅ XA × XB` whose condition, weight and character split
  (the weight depending only on the `XA`-coordinates) factors as a product; `norm_sum_factor_le`.
* `sum_ite_isUnit`, **`sum_hyperbola_eq_kl`**: `Σ_{x(y-x) = n} e(m y / B) = S(m, m n; B)` for a unit `n`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

lemma sum_range_mul_of_periodic {G : ℕ → ℂ} {C : ℕ} (hG : ∀ a, G (a + C) = G a) (K : ℕ) :
    ∑ a ∈ range (C * K), G a = K * ∑ a ∈ range C, G a := by
  have hGk : ∀ k a, G (C * k + a) = G a := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih => intro a; rw [show C * (k + 1) + a = (C * k + a) + C by ring, hG, ih]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show C * (K + 1) = C * K + C by ring, Finset.sum_range_add, ih]
    simp only [hGk]; push_cast; ring

section Factor

variable {X XA XB : Type*} [Fintype X] [Fintype XA] [Fintype XB]

open Classical in
/-- The value of `lam` at some lift satisfying `P`, if one exists. -/
def liftVal (πA : X → XA) (P : X → X → Prop) (lam : X → X → ℂ) (x1 y1 : XA) : ℂ :=
  if h : ∃ p : X × X, πA p.1 = x1 ∧ πA p.2 = y1 ∧ P p.1 p.2 then lam h.choose.1 h.choose.2 else 0

omit [Fintype XA] in
lemma norm_liftVal_le (πA : X → XA) (P : X → X → Prop) (lam : X → X → ℂ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖lam x y‖ ≤ L) (x1 y1 : XA) : ‖liftVal πA P lam x1 y1‖ ≤ L := by
  unfold liftVal
  split_ifs
  · exact hL _ _
  · simpa using hL0

omit [Fintype XA] in
lemma liftVal_eq (πA : X → XA) (P : X → X → Prop) (lam : X → X → ℂ)
    (hlam : ∀ x y x' y', P x y → P x' y' → πA x = πA x' → πA y = πA y' → lam x y = lam x' y')
    {x y : X} (hP : P x y) : liftVal πA P lam (πA x) (πA y) = lam x y := by
  have h : ∃ p : X × X, πA p.1 = πA x ∧ πA p.2 = πA y ∧ P p.1 p.2 := ⟨(x, y), rfl, rfl, hP⟩
  unfold liftVal
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := h.choose_spec
  exact hlam _ _ _ _ h3 hP h1 h2

lemma sum_sep (πA : X → XA) (πB : X → XB) (hbij : Function.Bijective fun x => (πA x, πB x))
    (a : XA → XA → ℂ) (b : XB → XB → ℂ) :
    ∑ x, ∑ y, a (πA x) (πA y) * b (πB x) (πB y) = (∑ x1, ∑ y1, a x1 y1) * (∑ x2, ∑ y2, b x2 y2) := by
  have hsum : ∀ g : XA × XB → ℂ, ∑ x, g (πA x, πB x) = ∑ p : XA × XB, g p :=
    fun g => Fintype.sum_bijective _ hbij _ _ (fun x => rfl)
  calc ∑ x, ∑ y, a (πA x) (πA y) * b (πB x) (πB y)
      = ∑ x, ∑ p : XA × XB, a (πA x) p.1 * b (πB x) p.2 :=
        Finset.sum_congr rfl fun x _ => hsum (fun p => a (πA x) p.1 * b (πB x) p.2)
    _ = ∑ p : XA × XB, ∑ p' : XA × XB, a p.1 p'.1 * b p.2 p'.2 :=
        hsum (fun p => ∑ p' : XA × XB, a p.1 p'.1 * b p.2 p'.2)
    _ = (∑ x1, ∑ y1, a x1 y1) * (∑ x2, ∑ y2, b x2 y2) := by
        rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **CRT factorization** of a double sum. -/
theorem sum_factor (πA : X → XA) (πB : X → XB) (hbij : Function.Bijective fun x => (πA x, πB x))
    (P : X → X → Prop) [DecidableRel P] (PA : XA → XA → Prop) [DecidableRel PA]
    (PB : XB → XB → Prop) [DecidableRel PB]
    (hP : ∀ x y, P x y ↔ PA (πA x) (πA y) ∧ PB (πB x) (πB y)) (lam : X → X → ℂ)
    (hlam : ∀ x y x' y', P x y → P x' y' → πA x = πA x' → πA y = πA y' → lam x y = lam x' y')
    (ψ : X → ℂ) (ψA : XA → ℂ) (ψB : XB → ℂ) (hψ : ∀ y, ψ y = ψA (πA y) * ψB (πB y)) :
    ∑ x, ∑ y, (if P x y then lam x y * ψ y else 0) =
      (∑ x1, ∑ y1, (if PA x1 y1 then liftVal πA P lam x1 y1 * ψA y1 else 0)) *
        (∑ x2, ∑ y2, (if PB x2 y2 then ψB y2 else 0)) := by
  rw [← sum_sep πA πB hbij]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : P x y
  · have h' := (hP x y).1 h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, liftVal_eq πA P lam hlam h, hψ]; ring
  · rw [if_neg h]
    by_cases hA : PA (πA x) (πA y)
    · have hB : ¬ PB (πB x) (πB y) := fun hB => h ((hP x y).2 ⟨hA, hB⟩)
      rw [if_neg hB, mul_zero]
    · rw [if_neg hA, zero_mul]

theorem norm_sum_factor_le (πA : X → XA) (πB : X → XB)
    (hbij : Function.Bijective fun x => (πA x, πB x))
    (P : X → X → Prop) [DecidableRel P] (PA : XA → XA → Prop) [DecidableRel PA]
    (PB : XB → XB → Prop) [DecidableRel PB]
    (hP : ∀ x y, P x y ↔ PA (πA x) (πA y) ∧ PB (πB x) (πB y)) (lam : X → X → ℂ)
    (hlam : ∀ x y x' y', P x y → P x' y' → πA x = πA x' → πA y = πA y' → lam x y = lam x' y')
    (ψ : X → ℂ) (ψA : XA → ℂ) (ψB : XB → ℂ) (hψ : ∀ y, ψ y = ψA (πA y) * ψB (πB y))
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x y, ‖lam x y‖ ≤ L) (hψA : ∀ y, ‖ψA y‖ = 1) :
    ‖∑ x, ∑ y, (if P x y then lam x y * ψ y else 0)‖ ≤
      L * ((Finset.univ.filter fun p : XA × XA => PA p.1 p.2).card : ℝ) *
        ‖∑ x2, ∑ y2, (if PB x2 y2 then ψB y2 else 0)‖ := by
  rw [sum_factor πA πB hbij P PA PB hP lam hlam ψ ψA ψB hψ, norm_mul]
  have h1 : ‖∑ x1, ∑ y1, (if PA x1 y1 then liftVal πA P lam x1 y1 * ψA y1 else 0)‖ ≤
      ∑ p : XA × XA, (if PA p.1 p.2 then L else 0) := by
    rw [Fintype.sum_prod_type]
    dsimp only
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x1 _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y1 _ => ?_))
    split_ifs
    · rw [norm_mul, hψA, mul_one]; exact norm_liftVal_le πA P lam hL0 hL x1 y1
    · simp
  have h2 : ∑ p : XA × XA, (if PA p.1 p.2 then L else 0) =
      L * ((Finset.univ.filter fun p : XA × XA => PA p.1 p.2).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [← h2]
  gcongr

end Factor

section Hyperbola

open Classical in
lemma sum_ite_isUnit {B : ℕ} [NeZero B] (g : ZMod B → ℂ) :
    ∑ x : ZMod B, (if IsUnit x then g x else 0) = ∑ u : (ZMod B)ˣ, g u := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun (u : (ZMod B)ˣ) _ => (u : ZMod B)) (fun u _ => ?_)
    (fun u _ v _ h => Units.ext h) ?_ (fun u _ => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u.isUnit⟩
  · intro y hy
    have hy' : IsUnit y := (Finset.mem_filter.mp hy).2
    exact ⟨hy'.unit, Finset.mem_univ _, rfl⟩

open Classical in
/-- **The modular hyperbola gives a Kloosterman sum.** -/
theorem sum_hyperbola_eq_kl {B : ℕ} [NeZero B] {n : ZMod B} (hn : IsUnit n) (m : ZMod B) :
    ∑ x : ZMod B, ∑ y : ZMod B, (if x * (y - x) = n then (ZMod.stdAddChar (m * y) : ℂ) else 0) =
      KL.kl B m (m * n) := by
  have inner : ∀ x : ZMod B,
      ∑ y : ZMod B, (if x * (y - x) = n then (ZMod.stdAddChar (m * y) : ℂ) else 0) =
        if IsUnit x then (ZMod.stdAddChar (m * x + m * n * x⁻¹) : ℂ) else 0 := by
    intro x
    by_cases hx : IsUnit x
    · rw [if_pos hx]
      have hinv : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hx
      have e : ∀ y, (x * (y - x) = n) ↔ (y = x + x⁻¹ * n) := by
        intro y
        constructor
        · intro h; linear_combination x⁻¹ * h - (y - x) * hinv
        · intro h; rw [h]; linear_combination n * hinv
      simp_rw [e]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1; ring
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => if_neg fun h => hx ?_
      rw [← h] at hn
      exact isUnit_of_mul_isUnit_left hn
  simp_rw [inner]
  rw [sum_ite_isUnit]
  rfl

end Hyperbola

end RamanujanPetersson.EllW2


