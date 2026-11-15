-- Prove2me | Definitions.Def_RPLib_S3_EllW2G
-- name    : RPLib_S3_EllW2G
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:28:36.300197+00:00
-- url     : https://prove2.me/theorems/9e2475aa-c49d-4048-af9e-ec8bf105a891
-- title:
--   The Eichler-Selberg trace formula in weight two: `Σ N(g)⁻¹` over split and parabolic matrices of determinant `n`
-- statement:
--   `Σ N(g)⁻¹` over split and parabolic matrices of determinant `n`.
--
--   `IsSP g` : the discriminant `tr² - 4 det` is a square. **`summable_SP`**: for `n > 0`,
--   `Σ_{det g = n, IsSP g} N(g)⁻¹ < ∞` (`N` = sum of squares of the entries, `Eg 2 g = N(g)⁻¹`).
--   Route: `c = 0` matrices inject into `(a, b)`; for `c ≠ 0`, `e = d - a` satisfies `c ∣ (r - e)(r + e)`,
--   `c₁ = gcd(c, r - e)`, `c₂ = |c| / c₁ ∣ r + e`, the admissible `e` lie in one class mod `lcm(c₁, c₂)`, and
--   `Σ_{c₁, c₂} lcm(c₁, c₂)⁻² < ∞`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_HypParT
import Definitions.Def_RPLib_S3_GSA

/-!
# S3-ES-Wt2 (O6, part G): `Σ N(g)⁻¹` over split and parabolic matrices of determinant `n`

`IsSP g` : the discriminant `tr² - 4 det` is a square. **`summable_SP`**: for `n > 0`,
`Σ_{det g = n, IsSP g} N(g)⁻¹ < ∞` (`N` = sum of squares of the entries, `Eg 2 g = N(g)⁻¹`).
Route: `c = 0` matrices inject into `(a, b)`; for `c ≠ 0`, `e = d - a` satisfies `c ∣ (r - e)(r + e)`,
`c₁ = gcd(c, r - e)`, `c₂ = |c| / c₁ ∣ r + e`, the admissible `e` lie in one class mod `lcm(c₁, c₂)`, and
`Σ_{c₁, c₂} lcm(c₁, c₂)⁻² < ∞`.
-/

open Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.HypPar

/-- The discriminant `tr² - 4 det` is a square. -/
def IsSP (g : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ r : ℤ, (g 0 0 + g 1 1) ^ 2 - 4 * g.det = r ^ 2

lemma Eg_two (g : Matrix (Fin 2) (Fin 2) ℤ) : Eg 2 g = (N g)⁻¹ := by
  have h0 : 0 ≤ N g := by unfold N; positivity
  rw [Eg, Real.sq_sqrt h0]

/-! ## Part 1: `Σ lcm(c₁, c₂)⁻²` -/

lemma summable_inv_sq_nat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
  Real.summable_nat_pow_inv.2 one_lt_two

lemma lcm_eq_mul (a b : ℕ) (h : 0 < Nat.gcd a b) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have ha : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have key := Nat.gcd_mul_lcm a b
  apply Nat.eq_of_mul_eq_mul_left h
  rw [key]
  calc a * b = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [ha, hb]
    _ = _ := by ring

lemma summable_inv_lcm_sq : Summable (fun p : ℕ × ℕ => ((Nat.lcm p.1 p.2 : ℝ) ^ 2)⁻¹) := by
  set h : ℕ × ℕ × ℕ → ℝ := fun x => ((x.1 : ℝ) ^ 2)⁻¹ * (((x.2.1 : ℝ) ^ 2)⁻¹ * ((x.2.2 : ℝ) ^ 2)⁻¹)
    with hh
  have hs : Summable h := summable_inv_sq_nat.mul_of_nonneg
    (summable_inv_sq_nat.mul_of_nonneg summable_inv_sq_nat (fun _ => by positivity) (fun _ => by positivity))
    (fun _ => by positivity) (fun _ => by positivity)
  set i : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    with hi_def
  have hi : Function.Injective i := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [hi_def, Prod.mk.injEq] at hab
    obtain ⟨h1, h2, h3⟩ := hab
    rcases Nat.eq_zero_or_pos (Nat.gcd a b) with h0 | h0
    · have e1 := Nat.gcd_eq_zero_iff.1 h0
      have e2 := Nat.gcd_eq_zero_iff.1 (h1.symm.trans h0)
      rw [e1.1, e1.2, e2.1, e2.2]
    · have ha : a = a' := by
        calc a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
          _ = Nat.gcd a' b' * (a' / Nat.gcd a' b') := by rw [h2, h1]
          _ = a' := Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')
      have hb : b = b' := by
        calc b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
          _ = Nat.gcd a' b' * (b' / Nat.gcd a' b') := by rw [h3, h1]
          _ = b' := Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')
      rw [ha, hb]
  refine (hs.comp_injective hi).of_nonneg_of_le (fun _ => by positivity) (fun p => ?_)
  rcases Nat.eq_zero_or_pos (Nat.gcd p.1 p.2) with h0 | h0
  · have e1 := Nat.gcd_eq_zero_iff.1 h0
    have hz : Nat.lcm p.1 p.2 = 0 := by rw [e1.1, Nat.lcm_zero_left]
    calc (((Nat.lcm p.1 p.2 : ℕ) : ℝ) ^ 2)⁻¹ = 0 := by rw [hz]; simp
      _ ≤ (h ∘ i) p := by simp only [Function.comp_apply, hh]; positivity
  · refine le_of_eq ?_
    simp only [Function.comp_apply, hi_def, hh]
    rw [lcm_eq_mul _ _ h0, Nat.cast_mul, Nat.cast_mul, mul_pow, mul_pow, mul_inv, mul_inv, mul_assoc]

/-! ## Part 2: one residue class modulo `lcm(c₁, c₂)` -/

/-- `K₀ = Σ_{q ∈ ℤ} (1 + q²)⁻¹`. -/
def K0 : ℝ := ∑' q : ℤ, (1 + (q : ℝ) ^ 2)⁻¹

lemma K0_nonneg : 0 ≤ K0 := tsum_nonneg fun _ => by positivity

lemma floor_bound {L : ℤ} (hL : 0 < L) (e : ℤ) :
    ((L : ℝ) ^ 2) * (1 + ((e / L : ℤ) : ℝ) ^ 2) ≤ 5 * ((L : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
  have h1 : e / L * L ≤ e := Int.ediv_mul_le e hL.ne'
  have h2 : e < (e / L + 1) * L := Int.lt_ediv_add_one_mul_self e hL
  set q := e / L
  have h1' : (q : ℝ) * L ≤ e := by exact_mod_cast h1
  have h2' : (e : ℝ) < ((q : ℝ) + 1) * L := by exact_mod_cast h2
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rcases le_or_gt 0 q with hq | hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    have h0 : 0 ≤ (q : ℝ) * L := mul_nonneg hq' hL'.le
    have h3 : ((q : ℝ) * L) ^ 2 ≤ (e : ℝ) ^ 2 := by
      nlinarith [mul_le_mul h1' h1' h0 (h0.trans h1')]
    nlinarith [sq_nonneg (e : ℝ)]
  · have hq' : (q : ℝ) ≤ -1 := by exact_mod_cast (by omega : q ≤ -1)
    have h4 : ((q : ℝ) + 1) * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hL'.le
    have h3 : (((q : ℝ) + 1) * L) ^ 2 ≤ (e : ℝ) ^ 2 := by
      nlinarith [mul_le_mul (show -(((q : ℝ) + 1) * L) ≤ -(e : ℝ) by linarith)
        (show -(((q : ℝ) + 1) * L) ≤ -(e : ℝ) by linarith) (by linarith) (by linarith)]
    have hpoly : 0 ≤ 4 * (q : ℝ) ^ 2 + 10 * q + 9 := by nlinarith [sq_nonneg (2 * (q : ℝ) + 5 / 2)]
    nlinarith [mul_nonneg (sq_nonneg (L : ℝ)) hpoly]

/-- **Key count**: the `e` with `c₁ ∣ r - e`, `c₂ ∣ r + e` lie in one class mod `L = lcm(c₁, c₂)`. -/
lemma coset_sum (r : ℤ) {c1 c2 : ℕ} (h1 : 1 ≤ c1) (h2 : 1 ≤ c2) :
    Summable ({e : ℤ | (c1 : ℤ) ∣ r - e ∧ (c2 : ℤ) ∣ r + e}.indicator
        (fun e : ℤ => (((c1 * c2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹)) ∧
    ∑' e : ℤ, {e : ℤ | (c1 : ℤ) ∣ r - e ∧ (c2 : ℤ) ∣ r + e}.indicator
        (fun e : ℤ => (((c1 * c2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹) e ≤
      5 * K0 * ((Nat.lcm c1 c2 : ℝ) ^ 2)⁻¹ := by
  set A := {e : ℤ | (c1 : ℤ) ∣ r - e ∧ (c2 : ℤ) ∣ r + e} with hA
  set f0 : ℤ → ℝ := fun e => (((c1 * c2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹ with hf0
  set L : ℕ := Nat.lcm c1 c2 with hL
  have hLpos : 0 < L := Nat.lcm_pos h1 h2
  have hLP : L ≤ c1 * c2 := Nat.le_of_dvd (Nat.mul_pos h1 h2) (Nat.lcm_dvd_mul c1 c2)
  have hP1 : (1 : ℝ) ≤ ((c1 * c2 : ℕ) : ℝ) := Nat.one_le_cast.2 (Nat.mul_pos h1 h2)
  have hsum0 : Summable fun e : ℤ => (1 + (e : ℝ) ^ 2)⁻¹ := RamanujanPetersson.GSA.summable_inv_one_add_sq
  have hf0le : ∀ e, f0 e ≤ (1 + (e : ℝ) ^ 2)⁻¹ := fun e => by
    simp only [hf0]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hsumf0 : Summable f0 := hsum0.of_nonneg_of_le (fun _ => by positivity) hf0le
  refine ⟨hsumf0.indicator A, ?_⟩
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLpos
  set κ : A → ℤ := fun e => (e : ℤ) / (L : ℤ) with hκ_def
  have hκ : Function.Injective κ := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ hee
    simp only [hκ_def] at hee
    have hd1 : (c1 : ℤ) ∣ e - e' := by
      have := dvd_sub he'.1 he.1
      rwa [show r - e' - (r - e) = e - e' by ring] at this
    have hd2 : (c2 : ℤ) ∣ e - e' := by
      have := dvd_sub he.2 he'.2
      rwa [show r + e - (r + e') = e - e' by ring] at this
    have hdL : (L : ℤ) ∣ e - e' := by
      rw [Int.natCast_dvd] at hd1 hd2 ⊢
      exact Nat.lcm_dvd hd1 hd2
    obtain ⟨k, hk⟩ := hdL
    have he_eq : e = e' + (L : ℤ) * k := by linarith
    rw [he_eq, Int.add_mul_ediv_left _ _ hLz.ne'] at hee
    have hk0 : k = 0 := by linarith
    subst hk0
    simp only [Subtype.mk.injEq]
    linarith
  set hq : ℤ → ℝ := fun q => 5 * ((L : ℝ) ^ 2)⁻¹ * (1 + (q : ℝ) ^ 2)⁻¹ with hq_def
  have hsq : Summable hq := hsum0.mul_left _
  have hq0 : ∀ q, 0 ≤ hq q := fun q => by simp only [hq_def]; positivity
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hpt : ∀ e : A, f0 e ≤ hq (κ e) := by
    intro e
    simp only [hf0, hq_def, hκ_def]
    have hb : ((L : ℝ)) ^ 2 * (1 + (((e : ℤ) / (L : ℤ) : ℤ) : ℝ) ^ 2) ≤ 5 * ((L : ℝ) ^ 2 + ((e : ℤ) : ℝ) ^ 2) := by
      exact_mod_cast floor_bound hLz (e : ℤ)
    have hLR : (L : ℝ) ≤ ((c1 * c2 : ℕ) : ℝ) := by exact_mod_cast hLP
    have hLP2 : (L : ℝ) ^ 2 ≤ ((c1 * c2 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ hL0.le hLR 2
    rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ∑' e, A.indicator f0 e = ∑' e : A, f0 e := (tsum_subtype A f0).symm
    _ ≤ ∑' e : A, hq (κ e) := Summable.tsum_le_tsum hpt (hsumf0.subtype A) (hsq.comp_injective hκ)
    _ ≤ ∑' q, hq q := tsum_comp_le_tsum_of_inj hsq hq0 hκ
    _ = 5 * K0 * ((L : ℝ) ^ 2)⁻¹ := by
      simp only [hq_def]
      rw [tsum_mul_left, K0]
      ring

end RamanujanPetersson.EllW2


