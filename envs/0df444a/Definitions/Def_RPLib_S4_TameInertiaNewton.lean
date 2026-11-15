-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaNewton
-- name    : RPLib_S4_TameInertiaNewton
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:02:16.201307+00:00
-- url     : https://prove2.me/theorems/b5597806-a228-41a2-b04f-d932b7c64b58
-- title:
--   The trinomial $X^{p+1} - FX + 1$ has exactly one small root at a pole of $F$
-- statement:
--   Let $v$ be a discrete valuation on a field $L$, written multiplicatively, and $F \in L$ with $v(F) > 1$ (a pole). Every root $w$ of $$X^{p+1} - F X + 1$$ satisfies either $\log v(w) = -\log v(F)$ (a small root) or $p \log v(w) = \log v(F)$ (a big root), by the three-term ultrametric inequality. If the trinomial splits, the product of the roots is $\pm 1$, so the logarithms sum to $0$ and exactly one root is small.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter II, Section 6 (Newton polygons); S. S. Abhyankar, Coverings of algebraic curves, Amer. J. Math. 79 (1957), 825-856

import Mathlib

/-!
# Tame inertia, part Newton: the Abhyankar trinomial has exactly one small root (S4-PD item (2), T6)

For a valuation `v : L → ℤᵐ⁰` and `F` with `1 < v F` (a pole), every root `w` of `X^(p+1) - F X + 1` has
`log v w = -log v F` (small root) or `p · log v w = log v F` (big root) (`trin_val_cases`, three-term
ultrametric). If the trinomial splits, the product of the roots is `±1`, so the logs sum to `0` and exactly one
root is small (`trin_existsUnique_small`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Trin

variable {L : Type*} [Field L]

/-- The Abhyankar trinomial `X^(p+1) - F X + 1`. -/
def trin (p : ℕ) (F : L) : L[X] := X ^ (p + 1) - C F * X + 1

theorem trin_isRoot_iff (p : ℕ) (F w : L) : (trin p F).IsRoot w ↔ w ^ (p + 1) - F * w + 1 = 0 := by
  simp [trin, IsRoot.def]

theorem trin_eq (p : ℕ) (F : L) : trin p F = X ^ (p + 1) + (C (-F) * X + C 1) := by
  rw [trin, C_neg, C_1]
  ring

theorem trin_degree_lt {p : ℕ} (hp : 0 < p) (F : L) :
    degree (C (-F) * X + C 1 : L[X]) < ((p + 1 : ℕ) : WithBot ℕ) :=
  degree_linear_le.trans_lt (by exact_mod_cast (by omega : 1 < p + 1))

theorem trin_monic {p : ℕ} (hp : 0 < p) (F : L) : (trin p F).Monic := by
  rw [trin_eq]
  exact monic_X_pow_add (trin_degree_lt hp F)

theorem trin_natDegree {p : ℕ} (hp : 0 < p) (F : L) : (trin p F).natDegree = p + 1 := by
  rw [trin_eq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact trin_degree_lt hp F

theorem trin_coeff_zero (p : ℕ) (F : L) : (trin p F).coeff 0 = 1 := by
  simp [trin]

/-- The three-term ultrametric case split for a root `w` of the trinomial. -/
theorem trin_val_cases (v : Valuation L (WithZero (Multiplicative ℤ))) {p : ℕ} {F w : L}
    (hw : w ^ (p + 1) - F * w + 1 = 0) {a c : ℤ} (ha : v w = WithZero.exp a) (hc : v F = WithZero.exp c)
    (hc0 : 0 < c) : a = -c ∨ (p : ℤ) * a = c := by
  have he : v (w ^ (p + 1) + 1) = WithZero.exp (c + a) := by
    rw [show w ^ (p + 1) + 1 = F * w by linear_combination hw, map_mul, hc, ha, ← WithZero.exp_add]
  have hp1 : v (w ^ (p + 1)) = WithZero.exp ((p + 1 : ℕ) • a) := by
    rw [map_pow, ha, ← WithZero.exp_nsmul]
  have h1 : v (1 : L) = WithZero.exp 0 := by rw [map_one, WithZero.exp_zero]
  rcases lt_trichotomy a 0 with h | h | h
  · left
    have hlt : v (w ^ (p + 1)) < v 1 := by
      rw [hp1, h1, WithZero.exp_lt_exp, nsmul_eq_mul]
      push_cast
      nlinarith
    rw [Valuation.map_add_eq_of_lt_right v hlt, h1] at he
    have := WithZero.exp_injective he
    omega
  · exfalso
    subst h
    have hle := Valuation.map_add v (w ^ (p + 1)) 1
    rw [he, hp1, h1, smul_zero, max_self, WithZero.exp_le_exp] at hle
    omega
  · right
    have hlt : v (1 : L) < v (w ^ (p + 1)) := by
      rw [hp1, h1, WithZero.exp_lt_exp, nsmul_eq_mul]
      push_cast
      nlinarith
    rw [Valuation.map_add_eq_of_lt_left v hlt, hp1] at he
    have := WithZero.exp_injective he
    rw [nsmul_eq_mul] at this
    push_cast at this
    linarith

/-- Counting identity: `p · Σ ℓ = c · #s - (p + 1) c · #{ℓ < 0}` when every `ℓ x` is `-c` or `c / p`. -/
theorem count_small {X : Type*} (s : Multiset X) (ℓ : X → ℤ) {c : ℤ} (hc : 0 < c) (p : ℕ)
    (h : ∀ x ∈ s, ℓ x = -c ∨ (p : ℤ) * ℓ x = c) :
    (p : ℤ) * (s.map ℓ).sum = c * Multiset.card s - (p + 1) * c * Multiset.countP (fun x => ℓ x < 0) s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have ih' := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    rcases h x (Multiset.mem_cons_self x s) with hx | hx
    · have hlt : ℓ x < 0 := by omega
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons, hlt,
        if_true]
      push_cast
      linear_combination ih' + (p : ℤ) * hx
    · have hpos : ¬ ℓ x < 0 := by
        intro hneg
        have : (p : ℤ) * ℓ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg p) hneg.le
        omega
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons, hpos,
        if_false, add_zero]
      push_cast
      linear_combination ih' + hx

theorem val_prod_eq_exp (v : Valuation L (WithZero (Multiplicative ℤ))) (s : Multiset L)
    (hs : ∀ x ∈ s, x ≠ 0) : v s.prod = WithZero.exp ((s.map fun x => WithZero.log (v x)).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.prod_cons, map_mul, ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy)),
      Multiset.map_cons, Multiset.sum_cons, WithZero.exp_add,
      WithZero.exp_log ((Valuation.ne_zero_iff v).2 (hs x (Multiset.mem_cons_self x s)))]

/-- **T6.** A split Abhyankar trinomial with `1 < v F` has exactly one root `w` with `v w < 1`. -/
theorem trin_existsUnique_small (v : Valuation L (WithZero (Multiplicative ℤ))) {p : ℕ} (hp : 0 < p) {F : L}
    (hF : 1 < v F) (hs : (trin p F).Splits) : ∃! w, (trin p F).IsRoot w ∧ v w < 1 := by
  classical
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, map_zero] at hF
    exact not_lt_of_ge zero_le' hF
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = WithZero.log (v F) := ⟨_, rfl⟩
  have hcF : v F = WithZero.exp c := by rw [hc, WithZero.exp_log ((Valuation.ne_zero_iff v).2 hF0)]
  have hc0 : 0 < c := by
    rw [hcF, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hF
    exact hF
  have hne : trin p F ≠ 0 := (trin_monic hp F).ne_zero
  obtain ⟨s, hsdef⟩ : ∃ s : Multiset L, s = (trin p F).roots := ⟨_, rfl⟩
  have hcard : Multiset.card s = p + 1 := by
    rw [hsdef, ← hs.natDegree_eq_card_roots, trin_natDegree hp F]
  have hmemr : ∀ w, w ∈ s ↔ (trin p F).IsRoot w := fun w => by rw [hsdef, mem_roots hne]
  have hroot : ∀ w ∈ s, w ^ (p + 1) - F * w + 1 = 0 := fun w hw =>
    (trin_isRoot_iff p F w).1 ((hmemr w).1 hw)
  have hw0 : ∀ w ∈ s, w ≠ 0 := by
    intro w hw h
    have h' := hroot w hw
    rw [h] at h'
    simp at h'
  let ℓ : L → ℤ := fun x => WithZero.log (v x)
  have hexp : ∀ w ∈ s, v w = WithZero.exp (ℓ w) := fun w hw =>
    (WithZero.exp_log ((Valuation.ne_zero_iff v).2 (hw0 w hw))).symm
  have hcases : ∀ w ∈ s, ℓ w = -c ∨ (p : ℤ) * ℓ w = c := fun w hw =>
    trin_val_cases v (hroot w hw) (hexp w hw) hcF hc0
  have hsum : (s.map ℓ).sum = 0 := by
    have h1 := hs.coeff_zero_eq_prod_roots_of_monic (trin_monic hp F)
    rw [trin_coeff_zero, ← hsdef] at h1
    have h3 := congrArg v h1
    rw [map_one, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
      val_prod_eq_exp v s hw0, ← WithZero.exp_zero] at h3
    exact (WithZero.exp_injective h3).symm
  have hcnt := count_small s ℓ hc0 p hcases
  rw [hsum, mul_zero, hcard] at hcnt
  have hr : Multiset.countP (fun x => ℓ x < 0) s = 1 := by
    have h : ((p : ℤ) + 1) * c * (1 - (Multiset.countP (fun x => ℓ x < 0) s : ℤ)) = 0 := by
      push_cast at hcnt
      linear_combination -hcnt
    rcases mul_eq_zero.1 h with h | h
    · exfalso
      have : (0 : ℤ) < ((p : ℤ) + 1) * c := mul_pos (by positivity) hc0
      omega
    · omega
  rw [Multiset.countP_eq_card_filter] at hr
  obtain ⟨w₀, hw₀⟩ := Multiset.card_eq_one.1 hr
  have hmem : ∀ w, w ∈ s.filter (fun x => ℓ x < 0) ↔ w = w₀ := fun w => by
    rw [hw₀, Multiset.mem_singleton]
  have hsmall : ∀ w ∈ s, v w < 1 ↔ ℓ w < 0 := fun w hw => by
    rw [hexp w hw, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  refine ⟨w₀, ?_, ?_⟩
  · have h0 := (hmem w₀).2 rfl
    rw [Multiset.mem_filter] at h0
    exact ⟨(hmemr w₀).1 h0.1, (hsmall w₀ h0.1).2 h0.2⟩
  · rintro w ⟨hw, hwv⟩
    have hws : w ∈ s := (hmemr w).2 hw
    exact (hmem w).1 (Multiset.mem_filter.2 ⟨hws, (hsmall w hws).1 hwv⟩)

end Trin

end

end TameInertia
end RamanujanPetersson


