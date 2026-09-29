-- Prove2me | solution 1 for ABC.sum_triples_finite_iff_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:55:17.520176+00:00
-- url     : https://prove2.me/submissions/e56a4e1c-e27c-4899-b84a-7361a504dfee

import Mathlib

open scoped BigOperators

/-- The set of ordered triples `(a, b, c)` of naturals with `a, b > 0` and `a + b = c`
satisfying an arbitrary further condition `P` is finite if and only if the set of
`c`-values it produces is bounded above. -/
theorem solution (P : ℕ × ℕ × ℕ → Prop) :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ P t}.Finite ↔
      BddAbove ((fun t : ℕ × ℕ × ℕ => t.2.2) ''
        {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ P t}) := by
  constructor
  · intro h
    exact (h.image _).bddAbove
  · rintro ⟨C, hC⟩
    refine Set.Finite.subset
      ((Set.finite_Iic C).prod ((Set.finite_Iic C).prod (Set.finite_Iic C))) ?_
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, hb, habc, hP⟩ := ht
    have hcC : c ≤ C := hC ⟨(a, b, c), ⟨ha, hb, habc, hP⟩, rfl⟩
    have hsum : a + b = c := habc
    have haC : a ≤ C := le_trans (hsum ▸ Nat.le_add_right a b) hcC
    have hbC : b ≤ C := le_trans (hsum ▸ Nat.le_add_left b a) hcC
    exact ⟨haC, hbC, hcC⟩
