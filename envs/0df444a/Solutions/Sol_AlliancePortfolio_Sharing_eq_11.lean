-- Prove2me | solution 1 for AlliancePortfolio.Sharing.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:52:42.014641+00:00
-- url     : https://prove2.me/submissions/32b3adc9-c051-48f9-999d-a2b1f4d2e130

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
set_option autoImplicit false

open AlliancePortfolio.Sharing

lemma uu_sum {M : Type*} [AddCommMonoid M] (f : Finset (Fin 3) → M) (j k : Fin 3)
    (hj : ({j, k} : Finset (Fin 3)).powerset = {∅, {j}, {k}, {j, k}})
    (h1 : (∅ : Finset (Fin 3)) ∉ ({{j}, {k}, {j, k}} : Finset (Finset (Fin 3))))
    (h2 : ({j} : Finset (Fin 3)) ∉ ({{k}, {j, k}} : Finset (Finset (Fin 3))))
    (h3 : ({k} : Finset (Fin 3)) ∉ ({{j, k}} : Finset (Finset (Fin 3)))) :
    ∑ S ∈ ({j, k} : Finset (Fin 3)).powerset, f S = f ∅ + f {j} + f {k} + f {j, k} := by
  rw [hj, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  abel

theorem solution (V I b πF sImp sRB : ℝ) :
    (0 ≤ netPayoff V I b πF sImp sRB A ∧ 0 ≤ netPayoff V I b πF sImp sRB B) ↔
      0 ≤ V - I - πF + (2 / 3) * b - (1 / 3) * (sImp - sRB) := by
  have hA : φ V b πF sImp sRB A = (V - πF) / 2 + b / 3 - sImp / 6 + sRB / 6 := by
    unfold φ Supermodularity.Cooperative.ShapleyValue
    have : Finset.univ.erase (A : Fin 3) = {0, 2} := by decide
    rw [this, uu_sum _ 0 2 (by decide) (by decide) (by decide) (by decide)]
    simp [game, F, A, B, Nat.factorial]
    ring
  have hB : φ V b πF sImp sRB B = (V - πF) / 2 + b / 3 - sImp / 6 + sRB / 6 := by
    unfold φ Supermodularity.Cooperative.ShapleyValue
    have : Finset.univ.erase (B : Fin 3) = {0, 1} := by decide
    rw [this, uu_sum _ 0 1 (by decide) (by decide) (by decide) (by decide)]
    simp [game, F, A, B, Nat.factorial]
    ring
  have nA : netPayoff V I b πF sImp sRB A = φ V b πF sImp sRB A - (1 / 2) * I := by
    simp [netPayoff, A, F]
  have nB : netPayoff V I b πF sImp sRB B = φ V b πF sImp sRB B - (1 / 2) * I := by
    simp [netPayoff, B, F]
  rw [nA, nB, hA, hB]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith
