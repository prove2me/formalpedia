-- Prove2me | Definitions.Def_VWZClique_Weighted
-- name    : VWZClique_Weighted
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T00:58:32.397092+00:00
-- url     : https://prove2.me/theorems/785f68f9-9ee9-47fc-a36b-becb9231feca
-- title:
--   Weighted nine-position sum and arithmetic-program cost
-- statement:
--   A field-valued product of unary and edge tables is summed over all assignments of nine positions. A costed program must give the correct output on every table.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Section 3, equation (1). https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

namespace VWZClique
open OAI.MatrixMultiplication.Arithmetic
abbrev V := Fin 9
abbrev WeightKey (n : ℕ) :=
  (V × Fin n) ⊕ (V × V × Fin n × Fin n)

open Classical in
noncomputable def weightedSum {F : Type*} [Field F] {n : ℕ}
    (H : SimpleGraph V) (w : WeightKey n → F) : F :=
  ∑ a : V → Fin n,
    (∏ i : V, w (.inl (i, a i))) *
    ∏ i : V, ∏ j : V,
      if i < j ∧ H.Adj i j then w (.inr (i, j, a i, a j)) else 1

def computesWithin {F I : Type*} [Field F] (f : (I → F) → F) (B : ℝ) : Prop :=
  ∃ (r : ℕ) (P : Program F I r) (o : Fin r),
    (P.cost : ℝ) ≤ B ∧ ∀ w, P.eval w o = f w

def wedge (H : SimpleGraph V) (f : Fin 3 → V) : Prop :=
  Function.Injective f ∧ H.Adj (f 0) (f 1) ∧ H.Adj (f 1) (f 2)
end VWZClique


