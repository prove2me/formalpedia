-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
-- name    : InfoLossLAR_Native_AFT_FiniteConcentration
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:22:56.83734+00:00
-- url     : https://prove2.me/theorems/8f19ebd5-e5a8-4f2c-b352-ae492f434a51
-- title:
--   Coordinate oscillations on finite product spaces
-- statement:
--   Let $f:C^d\to\mathbb R$ and let $(c_i)_{i<d}$ be real bounds. The bounded differences condition is $$|f(x)-f(y)|\le c_i\quad\text{whenever }x_j=y_j\text{ for every }j\ne i.$$ The accompanying expectation identity splits an independent product into its first coordinate and remaining coordinates. This is the finite product setup for concentration estimates.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteConcentration.lean; migrated source SHA256 f873907aeff4ff23ad9d882a6430d2d9acf05ae68ec17df93c36f4bb2cfd86a7; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_BlockFock
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Mathlib



/-! # Dimension-free concentration on actual finite product laws -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]



theorem expectation_cons (count : ℕ) (law : Fin (count + 1) → FiniteDist Color)
    (value : (Fin (count + 1) → Color) → ℝ) :
    (FiniteDist.independent law).expectation value =
      (law 0).expectation (fun first =>
        (FiniteDist.independent (fun index => law index.succ)).expectation
          (fun rest => value (Fin.cons first rest))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count + 1) => Color))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  change (∏ index, (law index).weight ((Fin.cons first rest : Fin (count + 1) → Color) index)) * value (Fin.cons first rest) = _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring



/-- Coordinate oscillations, with all other sample values fixed. -/
def BoundedDifferences (count : ℕ) (value : (Fin count → Color) → ℝ) (bound : Fin count → ℝ) : Prop :=
  ∀ index first second, (∀ other, other ≠ index → first other = second other) →
    |value first - value second| ≤ bound index



end

end AFT.FiniteConcentration


