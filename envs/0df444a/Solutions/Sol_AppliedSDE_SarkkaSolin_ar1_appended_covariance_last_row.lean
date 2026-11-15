-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_appended_covariance_last_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:46:34.722472+00:00
-- url     : https://prove2.me/submissions/2a66cc41-0135-4732-a0a0-29adf6beb7e1

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_fin_matrix_last_row_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) -> ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    (K.mulVec z) (Fin.last (n + 1)) =
      (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val))
        ⬝ᵥ (fun i => z i.castSucc) +
      V * z (Fin.last (n + 1)) := by
  let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
  have hsplit := AppliedSDE.SarkkaSolin.fin_matrix_last_row_split n K z
  have hrow :
      (fun i : Fin (n + 1) => K (Fin.last (n + 1)) i.castSucc) =
      (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val)) := by
    funext i
    change V * a ^ Nat.dist (n + 1) i.val =
      V * a ^ (n + 1 - i.val)
    rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt i.isLt)]
  have hdiag : K (Fin.last (n + 1)) (Fin.last (n + 1)) = V := by
    simp [K]
  change (K.mulVec z) (Fin.last (n + 1)) =
      (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val))
        ⬝ᵥ (fun i => z i.castSucc) + V * z (Fin.last (n + 1))
  simpa only [hrow, hdiag] using hsplit
