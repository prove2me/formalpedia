-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:47:32.727799+00:00
-- url     : https://prove2.me/submissions/e7965bd7-e0fb-4024-8a5f-e0aba8fdc9a0

import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V : ℝ) :
    (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val)) =
      a • (fun i : Fin (n + 1) => V * a ^ Nat.dist n i.val) := by
  funext i
  have hi : i.val <= n := by omega
  change V * a ^ (n + 1 - i.val) =
    a * (V * a ^ Nat.dist n i.val)
  rw [Nat.dist_eq_sub_of_le_right hi]
  have he : n + 1 - i.val = (n - i.val) + 1 := by omega
  rw [he, pow_succ]
  ring
