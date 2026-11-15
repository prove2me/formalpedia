-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_covariance_append_block
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:11:09.022193+00:00
-- url     : https://prove2.me/submissions/2f88d3a8-12ab-4b3e-af9b-0fd779206317

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

theorem solution
    (n : ℕ) (a V : ℝ) :
    let Knew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    let Kold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    Knew.submatrix Fin.castSucc Fin.castSucc = Kold ∧
      (∀ i : Fin (n + 1),
        Knew (Fin.castSucc i) (Fin.last (n + 1)) =
          V * a ^ (n + 1 - i.val)) ∧
      Knew (Fin.last (n + 1)) (Fin.last (n + 1)) = V := by
  constructor
  · ext i j
    rfl
  constructor
  · intro i
    change V * a ^ Nat.dist i.val (n + 1) =
      V * a ^ (n + 1 - i.val)
    rw [Nat.dist_comm i.val (n + 1), Nat.dist_eq_sub_of_le_right (Nat.le_of_lt i.isLt)]
  · change V * a ^ Nat.dist (n + 1) (n + 1) = V
    simp
