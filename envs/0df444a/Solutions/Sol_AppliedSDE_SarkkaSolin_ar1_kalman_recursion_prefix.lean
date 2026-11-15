-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_recursion_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:03:20.405773+00:00
-- url     : https://prove2.me/submissions/44f1eed7-f907-4887-965e-0474ac29720f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (y m P : Fin (n + 2) -> ℝ)
    (hstep : ∀ j : Fin (n + 1),
      let pred : ℝ := a ^ 2 * P j.castSucc + V * (1 - a ^ 2)
      P j.succ = pred * r / (pred + r) ∧
      m j.succ = a * m j.castSucc +
        pred / (pred + r) * (y j.succ - a * m j.castSucc)) :
    let yold : Fin (n + 1) -> ℝ := fun j => y j.castSucc
    let mold : Fin (n + 1) -> ℝ := fun j => m j.castSucc
    let Pold : Fin (n + 1) -> ℝ := fun j => P j.castSucc
    ∀ j : Fin n,
      let pred : ℝ := a ^ 2 * Pold j.castSucc + V * (1 - a ^ 2)
      Pold j.succ = pred * r / (pred + r) ∧
      mold j.succ = a * mold j.castSucc +
        pred / (pred + r) *
          (yold j.succ - a * mold j.castSucc) := by
  intro yold mold Pold j
  simpa [yold, mold, Pold, Fin.castSucc_succ] using
    (hstep j.castSucc)
