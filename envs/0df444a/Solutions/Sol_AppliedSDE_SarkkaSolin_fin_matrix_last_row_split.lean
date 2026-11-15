-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fin_matrix_last_row_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:45:39.222319+00:00
-- url     : https://prove2.me/submissions/f603a7d7-81ae-4a71-a815-d0bdcfbfdbe0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (z : Fin (n + 2) -> ℝ) :
    (K.mulVec z) (Fin.last (n + 1)) =
      (fun i : Fin (n + 1) => K (Fin.last (n + 1)) i.castSucc)
        ⬝ᵥ (fun i => z i.castSucc) +
      K (Fin.last (n + 1)) (Fin.last (n + 1)) *
        z (Fin.last (n + 1)) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
