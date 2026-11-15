-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_fromBlocks_last_covariance_system
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:57:38.792523+00:00
-- url     : https://prove2.me/submissions/fd3e82ff-98b9-456b-a31f-8f3806b9a051

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_covariance_fromBlocks_system
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_cross_covariance_last_row_smul
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let B : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
      fun i _ => V * a ^ (n + 1 - i.val)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    let knew : Fin (n + 2) -> ℝ :=
      fun j => V * a ^ Nat.dist (n + 1) j.val
    let z := Cnew⁻¹ |>.mulVec knew
    (Matrix.fromBlocks Cold B B.transpose D).mulVec (z ∘ e) =
      Sum.elim (a • kold) (fun _ : Fin 1 => V) := by
  intro e Cnew Cold B D kold knew z
  have hsys :=
    AppliedSDE.SarkkaSolin.ar1_batch_covariance_fromBlocks_system
      n a V r ha ha1 hV hr knew
  change (Matrix.fromBlocks Cold B B.transpose D).mulVec (z ∘ e) =
      knew ∘ e at hsys
  rw [hsys]
  funext j
  rcases j with i | i
  · change knew (e (Sum.inl i)) = (a • kold) i
    rw [finSumFinEquiv_apply_left]
    have hc :=
      congrFun (AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul
        n a V) i
    change V * a ^ Nat.dist (n + 1) i.val =
      a * (V * a ^ Nat.dist n i.val)
    rw [Nat.dist_eq_sub_of_le_right (by omega : i.val <= n + 1)]
    exact hc
  · fin_cases i
    change knew (e (Sum.inr (0 : Fin 1))) = V
    simp [knew, e, finSumFinEquiv_apply_right, Fin.val_natAdd]
