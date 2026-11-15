-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_posterior_innovation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:08:53.70896+00:00
-- url     : https://prove2.me/submissions/f21db246-00d1-4194-8410-b4137e694ec9

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_mulvec_innovation
import Theorems.Thm_AppliedSDE_SarkkaSolin_gp_batch_posterior_residual
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

theorem solution
    (n : ℕ) (a V r : ℝ) (y : Fin (n + 2) → ℝ)
    (hM :
      ((Matrix.of (fun i j : Fin (n + 2) => V * a ^ Nat.dist i.val j.val)) +
          r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).PosDef) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ))⁻¹ |>.mulVec y
    let m := K.mulVec z
    (r + V * (1 - a ^ 2)) * m (Fin.last (n + 1)) =
      a * r * m ((Fin.last n).castSucc) +
        V * (1 - a ^ 2) * y (Fin.last (n + 1)) := by
  let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
  let z : Fin (n + 2) → ℝ :=
    (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ))⁻¹ |>.mulVec y
  let m : Fin (n + 2) → ℝ := K.mulVec z
  let q : ℝ := V * (1 - a ^ 2)
  have hM' : (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).PosDef :=
    hM
  have hrow :
      m (Fin.last (n + 1)) - a * m ((Fin.last n).castSucc) =
        q * z (Fin.last (n + 1)) :=
    AppliedSDE.SarkkaSolin.ar1_covariance_mulvec_innovation n a V z
  have hres : m = y - r • z :=
    AppliedSDE.SarkkaSolin.gp_batch_posterior_residual K r y hM'
  have heq :
      m (Fin.last (n + 1)) =
        y (Fin.last (n + 1)) - r * z (Fin.last (n + 1)) := by
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      using congrFun hres (Fin.last (n + 1))
  change (r + q) * m (Fin.last (n + 1)) =
    a * r * m ((Fin.last n).castSucc) + q * y (Fin.last (n + 1))
  calc
    (r + q) * m (Fin.last (n + 1)) =
      r * (m (Fin.last (n + 1)) - a * m ((Fin.last n).castSucc)) +
        q * m (Fin.last (n + 1)) +
        a * r * m ((Fin.last n).castSucc) := by ring
    _ = r * (q * z (Fin.last (n + 1))) +
        q * (y (Fin.last (n + 1)) - r * z (Fin.last (n + 1))) +
        a * r * m ((Fin.last n).castSucc) := by rw [hrow, heq]
    _ = a * r * m ((Fin.last n).castSucc) +
        q * y (Fin.last (n + 1)) := by ring
