-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ocone_add_ocone_obd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8ce398e1-8fa9-5ccf-91d8-dd63058250ca

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace B16H1

open AlgebraicGeometry AlgebraicGeometry.Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem oface_cons_zero (m : K.ι) (n : ℕ) (u : K.OIdx n) :
    K.oface (Fin.cons m u : K.OIdx (n + 1)) 0 = u := by
  funext k
  rw [oface_apply, Fin.succAbove_zero, Fin.cons_succ]

theorem oface_cons_succ (m : K.ι) (n : ℕ) (u : K.OIdx (n + 1)) (j : Fin (n + 2)) :
    K.oface (Fin.cons m u : K.OIdx (n + 2)) j.succ = Fin.cons m (K.oface u j) := by
  funext k
  rw [oface_apply]
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero j), Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ, oface_apply]

theorem obd_ocone_single (m : K.ι) (n : ℕ) (u : K.OIdx (n + 1)) :
    K.obd (n + 1) (K.ocone m (n + 1) (Finsupp.single u 1)) + K.ocone m n (K.obd n (Finsupp.single u 1)) =
      Finsupp.single u 1 := by
  rw [ocone_single, obd_single, obd_single, map_sum, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul,
    oface_cons_zero]
  rw [add_assoc, add_eq_left]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [map_smul, ocone_single, oface_cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]

end B16H1

theorem solution
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (m : K.ι) (n : ℕ) (x : K.OCh (n + 1)) :
    K.obd (n + 1) (K.ocone m (n + 1) x) + K.ocone m n (K.obd n x) = x := by
  classical

  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]
  | single u a =>
    rw [← mul_one a, ← Finsupp.smul_single', map_smul, map_smul, map_smul, map_smul, ← smul_add,
      B16H1.obd_ocone_single]

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd (solution)
