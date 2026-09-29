-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e66097b6-15a3-5fa5-953d-547bc1a90796

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ohom_add_ohom_obd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace OhomAux

open AlgebraicGeometry.Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem oesort_zero_single (u : K.OIdx 0) : K.oesort 0 (Finsupp.single u 1) = Finsupp.single u 1 := by
  haveI : Subsingleton (Fin (0 + 1)) := by change Subsingleton (Fin 1); infer_instance
  have hinj : Function.Injective u := fun a b _ => Subsingleton.elim a b
  have hsort : Tuple.sort u = 1 := Equiv.ext fun i => Subsingleton.elim _ _
  rw [K.oesort_single_of_injective 0 u hinj, hsort, Equiv.Perm.sign_one, Units.val_one, one_smul]
  rfl

theorem oesort_zero (x : K.OCh 0) : K.oesort 0 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | single u a => rw [← mul_one a, ← Finsupp.smul_single', map_zsmul, oesort_zero_single]

theorem olin_ext {n : ℕ} {M : Type*} [AddCommGroup M] (f g : K.OCh n →ₗ[ℤ] M)
    (h : ∀ u, f (Finsupp.single u 1) = g (Finsupp.single u 1)) (x : K.OCh n) :
    f x = g x := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single u a => rw [← mul_one a, ← Finsupp.smul_single', map_zsmul, map_zsmul, h]

end OhomAux

open OhomAux AlgebraicGeometry.Scheme.OrderedAffineCover

theorem solution
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (σ : K.OIdx (n + 1)) :
    K.obd (n + 1) (K.ohom (n + 1) σ) + K.olin n (K.ohom n) (K.obd n (Finsupp.single σ 1)) =
      Finsupp.single σ 1 - K.oesort (n + 1) (Finsupp.single σ 1) := by

  suffices key : ∀ (n : ℕ) (x : K.OCh (n + 1)),
      K.obd (n + 1) (K.olin (n + 1) (K.ohom (n + 1)) x) + K.olin n (K.ohom n) (K.obd n x) = x - K.oesort (n + 1) x by
    have := key n (Finsupp.single σ 1)
    rwa [K.olin_single] at this
  intro n
  induction n with
  | zero =>
    intro x
    refine olin_ext K ((K.obd 1).comp (K.olin 1 (K.ohom 1)) + (K.olin 0 (K.ohom 0)).comp (K.obd 0))
      (LinearMap.id - K.oesort 1) (fun σ => ?_) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, K.olin_single]

    have hD0 : K.olin 0 (K.ohom 0) = 0 := by
      apply LinearMap.ext; intro y
      refine olin_ext K (K.olin 0 (K.ohom 0)) 0 (fun u => ?_) y
      rw [K.olin_single, K.ohom_zero, LinearMap.zero_apply]
    rw [K.ohom_succ]
    simp only [hD0, LinearMap.zero_apply, sub_zero, add_zero, Nat.zero_add]
    set y := Finsupp.single σ (1 : ℤ) - K.oesort 1 (Finsupp.single σ 1) with hy
    have hcone := K.obd_ocone_add_ocone_obd (σ 0) 0 y
    have hy0 : K.obd 0 y = 0 := by
      rw [hy, map_sub, K.obd_oesort, oesort_zero, sub_self]
    rw [hy0, map_zero, add_zero] at hcone
    exact hcone
  | succ k ih =>
    intro x
    refine olin_ext K ((K.obd (k + 2)).comp (K.olin (k + 2) (K.ohom (k + 2))) + (K.olin (k + 1) (K.ohom (k + 1))).comp (K.obd (k + 1)))
      (LinearMap.id - K.oesort (k + 2)) (fun σ => ?_) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, K.olin_single]
    rw [K.ohom_succ]
    set y := Finsupp.single σ (1 : ℤ) - K.oesort (k + 2) (Finsupp.single σ 1) -
      K.olin (k + 1) (K.ohom (k + 1)) (K.obd (k + 1) (Finsupp.single σ 1)) with hy
    have hcone := K.obd_ocone_add_ocone_obd (σ 0) (k + 1) y
    have hy0 : K.obd (k + 1) y = 0 := by
      rw [hy, map_sub, map_sub, K.obd_oesort]
      have h2 := ih (K.obd (k + 1) (Finsupp.single σ 1))
      rw [K.obd_obd, map_zero, add_zero] at h2
      rw [h2, sub_self]
    rw [hy0, map_zero, add_zero] at hcone
    rw [hcone, hy]
    abel

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ohom_add_ohom_obd
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ohom_add_ohom_obd (solution)
