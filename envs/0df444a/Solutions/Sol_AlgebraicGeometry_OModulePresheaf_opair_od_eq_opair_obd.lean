-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.opair_od_eq_opair_obd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dbb837a9-b53a-5062-bd59-12fd3b2a85bb

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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_opair_od_eq_opair_obd

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace PairingBoundary

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OrderedAffineCover AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem oSub_oface {n k : ℕ} {u : K.OIdx (n + 1)} {t : K.OIdx k} (h : K.OSub u t) (j : Fin (n + 2)) :
    K.OSub (K.oface u j) t := fun l => h (j.succAbove l)

theorem single_case {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n) (u : K.OIdx (n + 1)) (hu : K.OSub u t) :
    F.opair K t (n + 1) (F.od K n c) (Finsupp.single u 1) = F.opair K t n c (K.obd n (Finsupp.single u 1)) := by
  rw [opair_single, oresTo_apply_of_oSub _ _ t u hu, od_apply, map_sum, obd_single, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_zsmul, map_zsmul, opair_single, oresTo_apply_of_oSub _ _ t _ (oSub_oface K hu j), res_res]

end PairingBoundary

open PairingBoundary in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n)
    (x : K.OCh (n + 1)) (hx : ∀ u ∈ x.support, K.OSub u t) :
    F.opair K t (n + 1) (F.od K n c) x = F.opair K t n c (K.obd n x) := by
  have hx' : x = ∑ u ∈ x.support, Finsupp.single u (x u) := (Finsupp.sum_single x).symm
  rw [hx', map_sum, map_sum (K.obd n), map_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [← Finsupp.smul_single_one u (x u), map_zsmul, map_zsmul, map_zsmul]
  congr 1
  exact single_case F K t n c u (hx u hu)

end S_AlgebraicGeometry_OModulePresheaf_opair_od_eq_opair_obd
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_opair_od_eq_opair_obd (solution)
