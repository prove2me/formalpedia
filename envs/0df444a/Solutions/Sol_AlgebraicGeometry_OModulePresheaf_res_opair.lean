-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.res_opair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/308b5c65-f7a7-51d9-b2a3-6bacd90bc4ac

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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_res_opair

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k k' : ℕ} (t : K.OIdx k) (t' : K.OIdx k') (htt : K.OSub t' t)
    (n : ℕ) (c : F.ocochain K n) (x : K.OCh n) (hx : ∀ u ∈ x.support, K.OSub u t') :
    F.res (K.ointer_le_ointer_of_oSub htt) (F.opair K t' n c x) = F.opair K t n c x := by
  classical

  have hexp : ∀ {k₀ : ℕ} (s : K.OIdx k₀), F.opair K s n c x = x.sum (fun u r => r • F.oresTo K s u (c u)) := by
    intro k₀ s
    show K.olin n (fun u => F.oresTo K s u (c u)) x = _
    simp only [Scheme.OrderedAffineCover.olin, Finsupp.lift_apply]
  rw [hexp t', hexp t, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_zsmul]
  congr 1
  have hut' : K.OSub u t' := hx u hu
  have hut : K.OSub u t := K.oSub_trans hut' htt
  rw [F.oresTo_apply_of_oSub K t' u hut', F.oresTo_apply_of_oSub K t u hut, F.res_res]

end S_AlgebraicGeometry_OModulePresheaf_res_opair
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_res_opair (solution)
