-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.opair_oesort_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6c7875e8-d50c-51c9-8ccd-a245f9a64440

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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_opair_oesort_single

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n)
    (u : K.OIdx n) (hu : K.OSub u t) :
    F.opair K t n c (K.oesort n (Finsupp.single u 1)) =
      F.res (K.ointer_le_ointer_of_oSub hu) (F.oext K n (F.ores K n c) u) := by
  classical
  by_cases hinj : Function.Injective u
  · rw [K.oesort_single_of_injective _ _ hinj, map_zsmul, F.opair_single,
      F.oext_apply_of_injective K n _ u hinj, map_zsmul, F.ores_apply, F.res_res]
    have hw : K.OSub (u ∘ Tuple.sort u : K.OIdx n) t := K.oSub_trans (fun k => ⟨Tuple.sort u k, rfl⟩) hu
    rw [F.oresTo_apply_of_oSub K t _ hw]
    rfl
  · rw [K.oesort_single_of_not_injective _ _ hinj, map_zero, F.oext_apply_of_not_injective K n _ u hinj, map_zero]

end S_AlgebraicGeometry_OModulePresheaf_opair_oesort_single
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_opair_oesort_single (solution)
