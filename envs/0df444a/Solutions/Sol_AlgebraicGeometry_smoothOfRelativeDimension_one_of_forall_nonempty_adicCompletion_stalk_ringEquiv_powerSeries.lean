-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/db138326-5c16-5dcb-aa3c-0c7e8062ab66

import Mathlib
import Theorems.Thm_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (h : ∀ y : ↥Y, IsClosed ({y} : Set ↥Y) →
      Nonempty (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+* PowerSeries k)) :
    SmoothOfRelativeDimension 1 g := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  apply AlgebraicGeometry.smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk k g 1
  intro y hy
  obtain ⟨hdom, hdvr⟩ := IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
    (Y.presheaf.stalk y) k (h y hy)
  haveI := hdom; haveI := hdvr
  refine ⟨inferInstance, ?_⟩
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  rfl

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries (solution)
