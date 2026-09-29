-- Prove2me | solution 1 for AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5045a5fd-23f6-525e-a6f4-570a9f28e7b3

import Mathlib
import Theorems.Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective HasRingHomProperty.descendsAlong IsLocalIso LocallyQuasiFinite QuasiCompact IsLocalIso.le_of_isZariskiLocalAtSource Scheme Flat flat_and_surjective_SpecMap_iff HasRingHomProperty" namespace LocallyQuasiFinite end AlgebraicGeometry.LocallyQuasiFinite
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.LocallyQuasiFinite" in
theorem AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact' :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) ?_ ?_
    RingHom.QuasiFinite.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]

theorem solution :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact'

end S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact (solution)
