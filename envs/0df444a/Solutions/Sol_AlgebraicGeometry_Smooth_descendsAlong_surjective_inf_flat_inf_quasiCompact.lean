-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/86b2c53f-27c4-5b13-bbee-961606165e06

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective HasRingHomProperty.descendsAlong IsLocalIso QuasiCompact IsLocalIso.le_of_isZariskiLocalAtSource Scheme Smooth Flat Etale flat_and_surjective_SpecMap_iff HasRingHomProperty"
p2m_open "AlgebraicGeometry"

theorem desc_smooth_descendsAlong :
    DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong (P := @Smooth) (P' := @Surjective ⊓ @Flat)
    (Q := fun f => f.Smooth) (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) RingHom.Smooth.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩

end AlgebraicGeometry

open CategoryTheory _root_.CategoryTheory.MorphismProperty _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry in
theorem solution :
    DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  AlgebraicGeometry.desc_smooth_descendsAlong

end S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact (solution)
