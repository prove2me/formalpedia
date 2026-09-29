-- Prove2me | solution 1 for AlgebraicGeometry.charZero_functionField_of_hom_spec_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a66d1e39-b488-5f7e-a2e6-2addf4adcf0f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    (X : Scheme.{0}) [IsIntegral X]
    (C : Type) [Field C] [CharZero C] (f : Spec (CommRingCat.of C) ⟶ X) :
    CharZero X.functionField := by

  haveI : CharZero ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    (RingHom.charZero_iff (ϕ := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective).1 inferInstance

  haveI : CharZero ↑Γ(X, ⊤) := (f.appTop).hom.charZero

  haveI := (Scheme.Opens.nonempty_iff (⊤ : X.Opens)).2 ⟨(inferInstance : Nonempty X).some, trivial⟩
  exact (RingHom.charZero_iff (X.germToFunctionField_injective ⊤)).1 inferInstance

end S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero
end P2MW
export P2MW.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero (solution)
