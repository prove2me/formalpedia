-- Prove2me | solution 1 for Algebra.FormallyUnramified.of_residueField_baseChange_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/47f65255-adde-5411-8dfe-6f1fb92480b7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
open scoped TensorProduct

open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  haveI : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
  have e := KaehlerDifferential.tensorKaehlerEquivBase R (ResidueField R) S
    (ResidueField R ⊗[R] S)
  haveI : Subsingleton Ω[(ResidueField R ⊗[R] S)⁄(ResidueField R)] :=
    h.subsingleton_kaehlerDifferential
  haveI : Subsingleton (ResidueField R ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[S⁄R])).mp inferInstance⟩

end S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
end P2MW
export P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite (solution)
