-- Prove2me | solution 1 for Algebra.Etale.of_formallyUnramified_residueField_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f105a7ab-ad05-5759-a052-4b9362b121b5

import Mathlib
import Theorems.Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange
open scoped TensorProduct

theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.Etale R S := by
  haveI := Algebra.FormallyUnramified.of_residueField_baseChange_of_finite R S h
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  haveI : Algebra.FinitePresentation R S := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end S_Algebra_Etale_of_formallyUnramified_residueField_baseChange
end P2MW
export P2MW.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange (solution)
