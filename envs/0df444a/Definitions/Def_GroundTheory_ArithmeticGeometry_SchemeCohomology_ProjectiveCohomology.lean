-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:43:08.480826+00:00
-- url     : https://prove2.me/theorems/649ea901-0430-402e-a502-462fdbe0d6f6
-- title:
--   Projective Cohomology
-- statement:
--   Definitions and structural lemmas for Projective Cohomology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechCompute
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_iSup_stdOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe w' u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]
def HZeroEquiv (k : ℕ) :
    Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) 0 ≃+
      homogeneousSubmodule (Fin (n + 1)) A k :=
  (cechHZeroEquivH (modulesAb (twistingSheaf (grading A n) k)) (cover A n)
    iSup_stdOpen).symm.trans (cechHZeroEquiv' k)
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


