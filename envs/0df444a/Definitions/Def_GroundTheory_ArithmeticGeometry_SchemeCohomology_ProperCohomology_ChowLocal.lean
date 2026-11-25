-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ChowLocal
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ChowLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:36.217071+00:00
-- url     : https://prove2.me/theorems/5d67f677-2ced-4f62-b08e-4d2400b38dbd
-- title:
--   Chow Local
-- statement:
--   Definitions and structural lemmas for Chow Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ChowLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable {A : Type u} [CommRing A]
abbrev chartStructureMap (n : ℕ) : A →+* Chart A (0 : Fin (n + 1)) :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


