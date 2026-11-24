-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:17.070822+00:00
-- url     : https://prove2.me/theorems/fb4b5895-b574-4ad3-900d-9d042a369d10
-- title:
--   Proj Space
-- statement:
--   Definitions and structural lemmas for Proj Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjSpace.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable (A : Type u) [CommRing A] (n : ℕ)
abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A
end ProjSpace
open ProjSpace
abbrev projectiveSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)
namespace ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
def stdOpen (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) : (projectiveSpace A n).Opens :=
  Proj.basicOpen (grading A n) (X j)
def xprod {p : ℕ} (i : Fin p → Fin (n + 1)) : MvPolynomial (Fin (n + 1)) A := ∏ a, X (i a)
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


