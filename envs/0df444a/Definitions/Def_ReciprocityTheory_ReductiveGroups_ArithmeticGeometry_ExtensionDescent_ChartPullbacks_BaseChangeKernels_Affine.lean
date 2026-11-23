-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:29.442877+00:00
-- url     : https://prove2.me/theorems/7bc1e620-9a4a-4d5d-9301-97d1ddd90f42
-- title:
--   Affine
-- statement:
--   Definitions and structural lemmas for Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
universe u
section Square
variable {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B}
end Square
section Algebra
variable {R A R' A' : CommRingCat.{u}} {qa : R ⟶ A} {ba : R ⟶ R'} {ga : A ⟶ A'} {qa' : R' ⟶ A'}
  {X : Type u} [AddCommMonoid X]
end Algebra
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


