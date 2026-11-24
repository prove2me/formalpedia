-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:16.164803+00:00
-- url     : https://prove2.me/theorems/9f2bec11-422a-43a6-a582-bda6ce3a81c0
-- title:
--   PDual Geom Deg Pos
-- statement:
--   Definitions and structural lemmas for PDual Geom Deg Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder
noncomputable section
namespace DualGeometricDegreePositive
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
def stdLattice (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp
def oneLine : HermLine (dualBlocks T) :=
  HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
end DualGeometricDegreePositive
end
end GroundTheory.Heights₂.Heights


