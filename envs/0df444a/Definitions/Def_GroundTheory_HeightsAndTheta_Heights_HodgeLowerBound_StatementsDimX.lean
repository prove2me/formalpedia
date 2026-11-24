-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsDimX
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsDimX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:04.257035+00:00
-- url     : https://prove2.me/theorems/8919bebe-8c6a-4f3c-b3ea-003f2037917a
-- title:
--   Statements Dim X
-- statement:
--   Definitions and structural lemmas for Statements Dim X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsDimX.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)
abbrev DimX.genericCone {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : Type :=
  Localization (Algebra.algebraMapSubmonoid (MRing ι ⧸ P) (nonZeroDivisors ℤ))
def DimX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ),
    IsArithVar P (n + 1) →
      ringKrullDim (DimX.genericCone P) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights


