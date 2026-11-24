-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:40.579799+00:00
-- url     : https://prove2.me/theorems/e1bb1107-4efc-468b-b2ea-eb5a293ed5cd
-- title:
--   Statements Birational Coordinates
-- statement:
--   Definitions and structural lemmas for Statements Birational Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsBirationalCoordinates.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def BirationalCoordinates.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (c : κ), x ⟨(), c⟩ ≠ 0 →
    ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (x' : Ix κ → Ω'),
      mCoordIdeal (ι := GlobalTheory κ) x' = mCoordIdeal (ι := GlobalTheory κ) x ∧ Birational (ι := GlobalTheory κ) x' ∧
      ∀ (A : HermLine (GlobalTheory κ)) (τ : ℕ),
        smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x') x' A) (chartLat (ι := GlobalTheory κ) x' A.a) τ =
          smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


