-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:09.287013+00:00
-- url     : https://prove2.me/theorems/674d7fcf-2b10-4432-adb4-ff6ef0acd6b7
-- title:
--   Imports Ter Tail
-- statement:
--   Definitions and structural lemmas for Imports Ter Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def RegularityLocalFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    Finite (locRing P W ⧸ locIdeal P W y)
end
end GroundTheory.Heights₂.Heights.Inter


