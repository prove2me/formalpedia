-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:43.249924+00:00
-- url     : https://prove2.me/theorems/04659734-6fc8-4584-83e4-9bf2d4ba07f6
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Imports.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CurveDivVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ), IsArithVar W 1 → IsMultiHomog s a → s ∉ W →
    ∀ V ∈ divSupp W s, ¬ IsHorizontal V
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


