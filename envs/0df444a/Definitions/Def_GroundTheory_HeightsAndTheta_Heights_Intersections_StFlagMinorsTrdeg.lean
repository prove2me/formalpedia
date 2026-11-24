-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:15:30.225788+00:00
-- url     : https://prove2.me/theorems/6a188995-dc85-4064-b670-49a30661c69b
-- title:
--   St Flag Minors Trdeg
-- statement:
--   Definitions and structural lemmas for St Flag Minors Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StFlagMinorsTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
def FlagMinorsTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    Algebra.trdeg F (Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)) =
      ((flagDim n + (n - 1) : ℕ) : Cardinal)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


