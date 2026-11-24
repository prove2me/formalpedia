-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:12.430666+00:00
-- url     : https://prove2.me/theorems/dbdfe3d0-c3a4-4abf-a328-6cbb8dec0f45
-- title:
--   Imports Bis Further
-- statement:
--   Definitions and structural lemmas for Imports Bis Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsBisFurther.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CellMeets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
def CellDSq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), cellD S y (n + 1) (cellD S y n s) = 0
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


