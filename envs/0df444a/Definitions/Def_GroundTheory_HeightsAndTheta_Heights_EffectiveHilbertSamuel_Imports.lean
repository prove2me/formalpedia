-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:44.951517+00:00
-- url     : https://prove2.me/theorems/d40ec16a-674d-4255-b223-3fd41d137d89
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/Imports.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
def FLBoundOfGoodS.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (s : Fin D → Fin d.W.n → ℂ),
    d.IsGoodS s → FLBound A d.W.e (fun i => d.W.sec (s i))
end GroundTheory.Heights₂.Heights.EffectiveHS


