-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:32.310668+00:00
-- url     : https://prove2.me/theorems/4de56da0-4cc2-4c2f-b800-b74890832a98
-- title:
--   Imports Alt
-- statement:
--   Definitions and structural lemmas for Imports Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/ImportsAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition
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
open ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
def NatSpaceEqVnat.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.HSData A Y) (j : ℕ),
    ((d.natSpace j : Submodule ℂ (Fin A.n → X → ℂ)) : Set (Fin A.n → X → ℂ)) =
      Vnat A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) d.φA
        (IndefiniteRowSideFullHecke.EffectiveHS.fsPhi d.W) j
end GroundTheory.Heights₂.Heights.EffectiveHS


