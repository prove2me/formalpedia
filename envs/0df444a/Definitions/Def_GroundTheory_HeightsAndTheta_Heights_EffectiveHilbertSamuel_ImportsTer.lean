-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:04.987102+00:00
-- url     : https://prove2.me/theorems/a9ea0236-bc25-4dd3-9041-a84ccaa9f65e
-- title:
--   Imports Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/ImportsTer.lean

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
def HasSymbolIffSymEq.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas D X)
    (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ) (g : (Fin D → ℕ) → X → ℂ),
    F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    (d.HasSymbol s a F g ↔ d.InFil s a F ∧ SymEq A (fun i => d.W.sec (s i)) F a g)
end GroundTheory.Heights₂.Heights.EffectiveHS


