-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermComplementConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermComplementConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:15.88752+00:00
-- url     : https://prove2.me/theorems/fda1dbf2-553d-4dbb-8024-96b7c7732b77
-- title:
--   St Irreducible Germ Complement Connected
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Complement Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermComplementConnected.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
def IrreducibleGermComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (h : (σ → ℂ) → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AnalyticAt ℂ h w →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ X → h z = 0) →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsPreconnected ((X ∩ B) \ {z | h z = 0})
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


