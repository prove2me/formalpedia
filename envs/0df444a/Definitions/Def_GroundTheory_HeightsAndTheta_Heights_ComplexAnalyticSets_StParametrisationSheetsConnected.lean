-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametrisationSheetsConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametrisationSheetsConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:08.000107+00:00
-- url     : https://prove2.me/theorems/e1828bdc-7e82-4f23-b19f-b8d8d406926f
-- title:
--   St Parametrisation Sheets Connected
-- statement:
--   Definitions and structural lemmas for St Parametrisation Sheets Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParametrisationSheetsConnected.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalParametrisation
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
open Topology
def ParametrisationSheetsConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → GermIrreducibleAt X w →
      IsPreconnected {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


