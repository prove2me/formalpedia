-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:08.569792+00:00
-- url     : https://prove2.me/theorems/ab2046eb-2e83-4e7c-9fa2-28324cabb2af
-- title:
--   St Weierstrass Division At Point
-- statement:
--   Definitions and structural lemmas for St Weierstrass Division At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StWeierstrassDivisionAtPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloEliminate
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
def WeierstrassDivisionAtPoint.Statement : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y₀ : τ → ℂ) (c : τ) (d : ℕ) (F g : (τ → ℂ) → ℂ),
    AnalyticAt ℂ F y₀ → AnalyticAt ℂ g y₀ →
    analyticOrderAt (fun s : ℂ => F (y₀ + Pi.single c s)) 0 = d →
    ∃ (q : (τ → ℂ) → ℂ) (a : Fin d → (τ → ℂ) → ℂ),
      AnalyticAt ℂ q y₀ ∧ (∀ j, AnalyticAt ℂ (a j) (zeroCoordinate c y₀)) ∧
      ∀ᶠ y in 𝓝 y₀, g y = q y * F y + ∑ j : Fin d, a j (zeroCoordinate c y) * (y c - y₀ c) ^ (j : ℕ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


