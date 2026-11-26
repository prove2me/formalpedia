-- Prove2me | Definitions.Def_Eden_NonlinearInstability
-- name    : Eden_NonlinearInstability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:27:01.955707+00:00
-- url     : https://prove2.me/theorems/1678737d-4e04-4511-b6ce-4e8d31d8c1f8
-- title:
--   Nonlinear Instability
-- statement:
--   Definitions and structural lemmas for Nonlinear Instability, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean

import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set Filter Topology
namespace Eden
def UnstableRelativeTo (c : ℝ) (B K : Set PhaseSpace) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ p ∈ B, Metric.infDist p K < δ ∧
      ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K
def coordinatePlane (j : Fin 2) : Set PhaseSpace :=
  {p | (if j = 0 then radiusSq₂ p else radiusSq₁ p) = 0 ∧ p 4 = 0}
end Eden


