-- Prove2me | Definitions.Def_LeanNct_Auto_WienerSpace
-- name    : LeanNct_Auto_WienerSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:42:02.061828+00:00
-- url     : https://prove2.me/theorems/ad26202e-91f0-5bac-aba3-b9bf4a9b0efe
-- title:
--   Wiener Space
-- statement:
--   Definitions and structural lemmas for Wiener Space, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
noncomputable def wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (r : ℝ) (x : E) : ℝ :=
  sSup ((fun z : E ↦ ‖f (x + z)‖) '' closedBall 0 r)
def MemW0 {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E] [NormedAddCommGroup 𝕜]
    (f : E → 𝕜) : Prop :=
  Continuous f ∧ Integrable (wienerEnvelope f 1)
noncomputable def wienerNorm {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup 𝕜] (f : E → 𝕜) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (wienerEnvelope f r x)
noncomputable abbrev wienerNormOne {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup 𝕜] (f : E → 𝕜) : ℝ≥0∞ :=
  wienerNorm f 1
noncomputable def C_wienerNormRadiusIndependence (d : ℕ) (r s : ℝ) : ℝ :=
  max 1 ((3 * s / r) ^ d)
end Auto


