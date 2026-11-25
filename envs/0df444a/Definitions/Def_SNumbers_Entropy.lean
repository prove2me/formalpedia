-- Prove2me | Definitions.Def_SNumbers_Entropy
-- name    : SNumbers_Entropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:35.907031+00:00
-- url     : https://prove2.me/theorems/a145fa33-825e-4ca3-965d-4b811ba04585
-- title:
--   Entropy
-- statement:
--   Definitions and structural lemmas for Entropy, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open Filter Topology
namespace SNumbers
section General
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
def entropySet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {ε | 0 < ε ∧ ∃ N : Finset Y, N.card ≤ 2 ^ n ∧
    ⇑S '' Metric.closedBall 0 1 ⊆ ⋃ y ∈ (N : Set Y), Metric.closedBall y ε}
noncomputable def entropyNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (entropySet S n)
end General
section Densely
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end Densely
end SNumbers


