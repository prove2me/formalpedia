-- Prove2me | Definitions.Def_SourceProof_a4946c6794948bd9996bb99a
-- name    : SourceProof_a4946c6794948bd9996bb99a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:46.273262+00:00
-- url     : https://prove2.me/theorems/69a02185-b5a2-4846-b7ce-ca0c478771fa
-- title:
--   StochLean source theorem: MeasureTheory.uniformIntegrable_of_superlinearEnvelope

import Definitions.Def_SourceProof_6a6dcc85421906b6ea40dcc4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# A de la Vallée-Poussin envelope criterion

This file supplies the generic sufficient direction of the de la Vallée-Poussin criterion. If a
family has uniformly bounded integrals through a nonnegative superlinear envelope, its `L¹` tails
are uniformly small. The result is exposed both for Mathlib's measure-theoretic
`UnifIntegrable` and, on finite measure spaces, its probability-style `UniformIntegrable`.

Convexity and monotonicity of the envelope are useful when constructing an envelope from uniform
integrability, but are not needed for this sufficient direction.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

noncomputable section

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
variable [NormedAddCommGroup E]

namespace UniformIntegrableByEnvelope

variable {f g : ι → α → E} {p : ℝ≥0∞}

end UniformIntegrableByEnvelope

namespace SuperlinearEnvelope

end SuperlinearEnvelope


theorem _root_.Prove2MeSourceProof.h_a4946c6794948bd9996bb99a [IsFiniteMeasure μ]
    {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ≥0) (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞)) :
    UniformIntegrable f 1 μ :=
  uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun _ hε ↦
    (_root_.Prove2MeSourceProof.h_6a6dcc85421906b6ea40dcc4 hΦ) hΦmeas hf C hC hε
end

end MeasureTheory


