-- Prove2me | Definitions.Def_SourceProof_e04f83f7c1e6a0d560fd2699
-- name    : SourceProof_e04f83f7c1e6a0d560fd2699
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:11.376876+00:00
-- url     : https://prove2.me/theorems/b57ae80d-72ba-4717-a4b9-a4f1ca1db5eb
-- title:
--   StochLean source theorem: MeasureTheory.UniformIntegrableByEnvelope.aestronglyMeasurable

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_Function_DeLaValleePoussin_F000

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

theorem _root_.Prove2MeSourceProof.h_e04f83f7c1e6a0d560fd2699 (hf : UniformIntegrableByEnvelope f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ := hf.1.aestronglyMeasurable i
end UniformIntegrableByEnvelope

namespace SuperlinearEnvelope

end SuperlinearEnvelope

end

end MeasureTheory


