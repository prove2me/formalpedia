-- Prove2me | Definitions.Def_StochLean_ForMathlib_MeasureTheory_Function_DeLaValleePoussin_F000
-- name    : StochLean_ForMathlib_MeasureTheory_Function_DeLaValleePoussin_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:42.239324+00:00
-- url     : https://prove2.me/theorems/faff0379-f348-467c-9ec3-83e6cabfcbe0
-- title:
--   StochLean: ForMathlib.MeasureTheory.Function.DeLaValleePoussin F000

import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

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

/-- Klenke's sigma-finite uniform-integrability notion, expressed through Mathlib's canonical
decomposition into uniform absolute continuity and uniform tightness. On finite measure spaces the
tightness conjunct is automatic, while on infinite spaces it records the spatial envelope control
that ordinary `UniformIntegrable` does not provide. -/
def UniformIntegrableByEnvelope (f : ι → α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  UniformIntegrable f p μ ∧ UnifTight f p μ
namespace UniformIntegrableByEnvelope

variable {f g : ι → α → E} {p : ℝ≥0∞}

end UniformIntegrableByEnvelope

namespace SuperlinearEnvelope

end SuperlinearEnvelope

end

end MeasureTheory


