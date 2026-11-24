-- Prove2me | Definitions.Def_StochLean_Probability_Process_Measurability_Joint_F000
-- name    : StochLean_Probability_Process_Measurability_Joint_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:48.846711+00:00
-- url     : https://prove2.me/theorems/56237838-0412-4ae0-8d1a-3c52a5b27c80
-- title:
--   Product measurability of stochastic processes
-- statement:
--   The process is jointly measurable when the uncurried function on time and sample space is measurable.

import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Joint/product measurability of stochastic processes

This predicate means measurability on the ordinary product sigma-algebra. It is intentionally
distinct from progressive and predictable measurability.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} [MeasurableSpace T] [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

def IsProductMeasurable (X : T → Ω → E) : Prop :=
  Measurable (Function.uncurry X)
namespace IsProductMeasurable

variable {X : T → Ω → E}

end IsProductMeasurable

end ProbabilityTheory


