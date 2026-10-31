-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
-- name    : MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:18.699019+00:00
-- url     : https://prove2.me/theorems/2fac3ddb-3f00-4b50-bcf7-db9566349b26
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelConcatenation_cb54f8d1
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pulling a finite-time concatenation back to mixed labels

This file records the reindexing step after an ordered finite-dimensional law has been split at
a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
terminal past label without requiring either label to be present.

The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
continuity, density, path-space, or Feller hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]

/-- Pull a split finite path back to arbitrary past and future label types.  `none` selects the
terminal past coordinate; this is the coordinate used by a future label representing elapsed
time zero. -/
def pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n))
    (z : (Fin (m + 1) → alpha) × (Fin n → alpha)) :
    pastLabel ⊕ futureLabel → alpha
  | Sum.inl i => z.1 (pastIndex i)
  | Sum.inr j => (futureIndex j).elim (z.1 (Fin.last m)) z.2



namespace IsConservative



end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


