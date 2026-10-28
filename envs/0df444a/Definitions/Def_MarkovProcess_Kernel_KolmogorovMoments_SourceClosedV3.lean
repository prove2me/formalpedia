-- Prove2me | Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
-- name    : MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:49:34.311347+00:00
-- url     : https://prove2.me/theorems/f6829525-6d6e-461c-b9d9-558b074774bb
-- title:
--   MarkovProcess definitions: Kernel.KolmogorovMoments
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Kernel.KolmogorovMoments`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KolmogorovMoments.lean#L1-L75

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Intrinsic Kolmogorov moment bounds for a transition semigroup

Kolmogorov's continuity criterion is usually imposed on an already constructed coordinate
process.  This file states the same criterion directly on the transition semigroup: the
`p`-th moment of the displacement accumulated over a time step `h` is at most `M * h ^ q`,
uniformly in the starting point.

The predicate is purely a moment bound on the transition kernels.  It makes no path-space,
continuity, or stochastic-process claim; the transport of this bound to the canonical
dense-time coordinate process is proved elsewhere.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]

/-- A uniform `p`-th moment bound on the displacement of `P` over time `h`, of order `h ^ q`.

The exponents are constrained by `0 < p` and `1 < q`, exactly the range in which the
Kolmogorov--Chentsov threshold `(q - 1) / p` is a positive Hölder exponent.  The bound is demanded for every time `h ≥ 0`, not only
for small `h`; this is stronger than the local criterion the Kolmogorov--Chentsov theorem
needs, and it is what the bridge to `KolmogorovRegular` consumes. -/
def HasKolmogorovMoments (P : SubMarkovKernelSemigroup alpha) (p q : ℝ) (M : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧
    ∀ (h : ℝ≥0) (y : alpha), ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q

namespace HasKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M : ℝ≥0}











end HasKolmogorovMoments

end SubMarkovKernelSemigroup

end MarkovProcess


