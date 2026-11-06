-- Prove2me | Definitions.Def_BianchiIX_Literature
-- name    : BianchiIX_Literature
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T18:21:47.801204+00:00
-- url     : https://prove2.me/theorems/57a4cc60-fbdb-4844-b9da-e90f6dd6cd03
-- title:
--   The pointwise ergodic theorem as an explicit input
-- statement:
--   For a measurable space $X$, let $(\mathrm B)_X$ be
--   the following proposition: for every probability measure $\mu$ on $X$,
--   every ergodic map $F:X\to X$, and every integrable $f:X\to\mathbb R$,
--   $$\frac1n\sum_{j=0}^{n-1}f(F^jx)\longrightarrow\int_X f\,d\mu
--   \quad\text{for }\mu\text{-almost every }x.$$
--   This proposition is an explicit hypothesis in the results that use it.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Literature.lean

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Explicit literature inputs. These propositions are parameters, not project axioms. -/

open Filter MeasureTheory
open scoped Topology

namespace BianchiIX.Literature

/-- The real-valued ergodic probability-space form of Birkhoff's pointwise theorem.
Reference: C. Walkden, Ergodic Theory, Corollary 10.1.2, printed page 89,
https://personalpages.manchester.ac.uk/staff/Charles.Walkden/ergodic-theory/ergodic_theory.pdf
No Gauss-specific conclusion or Einstein-flow estimate is included in this input. -/
def BirkhoffErgodicInput (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ (μ : Measure X), IsProbabilityMeasure μ → ∀ (F : X → X), Ergodic F μ →
    ∀ (f : X → ℝ), Integrable f μ →
      ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ F f n x) atTop (𝓝 (∫ y, f y ∂μ))

end BianchiIX.Literature


