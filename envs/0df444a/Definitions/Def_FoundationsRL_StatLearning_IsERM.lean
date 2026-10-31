-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_IsERM
-- name    : FoundationsRL_StatLearning_IsERM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:28.75714+00:00
-- url     : https://prove2.me/theorems/69828d49-a337-4bc5-9b4a-016704cb73bf
-- title:
--   Empirical risk minimizer (measurable selection)
-- statement:
--   A map $\widehat f$ from datasets to predictors is an **empirical risk minimizer** with respect to $\mathcal F$ if for every dataset
--
--   $$
--   \widehat f\in\operatorname*{arg\,min}_{f\in\mathcal F}\widehat L(f).
--   $$
--
--   Ties may be broken in any way, as long as the selection is measurable.
--
--   **Formalization Note** Measurability means that for each $f\in\mathcal F$ the set of datasets on which $\widehat f=f$ is measurable. Without it $\mathbb E[\mathcal E(\widehat f)]$ would be an integral of a non-measurable function, which Lean evaluates to the junk $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, (1.6), p. 8

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_empLoss
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Empirical risk minimizer** `f̂ ∈ argmin_{f∈F} L̂(f)`, as a map from datasets to `F`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, (1.6), p. 8.

**Formalization Note.** `fhat` is any selection of the argmin: no tie-break is fixed. It is required
to be measurable, in the only sense a selection into a finite class needs: each `{D | fhat D = f}`,
`f ∈ F`, is a measurable set of datasets. Without this, `E[E(f̂)]` would be an integral of a
non-measurable function, which Lean evaluates to the junk value `0`. -/
structure IsERM {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}
    (ℓ : Y' → Y → ℝ) (F : Finset (X → Y')) (fhat : (Fin T → X × Y) → X → Y') : Prop where
  /-- `f̂` takes values in `F`. -/
  mem : ∀ D, fhat D ∈ F
  /-- `f̂` minimizes the empirical loss over `F`. -/
  isMin : ∀ D, ∀ f ∈ F, empLoss ℓ (fhat D) D ≤ empLoss ℓ f D
  /-- `f̂` is a measurable selection. -/
  measurableSet : ∀ f ∈ F, MeasurableSet {D | fhat D = f}

end FoundationsRL.StatLearning


