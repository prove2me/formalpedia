-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_dataLaw
-- name    : FoundationsRL_StatLearning_dataLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:16.989355+00:00
-- url     : https://prove2.me/theorems/20e54242-e8ee-4486-a030-81e9170e4f6d
-- title:
--   Law of the i.i.d. dataset
-- statement:
--   The dataset $H_T=\{(x_t,y_t)\}_{t=1}^T$ consists of $T$ i.i.d. draws from $M^\star$, so its law is the product measure
--
--   $$
--   (M^\star)^{\otimes T}\quad\text{on }(\mathcal X\times\mathcal Y)^T.
--   $$
--
--   Expectations and probabilities over the data in this mission are taken under this measure.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, p. 7

import Mathlib
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Law of the dataset** `H_T = (x_t, y_t)_{t=1}^T`: `T` i.i.d. draws from `M⋆`, that is the
product measure `(M⋆)^{⊗T}` on `(X × Y)^T`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, p. 7. -/
noncomputable def dataLaw {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure (X × Y)) [IsProbabilityMeasure M] (T : ℕ) : Measure (Fin T → X × Y) :=
  Measure.pi fun _ => M

end FoundationsRL.StatLearning


