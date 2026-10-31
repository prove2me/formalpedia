-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_excessLoss
-- name    : FoundationsRL_StatLearning_excessLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:11.576762+00:00
-- url     : https://prove2.me/theorems/63c88ff6-792d-4161-9814-19d6de6a605e
-- title:
--   Excess loss $\mathcal E(f)=L(f)-\min_{f'\in\mathcal F}L(f')$
-- statement:
--   For a finite nonempty class $\mathcal F$, the **excess loss** (or regret) of $f$ is
--
--   $$
--   \mathcal E(f)=L(f)-\min_{f'\in\mathcal F}L(f').
--   $$
--
--   It compares $f$ with the best predictor in the class, with no assumption linking $\mathcal F$ to the distribution.
--
--   **Formalization Note** The minimum is `Finset.inf'` on a nonempty finset: a genuine minimum, with no junk value. The predictor $f$ need not lie in $\mathcal F$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, (1.7), p. 8

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_popLoss
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Excess loss (regret)** `E(f) = L(f) − min_{f'∈F} L(f')`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, (1.7), p. 8.

**Formalization Note.** The class `F` is a nonempty `Finset` of functions and the minimum is
`Finset.inf'`, a genuine attained minimum with no junk value (no `⨅` over a possibly empty or
unbounded index). `f` need not belong to `F`. -/
noncomputable def excessLoss {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure (X × Y)) (ℓ : Y' → Y → ℝ) (F : Finset (X → Y')) (hF : F.Nonempty)
    (f : X → Y') : ℝ :=
  popLoss M ℓ f - F.inf' hF (popLoss M ℓ)

end FoundationsRL.StatLearning


