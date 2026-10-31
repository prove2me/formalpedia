-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_empLoss
-- name    : FoundationsRL_StatLearning_empLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:14.191858+00:00
-- url     : https://prove2.me/theorems/e1609b3d-2354-4513-bc0b-e072d2881115
-- title:
--   Empirical loss $\widehat L(f)$
-- statement:
--   For a dataset $(x_1,y_1),\dots,(x_T,y_T)$ the **empirical loss** of $f$ is
--
--   $$
--   \widehat L(f)=\frac1T\sum_{i=1}^T\ell(f(x_i),y_i).
--   $$
--
--   It is the observable proxy for $L(f)$ that empirical risk minimization optimizes.
--
--   **Formalization Note** The dataset is a function on `Fin T`. At $T=0$ the value is the junk $0$; every theorem assumes $T\ge1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, (1.5), p. 8

import Mathlib

namespace FoundationsRL.StatLearning

/-- **Empirical loss** `L̂(f) = (1/T) ∑_{i=1}^T ℓ(f(x_i), y_i)` of `f` on a dataset
`D = (x_i, y_i)_{i}` of `T` examples.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, (1.5), p. 8.

**Formalization Note.** The dataset is indexed by `Fin T` (the notes' `1, …, T`). At `T = 0` the
value is the junk `0`; every theorem assumes `0 < T`. -/
noncomputable def empLoss {X Y Y' : Type*} {T : ℕ} (ℓ : Y' → Y → ℝ) (f : X → Y')
    (D : Fin T → X × Y) : ℝ :=
  (1 / (T : ℝ)) * ∑ i, ℓ (f (D i).1) (D i).2

end FoundationsRL.StatLearning


