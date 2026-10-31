-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_gridWidth
-- name    : KallMayerSLP_RecourseBounds_gridWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:47.146687+00:00
-- url     : https://prove2.me/theorems/95e52acc-635f-452a-b681-ffbeaa780c7a
-- title:
--   Grid width of a partition
-- statement:
--   For a partition $\mathcal X=\{\Xi_k;\ k=1,\dots,K\}$ of $\Xi$, the diameter of a cell is $\operatorname{diam}\Xi_k=\sup\{\|\xi-\eta\|\mid \xi,\eta\in\Xi_k\}$ and the **grid width** of the partition is
--   $$
--   \operatorname{grid}\mathcal X=\max_{k=1,\dots,K}\operatorname{diam}\Xi_k .
--   $$
--
--   **Formalization Note** The diameter is `Metric.diam` for the sup norm of `Fin r → ℝ`. The book does not name its norm; all norms on $\mathbb R^r$ are equivalent and the grid width is only used through $\operatorname{grid}\mathcal X^\nu\to0$, which does not depend on the norm. The maximum is `⨆ k`, which is $0$ only for $K=0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, before Lemma 2.9, p.224 (PDF 233)

import Mathlib

namespace KallMayerSLP.RecourseBounds

/-- **The grid width of a partition.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, before Lemma 2.9, printed p.224
(PDF 233): `diam Ξₖ := sup{‖ξ − η‖ | ξ, η ∈ Ξₖ}` and `grid X := max_{k=1,···,K} diam Ξₖ`.

**Formalization Note.** `diam` is `Metric.diam`, for the sup norm of `Fin r → ℝ`; the book does not
name its norm, all norms on `ℝ^r` are equivalent, and the grid width is only used through
`grid X^ν → 0`, which does not depend on the norm. The cells of a partition of a box are bounded,
so `Metric.diam` is their true diameter. The maximum over the finitely many cells is `⨆ k`; it is
`0` only for `K = 0`, which no partition of a nonempty box has. -/
noncomputable def gridWidth {r K : ℕ} (cell : Fin K → Set (Fin r → ℝ)) : ℝ :=
  ⨆ k, Metric.diam (cell k)

end KallMayerSLP.RecourseBounds


