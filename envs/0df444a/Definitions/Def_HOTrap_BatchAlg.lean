-- Prove2me | Definitions.Def_HOTrap_BatchAlg
-- name    : HOTrap_BatchAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:03.877436+00:00
-- url     : https://prove2.me/theorems/a4369871-a98f-4142-995c-9584fc5a9bed
-- title:
--   Batched gradient-only algorithm
-- statement:
--   A batched gradient-only algorithm with seed space $\Omega$ has a number of adaptive rounds and a batch size for each round. In each round it issues all queries of the batch at once, as a function of the seed and of the gradient answers of the earlier rounds. After the last round it returns a point computed from the seed and all answers.
--
--   This is the class of algorithms over which Theorem 4.1 asserts existence. A deterministic algorithm is the case $\Omega=\{*\}$.
--
--   **Formalization Note** The algorithm receives no value of the objective and is not given the objective: it sees only exact gradients at its own query points. The number of rounds and the batch sizes are fixed, which gives a budget valid for every objective and seed; a run that needs fewer queries pads with dummy queries. Queries may be arbitrary points of $\mathbb R^d$ and offline computation is free.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, Oracle models, pp.13–14; Remark 3.8, p.17

import Mathlib

namespace HOTrap

/-- **A batched gradient-only algorithm with seed space `Ω`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, Oracle models, pp.13–14. The
algorithm has `rounds` adaptive rounds. In round `r` it issues `batch r` query points at once, computed from
the seed and the list of all gradient answers of earlier rounds. At the end `output` maps the seed
and all answers to the returned point.

**Formalization Note** The algorithm sees the objective only through the answers: `query` and `output` do
not receive `f`. A deterministic algorithm is a `BatchAlg d Unit`. The number of rounds and the batch
sizes are fixed in advance, so the budget holds for every objective and every seed; a run that needs
fewer queries pads with dummy queries. Queries may be arbitrary points of `ℝ^d`. Offline computation
is unrestricted (Remark 3.8, p.17). `batch r` is read only for `r < rounds`. -/
structure BatchAlg (d : ℕ) (Ω : Type) where
  /-- Number of adaptive rounds. -/
  rounds : ℕ
  /-- Size of the batch of round `r`. -/
  batch : ℕ → ℕ
  /-- The `i`-th query of round `r`, from the seed and the earlier answers. -/
  query : (r : ℕ) → Ω → List (EuclideanSpace ℝ (Fin d)) → Fin (batch r) → EuclideanSpace ℝ (Fin d)
  /-- The returned point, from the seed and all answers. -/
  output : Ω → List (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)

end HOTrap


