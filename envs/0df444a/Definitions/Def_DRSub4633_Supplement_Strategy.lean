-- Prove2me | Definitions.Def_DRSub4633_Supplement_Strategy
-- name    : DRSub4633_Supplement_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:27:12.821111+00:00
-- url     : https://prove2.me/theorems/c9d8bbda-eeb8-4b1f-80e1-a26cc747936c
-- title:
--   A randomized oracle algorithm (exact-real model)
-- statement:
--   A randomized oracle algorithm on $\mathbb R^n$ with randomness space $\Omega$ is a rule that, given a random seed $\omega\in\Omega$ and the transcript so far (the past queries together with their exact answers), either issues the next query or stops and outputs a point $y\in\mathbb R^n$.
--
--   This is the paper's exact-real oracle model: "Counts refer to exact-real oracle calls, with the scalar arithmetic and sampling operations of the field construction" (p.8). Computation on the exact real answers and the use of randomness are free; only oracle calls are counted. The algorithm sees the objective and the feasible set only through the oracle answers.
--
--   **Formalization Note** The seed is drawn from a probability measure on $\Omega$ that is chosen together with the strategy.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, p.8 (exact-oracle model (6)), and Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query

namespace DRSub4633.Supplement

/-- **A randomized oracle algorithm.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, p.8: "Counts refer to exact-real
oracle calls, with the scalar arithmetic and sampling operations of the field construction"; and
Theorem 6.3, p.37: "there is a randomized algorithm returning `y ∈ K`".

A `Strategy n Ω` maps a random seed `ω ∈ Ω` and the transcript so far (the list of past queries
with their answers) either to the next query (`Sum.inl q`) or to the output point
(`Sum.inr y`), at which the algorithm stops.

**Formalization Note.** This is the exact-real (real-RAM) oracle model: the next decision is an
arbitrary function of the seed and of the exact real answers, so scalar computation and sampling
are free and only oracle calls are counted. The algorithm sees the objective and the feasible set
only through the answers; it is chosen knowing only `n` (and `ε`, in Theorem 6.3). Its
randomness is the seed `ω`, drawn from a probability measure on `Ω` fixed together with the
strategy. -/
def Strategy (n : ℕ) (Ω : Type) : Type :=
  Ω → List (Query n × (ℝ × EuclideanSpace ℝ (Fin n))) → Query n ⊕ EuclideanSpace ℝ (Fin n)

end DRSub4633.Supplement


