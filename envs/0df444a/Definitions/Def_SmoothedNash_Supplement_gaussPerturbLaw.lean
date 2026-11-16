-- Prove2me | Definitions.Def_SmoothedNash_Supplement_gaussPerturbLaw
-- name    : SmoothedNash_Supplement_gaussPerturbLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:08:40.777302+00:00
-- url     : https://prove2.me/theorems/99af4be1-872e-46f7-a032-50c24e0e0673
-- title:
--   Law of the Gaussian perturbation $(D, e)$ with i.i.d. $N(0, s)$ entries
-- statement:
--   The algorithm of Theorem 4.20 draws an $n \times n$ matrix $D$ and a vector $e \in \mathbb R^n$ whose $n^2 + n$ entries are independent centered Gaussians of variance $s$. This definition is the law of $(D, e)$: the product of $n^2 + n$ copies of $N(0, s)$.
--
--   **Formalization Note** A nonpositive $s$ is read as variance $0$ (a point mass); the theorem chooses $s$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), proof of Theorem 4.20, p.43

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The law of the Gaussian perturbation drawn by the algorithm of Theorem 4.20 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53),
p.43): an `n × n` matrix `D` and a vector `e ∈ ℝ^n` whose `n² + n` entries are independent
`N(0, s)` random variables (variance `s`).

**Formalization Note** The product of `n² + n` copies of `gaussianReal 0 s`; a variance `s ≤ 0` is
read as `0` (point mass), which no theorem uses. -/
noncomputable def gaussPerturbLaw (n : ℕ) (s : ℝ) :
    Measure ((Fin n × Fin n → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi fun _ : Fin n × Fin n => ProbabilityTheory.gaussianReal 0 s.toNNReal).prod
    (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 s.toNNReal)

end SmoothedNash.Supplement


