-- Prove2me | Definitions.Def_DKFAsymptotics_Assumptions
-- name    : DKFAsymptotics_Assumptions
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T20:51:56.432884+00:00
-- url     : https://prove2.me/theorems/2dedef68-66ac-4706-ac22-080efa6bbc2b
-- title:
--   Theorem 2 data and assumptions A1–A5
-- statement:
--   For a fixed stationary Gaussian model, the problem data specify two probability-density sequences, two Gaussian approximating density sequences, a point $b$, and an arbitrary probability measure $P$. The exact normalized update must be well defined at every positive index. The exact and approximate updates are both defined by the same discriminative density-update formula. The assumptions are exactly A1–A5: weak convergence of the previous-state densities to $P$, $L^1$ approximation by their Gaussian sequence, weak convergence of the current-observation densities to $\delta_b$, $L^1$ approximation by their Gaussian sequence, and weak convergence of the exact updated densities to $\delta_b$. The approximate update's validity, Gaussianity and convergence are conclusions, not fields in these assumptions.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Theorem 2, Appendix B, p. 1003, equation (B.1), assumptions A1–A5 and Remark 2.

import Definitions.Def_DKFAsymptotics_Filter

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics
variable {d : ℕ}

structure Problem (M : Model d) where
  s : ℕ+ → Density d
  u : ℕ+ → Density d
  s' : ℕ+ → Density d
  u' : ℕ+ → Density d
  b : State d
  P : ProbabilityMeasure (State d)
  s_pdf : ∀ n, IsPDF (s n)
  u_pdf : ∀ n, IsPDF (u n)
  s'_gaussian : ∀ n, IsGaussianPDF (s' n)
  u'_gaussian : ∀ n, IsGaussianPDF (u' n)
  original_defined : ∀ n, UpdateDefined M (s n) (u n)

def Problem.p (M : Model d) (D : Problem M) (n : ℕ+) : Density d :=
  updateDensity M (D.s n) (D.u n)

def Problem.p' (M : Model d) (D : Problem M) (n : ℕ+) : Density d :=
  updateDensity M (D.s' n) (D.u' n)

structure Assumptions (M : Model d) (D : Problem M) : Prop where
  A1 : Weakly D.s D.P
  A2 : Tendsto (fun n => l1Distance (D.s n) (D.s' n)) atTop (𝓝 0)
  A3 : Weakly D.u (Measure.dirac D.b)
  A4 : Tendsto (fun n => l1Distance (D.u n) (D.u' n)) atTop (𝓝 0)
  A5 : Weakly (D.p M) (Measure.dirac D.b)

end DKFAsymptotics


