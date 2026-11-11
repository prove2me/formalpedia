-- Prove2me | Definitions.Def_GaussDiffSVP_factMoment
-- name    : GaussDiffSVP_factMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:49.413136+00:00
-- url     : https://prove2.me/theorems/73e632e1-b2b0-411a-b942-142225e4f34d
-- title:
--   Second factorial measure $S_\Xi$ of a random record list
-- statement:
--   For a random record list with records $(X_i)_{i\in I}$,
--   $$S_\Xi(x,y) = \mathbb E\,\#\{(i,j)\in I^2 : i\ne j,\ X_i = x,\ X_j = y\},$$
--   the expected number of ordered pairs of **distinct records** with values $x$ and $y$. The exclusion is by record, not by value: with $N_x = \Xi(\{x\})$, $S_\Xi(x,x) = \mathbb E[N_x(N_x-1)]$ can be positive. Together with the intensity it gives the second moment, $\mathbb E[\Xi^{\otimes 2}] = S_\Xi + \Delta_*m_\Xi$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (4), §3.2, p.18

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The second factorial measure `S_Ξ(x, y) = E[∑_{i ≠ j} δ_{(X_i, X_j)}](x, y)` of a random record
list (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.2, (4), p.18): the expected number of ordered pairs of **distinct records** (distinct
list positions `i ≠ j`) with values `x` and `y`. "The exclusion is by ID, so for
`N_x = Ξ({x})`, `S_Ξ(x, x) = E[N_x(N_x − 1)]` can be positive."

**Formalization Note.** Records are list positions (see `intensity`); the count is `Set.encard`
and the expectation a sum in `ℝ≥0∞`. -/
noncomputable def factMoment {α : Type*} (μ : PMF (List α)) (x y : α) : ℝ≥0∞ :=
  ∑' l : List α, μ l *
    (({ij : Fin l.length × Fin l.length | ij.1 ≠ ij.2 ∧ l.get ij.1 = x ∧ l.get ij.2 = y}.encard :
      ℕ∞) : ℝ≥0∞)

end GaussDiffSVP


