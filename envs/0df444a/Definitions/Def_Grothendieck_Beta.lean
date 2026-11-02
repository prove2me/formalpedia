-- Prove2me | Definitions.Def_Grothendieck_Beta
-- name    : Grothendieck_Beta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T04:15:00.431552+00:00
-- url     : https://prove2.me/theorems/5544fafa-a5e2-4717-a5e9-b36a815c9132
-- title:
--   The constant $\beta(r,G)$
-- statement:
--   Let $r$ be a positive integer, let $G=(V,E)$ be a finite graph with at least one edge, let $(b_{2k+1})_{k\ge0}$ be the Taylor coefficients of $E_r^{-1}$ at the origin, and let $\vartheta(G)$ be the theta number of the complement of $G$. The constant $\beta(r,G)$ is defined by the equation
--
--   $$
--   \sum_{k\ge0}|b_{2k+1}|\,\beta(r,G)^{2k+1}=\frac{1}{\vartheta(G)-1}.
--   $$
--
--   The left-hand side is a series with nonnegative coefficients, increasing and vanishing at $0$, so the equation has at most one positive solution; the paper shows that one exists and lies strictly inside the disc of convergence of $\sum_k b_{2k+1}t^{2k+1}$ (Proposition 4.2). The constant is the one that enters the main theorem: $\beta(r,G)$ is the factor by which the rounding construction of Lemma 4.1 degrades the value of a solution, and $K(r,G)\le\beta(r,G)^{-1}$.
--
--   Equivalently, $\beta(r,G)$ is the unique $t>0$ at which the function $f(t)=\sum_k|b_{2k+1}|t^{2k+1}$ — the series with the *absolute values* of the coefficients — takes the value $1/(\vartheta(G)-1)$; the definition also records this series.
--
--   **Formalization Note** The equation is encoded by taking $\beta(r,G)$ to be the `sInf` of the set of $t\ge0$ with $f(t)\ge1/(\vartheta(G)-1)$. Proposition 4.2 is the statement that this infimum is attained and equals the solution of the equation, which rules out the degenerate reading in which the infimum is taken over an empty set. That $\vartheta(G)\ge2$ for a graph with an edge — so that $1/(\vartheta(G)-1)$ is a finite positive number — is a separate lemma of the mission.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, equation (1.3), p. 83; equation (4.2), p. 92. https://doi.org/10.4086/toc.2014.v010a004

import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Theta

/-!
# The constant `β(r,G)`

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

Equation (1.3), p. 83, and equation (4.2), p. 92: `β(r,G)` is the number defined by

  `∑_{k≥0} |b_{2k+1}| β(r,G)^{2k+1} = 1/(ϑ(G) - 1)`,

where `b_{2k+1}` are the Taylor coefficients of `E_r⁻¹`. It is encoded here as the
infimum of the set of `t ≥ 0` for which the left-hand side is at least the right-hand
side; Proposition 4.2 states that this number exists (the set is nonempty and the
series converges at the infimum).
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The left-hand side `f(t) = ∑_{k≥0} |b_{2k+1}| t^{2k+1}` of equations (1.3) and
(4.2), built from the Taylor coefficients of `E_r⁻¹`. -/
def betaSeries (r : ℕ) (t : ℝ) : ℝ := ∑' k : ℕ, |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1)

/-- `β(r,G)`: the solution of equation (1.3)/(4.2), encoded as the infimum of the
`t ≥ 0` with `∑_k |b_{2k+1}| t^{2k+1} ≥ 1/(ϑ(G) - 1)`. -/
def beta (r : ℕ) (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t}

end Grothendieck


