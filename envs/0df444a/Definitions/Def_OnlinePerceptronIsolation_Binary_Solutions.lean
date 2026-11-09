-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Solutions
-- name    : OnlinePerceptronIsolation_Binary_Solutions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:35.435458+00:00
-- url     : https://prove2.me/theorems/48381b1a-9a28-4ba5-8c08-cfa34ce295c3
-- title:
--   Binary perceptron solutions
-- statement:
--   Let $G\in\mathbb R^{m\times n}$ and let $\kappa\in\mathbb R$ be any margin. A signing is a vector $\sigma\in\{-1,+1\}^n$. It is a solution precisely when
--   $$\forall j\in\{1,\ldots,m\},\qquad \sum_{i=1}^nG_{ji}\sigma_i\ge\kappa\sqrt n.$$
--   This definition provides the feasibility predicate shared by the isolation and uniqueness statements. Signs have exact real values; no satisfiability assumption or margin restriction is included. Coordinates use zero-based finite indices in Lean. Empty row and column sets use their ordinary empty-sum conventions.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.1, Eq. (2.1), printed p.6, PDF p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_ABPOnline_IsOnlineAlg
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Real sign vectors are exactly the finite cube, with no normalization or rounding. -/
def IsSigning {n : ℕ} (σ : Fin n → ℝ) : Prop := ∀ i, σ i = 1 ∨ σ i = -1

/-- Definition 2.1, equation (2.1), printed p.6 / PDF p.8. -/
def IsSolution {m n : ℕ} (G : Fin m × Fin n → ℝ) (κ : ℝ) (σ : Fin n → ℝ) : Prop :=
  IsSigning σ ∧ ∀ j : Fin m, κ * Real.sqrt n ≤ ∑ i : Fin n, G (j, i) * σ i

end OnlinePerceptronIsolation.Binary


