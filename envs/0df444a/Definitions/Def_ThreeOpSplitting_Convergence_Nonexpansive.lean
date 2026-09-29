-- Prove2me | Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
-- name    : ThreeOpSplitting_Convergence_Nonexpansive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:46:22.0083+00:00
-- url     : https://prove2.me/theorems/0eef4655-f399-43b1-9b7d-9bd408f855b2
-- title:
--   Nonexpansive, firmly nonexpansive and $\alpha$-averaged maps
-- statement:
--   Let $H$ be a real inner product space and $T : H \to H$.
--
--   1. $T$ is **nonexpansive** if $\|Tx - Ty\| \le \|x - y\|$ for all $x, y$.
--   2. $T$ is **firmly nonexpansive** if $\|Tx - Ty\|^2 \le \langle Tx - Ty, x - y\rangle$ for all $x, y$.
--   3. $T$ is **$\alpha$-averaged** if $\alpha \in (0,1)$ and there is a nonexpansive $R : H \to H$ with
--   $$T = (1 - \alpha) I + \alpha R.$$
--
--   These are the regularity classes in which Lemma 2.3 and Proposition 2.1 of Davis and Yin are stated; averagedness of the three-operator map is what drives the convergence of Algorithm 1.
--
--   **Formalization Note** The paper does not define "$\alpha$-averaged"; the standard definition (Bauschke and Combettes, Definition 4.33) is used.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 833, Lemma 2.3 and Proposition 2.1 (terms used there)

import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

/-- `R` is nonexpansive (1-Lipschitz): `‖R x - R y‖ ≤ ‖x - y‖`. -/
def IsNonexpansive {H : Type*} [NormedAddCommGroup H] (R : H → H) : Prop :=
  ∀ x y : H, ‖R x - R y‖ ≤ ‖x - y‖

/-- `T` is firmly nonexpansive: `‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
def IsFirmlyNonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ

/-- `T` is `α`-averaged: `α ∈ (0, 1)` and `T = (1 - α) I + α R` for some nonexpansive `R`. -/
def IsAveraged {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (T : H → H) : Prop :=
  0 < α ∧ α < 1 ∧ ∃ R : H → H, IsNonexpansive R ∧ ∀ x : H, T x = (1 - α) • x + α • R x

end ThreeOpSplitting.Convergence


