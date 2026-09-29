-- Prove2me | Definitions.Def_NonmonotoneLS_Shared_Steps
-- name    : NonmonotoneLS_Shared_Steps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:16:45.096343+00:00
-- url     : https://prove2.me/theorems/746012f9-a7cb-4fe3-b516-bf282962fd12
-- title:
--   Nonmonotone Wolfe and Armijo step conditions (1.4)–(1.5)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$, a point $x$, a direction $d$ and a reference value $C \in \mathbb{R}$ be given, and write $\nabla f(x) d$ for the directional derivative $\langle \nabla f(x), d\rangle$.
--
--   1. A step $\alpha$ satisfies the **nonmonotone Wolfe conditions** if $\alpha > 0$ and
--   $$f(x + \alpha d) \le C + \delta \alpha \nabla f(x) d \quad (1.4), \qquad \nabla f(x + \alpha d) d \ge \sigma \nabla f(x) d \quad (1.5).$$
--   2. For a trial step $\bar\alpha > 0$, an integer $h$ is **admissible** if the step $\bar\alpha\rho^h$ satisfies (1.4) and $\bar\alpha \rho^h \le \mu$.
--   3. A step $\alpha$ satisfies the **nonmonotone Armijo conditions** if $\alpha = \bar\alpha \rho^{h}$ for some trial step $\bar\alpha > 0$ and some integer $h$ that is the largest admissible integer for $\bar\alpha$.
--
--   With $C = f(x)$ these are the usual monotone Wolfe and Armijo conditions; the reference value $C$ replaces $f(x)$ in the nonmonotone scheme.
--
--   It serves chunk 01-global-convergence (p. 1044, Eqs. (1.4)–(1.5) and the Armijo rule; used by the NLSA run, Lemma 1.1 p. 1045 and Lemma 2.1 p. 1046) and chunk 02-r-linear-convergence (p. 1044, Eqs. (1.4)–(1.5) and the Armijo rule; used by the NLSA run of Theorems 3.1 p. 1049 and 3.2 p. 1051).
--
--   **Formalization Note.** The space is `EuclideanSpace ℝ (Fin n)`, the paper's row vector $\nabla f(x)$ acting on $d$ is the inner product of Mathlib's `gradient f x` with $d$. Because $\rho > 1$, the exponent $h$ ranges over all integers (it may be negative) and uses integer powers; "largest" is `IsGreatest` on the admissible set of integers, not a supremum.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1044, NLSA line search update, Eqs. (1.4)–(1.5)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

open scoped InnerProductSpace

namespace NonmonotoneLS.Shared

variable {n : ℕ}

/-- The nonmonotone Wolfe conditions (1.4)–(1.5) at the point `x` with direction `d`,
reference value `C` and step `α > 0`:
`f(x + α d) ≤ C + δ α ∇f(x) d` and `∇f(x + α d) d ≥ σ ∇f(x) d`. -/
def IsWolfeStep (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  0 < α ∧
    f (x + α • d) ≤ C + p.δ * α * ⟪gradient f x, d⟫_ℝ ∧
    p.σ * ⟪gradient f x, d⟫_ℝ ≤ ⟪gradient f (x + α • d), d⟫_ℝ

/-- For a trial step `ᾱ`, the set of integer exponents `h` such that the step `ᾱ ρ^h`
satisfies (1.4) with reference value `C` and does not exceed `μ`. -/
def armijoAdmissible (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C αbar : ℝ) : Set ℤ :=
  {h | f (x + (αbar * p.ρ ^ h) • d) ≤ C + p.δ * (αbar * p.ρ ^ h) * ⟪gradient f x, d⟫_ℝ ∧
        αbar * p.ρ ^ h ≤ p.μ}

/-- The nonmonotone Armijo conditions (p. 1044): `α = ᾱ ρ^h`, where `ᾱ > 0` is a trial step and
`h` is the largest integer such that (1.4) holds and `α ≤ μ`. -/
def IsArmijoStep (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  ∃ αbar : ℝ, 0 < αbar ∧ ∃ h : ℤ, α = αbar * p.ρ ^ h ∧
    IsGreatest (armijoAdmissible p f x d C αbar) h

end NonmonotoneLS.Shared


