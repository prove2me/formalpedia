-- Prove2me | Definitions.Def_NonmonotoneLS_Global_Regions
-- name    : NonmonotoneLS_Global_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:18:53.601228+00:00
-- url     : https://prove2.me/theorems/44c21841-d767-4a89-9b34-53c2963ebd81
-- title:
--   The level set $\mathcal L$, its neighbourhood $\bar{\mathcal L}$ and the Lipschitz hypothesis of Theorem 2.2
-- statement:
--   For a run with iterates $x_k$ and directions $d_k$ of the nonmonotone line search on $f : \mathbb{R}^n \to \mathbb{R}$:
--
--   1. the **level set** is $\mathcal L = \{ y \in \mathbb{R}^n : f(y) \le f(x_0)\}$;
--   2. $d_{\max} = \sup_k \|d_k\| \in [0, \infty]$;
--   3. $\bar{\mathcal L}$ is the set of $y \in \mathbb{R}^n$ whose distance to $\mathcal L$ is at most $\mu d_{\max}$.
--
--   The **Lipschitz hypothesis** of Theorem 2.2 with constant $L$ is: $\nabla f$ is Lipschitz continuous with constant $L$ on $\mathcal L$ if the Wolfe conditions are used, and on $\bar{\mathcal L}$ if the Armijo conditions are used.
--
--   $\bar{\mathcal L}$ is the region in which the Armijo rule may probe trial points $x_k + \rho\alpha_k d_k$ with $\rho\alpha_k \le \mu$.
--
--   **Formalization Note.** $d_{\max}$ and the distance to $\mathcal L$ are computed in the extended nonnegative reals: the paper does not assume the directions bounded, and when $d_{\max} = \infty$ the set $\bar{\mathcal L}$ is all of $\mathbb{R}^n$ (a real supremum would silently return $0$ for an unbounded sequence and shrink $\bar{\mathcal L}$ to the closure of $\mathcal L$).
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1047, Theorem 2.2 (definitions of the level set, d_max and the set L-bar)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Global_Run

open scoped ENNReal NNReal

namespace NonmonotoneLS.Global

variable {n : ℕ}

/-- The level set `𝓛 = {y : f(y) ≤ f(x₀)}` (Theorem 2.2). -/
def levelSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | f y ≤ f x₀}

/-- `d_max = sup_k ‖d_k‖`, taken in `[0, ∞]` (it is `∞` when the directions are unbounded). -/
noncomputable def dmax (d : ℕ → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ k, (‖d k‖₊ : ℝ≥0∞)

/-- `𝓛̄`: the points whose distance to `𝓛 = {y : f(y) ≤ f(x₀)}` is at most `μ d_max`
(Theorem 2.2), computed in `[0, ∞]`. -/
noncomputable def Lbar (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | Metric.infEDist y (levelSet f (x 0)) ≤ ENNReal.ofReal p.μ * dmax d}

/-- The Lipschitz hypothesis of Theorem 2.2 for the rule `r`, with constant `L`: `∇f` is
`L`-Lipschitz on `𝓛` if the Wolfe conditions are used, and on `𝓛̄` if the Armijo conditions
are used. -/
def LipschitzHyp (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (L : ℝ≥0) : Prop :=
  match r with
  | Rule.wolfe => LipschitzOnWith L (gradient f) (levelSet f (x 0))
  | Rule.armijo => LipschitzOnWith L (gradient f) (Lbar p f x d)

end NonmonotoneLS.Global


