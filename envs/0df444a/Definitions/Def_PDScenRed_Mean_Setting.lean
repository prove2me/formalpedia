-- Prove2me | Definitions.Def_PDScenRed_Mean_Setting
-- name    : PDScenRed_Mean_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:58.355977+00:00
-- url     : https://prove2.me/theorems/06896335-eaa5-4984-88e8-5c721839fe8b
-- title:
--   §2.1, §4.2–4.3, pp. 9, 22–24 — the polytope 𝒵, set 𝒰, loss L, upper-bound objective, and one-scenario Wasserstein cost
-- statement:
--   Fix dimensions $d, r \in \mathbb N$, a matrix $P \in \mathbb R^{r\times d}$ and a vector $q \in \mathbb R^r$. Uncertain parameters $\xi$ and decisions $z$ both live in $\mathbb R^d$ with the Euclidean inner product $z'\xi$. The objects of §4.2–4.3 of Bertsimas and Mundru are:
--
--   1. the **polytope** of feasible decisions (§4.2, p. 22)
--   $$\mathcal Z = \{ z \in \mathbb R^d_+ : Pz \le q \};$$
--   2. for a set $\mathcal Z$, the set of **cost-reducing scenarios** of Assumption 5a (p. 24)
--   $$\mathcal U = \Big\{ \xi \in \mathbb R^d : \min_{z \in \mathcal Z} z'\xi < 0 \Big\};$$
--   3. for a set $\mathcal Z$ and a decision rule $z^*:\mathbb R^d\to\mathbb R^d$ (intended to satisfy $z^*(\xi) \in \arg\min_{z\in\mathcal Z} z'\xi$), the **per-scenario upper-bound loss** of the proof of Theorem 3 (p. 24)
--   $$L(\xi, \zeta) = \max\Big\{\max_{z\in\mathcal Z} z'(\xi - 2\zeta),\, 0\Big\} + 2\max\{ z^*(\xi)'\zeta,\, 0\};$$
--   4. for a probability law $\mu$ of $\xi$, the **upper-bound objective** for a single reduced scenario $\zeta$ ($m = 1$)
--   $$F(\zeta) = \mathbb E_{\xi\sim\mu}\big[L(\xi,\zeta)\big].$$
--   5. the **squared one-scenario Wasserstein cost** corresponding to (4), extended to a population law,
--   $$W(\zeta)=\int \|\xi-\zeta\|_2^2\,d\mu(\xi).$$
--
--   $L$ is the per-point objective of the convex upper-bound problem (16) of Proposition 3 for the cost $c(z;\xi) = \max\{z'\xi, 0\}$ of §4.3, after the inner linear programme in $(\lambda, \theta, \gamma)$ is replaced by its optimal value; $F$ is its population version, the objective minimized in Theorem 3.
--
--   **Formalization Note** The minimum $\min_{z\in\mathcal Z} z'\xi$ and maximum $\max_{z\in\mathcal Z} z'v$ are the published `SmartPTO.Fisher.zstar` (an infimum) and `SmartPTO.Fisher.xi` (a supremum); they equal the true minimum and maximum when $\mathcal Z$ is nonempty and bounded, which every theorem using them assumes. The decision rule $z^*$ is a free argument of $L$; the theorems constrain it. $F$ is a Bochner integral, which is $0$ when $\xi\mapsto L(\xi,\zeta)$ is not integrable; the theorems carry the hypotheses (bounded $\mathcal Z$, integrable $\xi$, measurable $z^*$) under which it is integrable. $W$ uses an extended nonnegative integral, so it remains well-defined when the second moment is infinite; the square root in (4) has the same minimizers.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 9 (§2.1, (4)), p. 22 (§4.2, the polytope 𝒵), p. 24 (§4.3, Assumption 5a, proof of Theorem 3, first display)

import Mathlib
import Definitions.Def_SmartPTO_Fisher_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

/-- The polytope `𝒵 = {z ∈ ℝ^d_+ : P z ≤ q}` of §4.2, p. 22 (here `n_z = d`, since the cost of
§4.3 is `z′ξ`). -/
def polytope {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {z | (∀ k, 0 ≤ z k) ∧ ∀ l, ∑ k, P l k * z k ≤ qv l}

/-- The set `𝒰 = {ξ : min_{z∈𝒵} z′ξ < 0}` of Assumption 5a, p. 24. -/
noncomputable def Uset {d : ℕ} (Z : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {ξ | SmartPTO.Fisher.zstar Z ξ < 0}

/-- The per-scenario objective `L(ξ, ζ) = max{max_{z∈𝒵} z′(ξ − 2ζ), 0} + 2 max{z*(ξ)′ζ, 0}` of the
proof of Theorem 3, p. 24, for the cost `c(z; ξ) = max{z′ξ, 0}`; `zsel ξ` is the decision `z*(ξ)`. -/
noncomputable def lossL {d : ℕ} (Z : Set (EuclideanSpace ℝ (Fin d)))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ξ ζ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0 + 2 * max ⟪zsel ξ, ζ⟫_ℝ 0

/-- The upper-bound objective `𝔼[L(ξ, ζ)]` for `m = 1`, p. 24. -/
noncomputable def upperBoundObj {d : ℕ} (Z : Set (EuclideanSpace ℝ (Fin d)))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (ζ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ξ, lossL Z zsel ξ ζ ∂μ

/-- The squared one-scenario Wasserstein transport cost corresponding to (4), pp. 9–10,
extended to a population law. With one target atom the coupling is forced. -/
noncomputable def wassersteinOneObj {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (ζ : EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ - ζ‖ ^ (2 : ℕ)) ∂μ

end PDScenRed.Mean


