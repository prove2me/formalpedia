-- Prove2me | Definitions.Def_ShorNonsmooth_RAlgorithm_Widths
-- name    : ShorNonsmooth_RAlgorithm_Widths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:11:44.808983+00:00
-- url     : https://prove2.me/theorems/a3a0a689-303e-4136-8fc4-393229ff9011
-- title:
--   Space dilation $R_\alpha(\xi)$, widths $d_\eta(W)$, $d(W)$, $D(W)$ and the ratio $p(W)$ of a convex body
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x, y)$.
--
--   1. **Space dilation.** For a unit vector $\xi \in E_n$ and a real number $\alpha$, the operator of space dilation in the direction $\xi$ with coefficient $\alpha$ is the linear map
--   $$
--   R_\alpha(\xi)\,x = x + (\alpha - 1)(x, \xi)\,\xi ,
--   $$
--   which multiplies the component of $x$ along $\xi$ by $\alpha$ and leaves the orthogonal component unchanged.
--
--   2. **Widths.** For a set $W \subseteq E_n$ and a unit vector $\eta$ let
--   $$
--   d_\eta^- = \min_{x \in W} (\eta, x), \qquad d_\eta^+ = \max_{x \in W} (\eta, x) \qquad (3.51),
--   $$
--   the positions of the two hyperplanes with normal $\eta$ that support $W$. The width of $W$ in the direction $\eta$ is $d_\eta(W) = d_\eta^+ - d_\eta^-$; the width of $W$ is $d(W) = \min_{\|\eta\| = 1} d_\eta(W)$ and its diameter is $D(W) = \max_{\|\eta\| = 1} d_\eta(W)$.
--
--   3. **The ratio $p(W)$.** For a unit vector $\rho$ let $e_\rho(W) = \inf_{z \in W} |(\rho, z)|$, the distance from $W$ to the hyperplane through the origin with normal $\rho$, and
--   $$
--   K_\rho(W) = \begin{cases} d_\rho(W)/e_\rho(W) & \text{if } e_\rho(W) \neq 0,\\ +\infty & \text{if } e_\rho(W) = 0,\end{cases}
--   \qquad p(W) = \inf_{\|\rho\| = 1} K_\rho(W).
--   $$
--
--   These quantities measure how thin a convex body is and how far it is from the origin relative to its thickness; they are the tools with which Section 3.7 tracks the effect of repeated space dilations in the $r$-algorithm.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`. The book's minima and maxima over $W$ and over the unit sphere are written as `sInf`/`sSup`; they coincide with the book's values whenever $W$ is nonempty and compact, which every theorem of the mission assumes or guarantees (a closed bounded body; the set $\bar P_{\delta,\varepsilon}(x)$). $K_\rho$ and $p$ take values in $[0, +\infty]$ (`ℝ≥0∞`), so the book's value $+\infty$ is represented exactly.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 50, Definition of $R_\alpha(\xi)$ (§3.2); p. 80, (3.51) and the definitions of $d_\eta(W)$, $d(W)$, $D(W)$; p. 82, definitions of $e_\rho(W)$, $K_\rho(W)$, $p(W)$

import Mathlib

open scoped InnerProductSpace ENNReal

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), p. 50, Definition (§3.2): the **operator of space dilation** `R_α(ξ)` in the
direction `ξ` (a unit vector) with coefficient `α`: writing `x = (x, ξ) ξ + d_ξ(x)`, it maps
`x ↦ α (x, ξ) ξ + d_ξ(x) = x + (α - 1)(x, ξ) ξ`. Here `innerSL ℝ ξ x = (ξ, x)`. -/
noncomputable def dilation {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + (α - 1) • (innerSL ℝ ξ).smulRight ξ

/-- Shor (1985), p. 80, (3.51): for a set `W` and a unit vector `η`,
`d_η⁻ = max {d | (η, x) - d ≥ 0, x ∈ W} = min_{x ∈ W} (η, x)`. Taken as an infimum; it is the
book's value whenever `W` is nonempty and compact (every use below). -/
noncomputable def lowerSupport {n : ℕ} (η : EuclideanSpace ℝ (Fin n))
    (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun x => ⟪η, x⟫_ℝ) '' W)

/-- Shor (1985), p. 80, (3.51): `d_η⁺ = min {d | (η, x) - d ≤ 0, x ∈ W} = max_{x ∈ W} (η, x)`. -/
noncomputable def upperSupport {n : ℕ} (η : EuclideanSpace ℝ (Fin n))
    (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup ((fun x => ⟪η, x⟫_ℝ) '' W)

/-- Shor (1985), p. 80: the **width of `W` in the direction `η`**, `d_η(W) = d_η⁺ - d_η⁻`, the
distance between the two parallel supporting hyperplanes with normal `η`. -/
noncomputable def dirWidth {n : ℕ} (η : EuclideanSpace ℝ (Fin n))
    (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  upperSupport η W - lowerSupport η W

/-- Shor (1985), p. 80: the **width** `d(W) = min_{‖η‖ = 1} d_η(W)`. -/
noncomputable def width {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun η => dirWidth η W) '' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- Shor (1985), p. 80: the **diameter** `D(W) = max_{‖η‖ = 1} d_η(W)`. -/
noncomputable def diameterW {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup ((fun η => dirWidth η W) '' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- Shor (1985), p. 82: `e_ρ(W) = inf_{z ∈ W} |(ρ, z)|`, the distance from the hyperplane
`(ρ, z) = 0` through the origin to `W` (for a unit `ρ`). -/
noncomputable def eRho {n : ℕ} (ρ : EuclideanSpace ℝ (Fin n))
    (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun z => |⟪ρ, z⟫_ℝ|) '' W)

/-- Shor (1985), p. 82: `K_ρ(W) = d_ρ(W) / e_ρ(W)` if `e_ρ(W) ≠ 0`, and `+∞` if `e_ρ(W) = 0`;
valued in `[0, +∞]`. -/
noncomputable def kRatio {n : ℕ} (ρ : EuclideanSpace ℝ (Fin n))
    (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  if eRho ρ W = 0 then ⊤ else ENNReal.ofReal (dirWidth ρ W / eRho ρ W)

/-- Shor (1985), p. 82: `p(W) = inf_{‖ρ‖ = 1} K_ρ(W)`, valued in `[0, +∞]`. -/
noncomputable def pRatio {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ ρ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, kRatio ρ W

end ShorNonsmooth.RAlgorithm


