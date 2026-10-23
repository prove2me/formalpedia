-- Prove2me | Definitions.Def_ErgSingMFG_Abelian_Systems
-- name    : ErgSingMFG_Abelian_Systems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:09.029285+00:00
-- url     : https://prove2.me/theorems/60b33bc4-2aa3-4a71-88e6-e449d921b802
-- title:
--   §4–§5, pp. 9–10 — Π, K, K̂, Ĝ, F⁻¹, Φ (5.1) and the equilibrium systems (4.1), (4.3)
-- statement:
--   The functions of §5 and the systems characterizing the equilibria (Theorems 4.2 and 4.4). For a decreasing fundamental solution $\widehat\varphi_r$ of (2.10),
--   $$\Pi(y,\theta;r)=\widehat m'(y)\big(\pi_x(y,\theta)-(r-b'(y))\big),\qquad K(x,\theta;r)=\int_x^\infty\widehat\varphi_r(y)\Pi(y,\theta;r)\,dy,\qquad \widehat K(x,\theta;r)=\frac{K(x,\theta;r)}{\widehat\varphi_r(x)},$$
--   $$\widehat G(x,\theta)=\int_x^\infty\big(f(y)-F^{-1}(\theta)\big)m'(y)\,dy,\qquad \Phi(x,\theta;r)=\big(\widehat K(x,\theta;r),\widehat G(x,\theta)\big)\quad(5.1).$$
--   Here $F^{-1}$ is the inverse of $F$ on $[F(0),\infty)$, extended by $0$ on $(-\infty,F(0)]$.
--
--   A pair $(a,\theta)\in\mathbb R_+^2$ **solves the system** at rate $r$ for $\widehat\varphi_r$ when both integrands are integrable on $(a,\infty)$ and
--   $$\int_a^\infty\widehat\varphi_r(y)\big(\pi_x(y,\theta)-r+b'(y)\big)\widehat m'(y)\,dy=0,\qquad\int_a^\infty\big(f(y)-F^{-1}(\theta)\big)m'(y)\,dy=0,$$
--   with $F^{-1}(\theta)$ a point $z\ge0$ with $F(z)=\theta$. System (4.1) is this at rate $r>0$, and system (4.3) at $r=0$, each required for every choice of $\widehat\varphi_r$.
--
--   **Formalization Note.** $K$ and $\widehat G$ are Bochner integrals; every statement using them carries the integrability of the integrand. The zero extension of $F^{-1}$ (used in $\widehat G$ and $\Phi$) is continuous when $F$ is continuous, strictly increasing and unbounded; in the systems, $F^{-1}(\theta)$ is instead written as a preimage, so $\theta\ge F(0)$ is forced.
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, pp. 9–10, (4.1), (4.3), (5.1), definitions of Π, K, K̂, Ĝ

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- `Π(y, θ; r) := m̂′(y)(π_x(y, θ) − (r − b′(y)))` (§5, p. 10). -/
noncomputable def Pi (m : Model) (y θ r : ℝ) : ℝ := mHat m y * (πx m y θ - (r - deriv m.b y))

/-- `K(x, θ; r) := ∫ₓ^∞ φ̂_r(y) Π(y, θ; r) dy` (§5, p. 10; at `r > 0` it is the `K` of (9.7), at
`r = 0` the left side of (9.17)), for a given decreasing fundamental solution `φh = φ̂_r` of (2.10).
Statements quantify over every `φh` with `IsDecrFundHat m r φh` and state the integrability of the
integrand on `(x, ∞)` alongside. -/
noncomputable def K (m : Model) (φh : ℝ → ℝ) (x θ r : ℝ) : ℝ := ∫ y in Ioi x, φh y * Pi m y θ r

/-- `K̂(x, θ; r) := K(x, θ; r)/φ̂_r(x)` (§5, p. 10). -/
noncomputable def KHat (m : Model) (φh : ℝ → ℝ) (x θ r : ℝ) : ℝ := K m φh x θ r / φh x

open Classical in
/-- `F⁻¹(θ)`, the inverse of `F` on `[0, ∞)` for `θ > F(0)`, extended by `0` for `θ ≤ F(0)`.
For `F` continuous and strictly increasing on `[0, ∞)` with `F(y) → ∞`, this is the inverse on
`[F(0), ∞)` and is continuous on `ℝ`. -/
noncomputable def Finv (m : Model) (θ : ℝ) : ℝ :=
  if θ ≤ m.F 0 then 0 else Function.invFunOn m.F (Ici 0) θ

/-- `Ĝ(x, θ) := ∫ₓ^∞ (f(y) − F⁻¹(θ)) m′(y) dy` (§5, p. 10), with `F⁻¹` as in `Finv`. -/
noncomputable def GHat (m : Model) (x θ : ℝ) : ℝ := ∫ y in Ioi x, (m.f y - Finv m θ) * mp m y

/-- `Φ(x, θ; r) := (K̂(x, θ; r), Ĝ(x, θ))` (5.1), for a family `φh r = φ̂_r` of decreasing
fundamental solutions of (2.10). -/
noncomputable def Phi (m : Model) (φh : ℝ → ℝ → ℝ) (x θ r : ℝ) : ℝ × ℝ :=
  (KHat m (φh r) x θ r, GHat m x θ)

/-- The pair `(a, θ)` solves the system (4.1) (at a rate `r > 0`) or (4.3) (at `r = 0`), for the
fundamental solution `φh = φ̂_r`:
`∫ₐ^∞ φ̂_r(y)(π_x(y, θ) − r + b′(y)) m̂′(y) dy = 0` and `∫ₐ^∞ (f(y) − F⁻¹(θ)) m′(y) dy = 0`,
with `a, θ > 0`, both integrands integrable on `(a, ∞)`, and `F⁻¹(θ)` written as a point `z ≥ 0`
with `F(z) = θ`. -/
def SysAt (m : Model) (φh : ℝ → ℝ) (r a θ : ℝ) : Prop :=
  0 < a ∧ 0 < θ ∧
  IntegrableOn (fun y => φh y * Pi m y θ r) (Ioi a) ∧ K m φh a θ r = 0 ∧
  ∃ z ≥ (0 : ℝ), m.F z = θ ∧ IntegrableOn (fun y => (m.f y - z) * mp m y) (Ioi a) ∧
    ∫ y in Ioi a, (m.f y - z) * mp m y = 0

/-- The system (4.1) of Theorem 4.2 at the rate `r > 0`, for every choice of `φ̂_r`. -/
def Sys41 (m : Model) (r a θ : ℝ) : Prop := ∀ φh, IsDecrFundHat m r φh → SysAt m φh r a θ

/-- The system (4.3) of Theorem 4.4, for every choice of `φ̂₀`. -/
def Sys43 (m : Model) (a θ : ℝ) : Prop := ∀ φh, IsDecrFundHat m 0 φh → SysAt m φh 0 a θ

end ErgSingMFG.Abelian


