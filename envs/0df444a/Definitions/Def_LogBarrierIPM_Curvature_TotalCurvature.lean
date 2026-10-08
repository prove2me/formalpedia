-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
-- name    : LogBarrierIPM_Curvature_TotalCurvature
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:05.141773+00:00
-- url     : https://prove2.me/theorems/8e9a7526-3547-48eb-bb6a-d240ebcc561a
-- title:
--   Turning angle $\angle UVW$ and total curvature $\kappa(\sigma, I)$ of a curve, as a supremum over inscribed polygons
-- statement:
--   Work in $\mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. For non-null $x,y\in\mathbb R^d$, $\angle xy\in[0,\pi]$ is the angle with
--   $$\cos\angle xy=\frac{\langle x,y\rangle}{\|x\|\,\|y\|}.$$
--
--   1. **Turning angle.** For three points $U,V,W\in\mathbb R^d$ with $U\neq V$ and $V\neq W$, $\angle UVW$ is the angle formed by the vectors $UV=V-U$ and $VW=W-V$, that is $\angle UVW=\angle(V-U)(W-V)$. It is $0$ when the three points are aligned in this order and $\pi$ when the curve turns back.
--   2. **Inscribed polygons.** Let $\sigma$ be a curve in $\mathbb R^d$ parameterized over a set $I\subseteq\mathbb R$. For parameters $\mu_0<\mu_1<\dots<\mu_p$ in $I$, the polygonal curve with vertices $\sigma(\mu_0),\dots,\sigma(\mu_p)$ is inscribed in $\sigma$, and its total curvature is the sum of the angles between consecutive segments,
--   $$\sum_{k=1}^{p-1}\angle\,\sigma(\mu_{k-1})\,\sigma(\mu_k)\,\sigma(\mu_{k+1}).$$
--   3. **Total curvature.** The total curvature of $\sigma$ over $I$ is
--   $$\kappa(\sigma,I)=\sup\Big\{\sum_{k=1}^{p-1}\angle\,\sigma(\mu_{k-1})\sigma(\mu_k)\sigma(\mu_{k+1})\ :\ p\ge0,\ \mu_0<\dots<\mu_p,\ \mu_k\in I\Big\}\in[0,+\infty].$$
--   For $I=[a,b]$ this is the paper's $\kappa(\sigma,[a,b])$; for a twice continuously differentiable curve it coincides with $\int\|\sigma''(s)\|\,ds$ in arc length.
--
--   These are the notions in which the paper measures how much the central path of a linear program winds.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin d)` and the angle is Mathlib's `InnerProductGeometry.angle (V - U) (W - V)`, the turning angle, not the vertex angle `EuclideanGeometry.angle U V W` (which is $\pi$ minus it). The paper defines $\angle UVW$ only for $U\ne V$ and $V\ne W$; for a degenerate triple the Lean value is set to $0$, so repeated points never add curvature (Mathlib's angle with the zero vector is $\pi/2$). The supremum is taken in `EReal`, so an unbounded set of polygon curvatures gives $+\infty$, not a junk value. The parameters are a sequence $\mu:\mathbb N\to\mathbb R$ of which only $\mu_0,\dots,\mu_p$ are read.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 21, §5 (angles ∠xy, ∠UVW and total curvature κ(σ,[a,b]))

import Mathlib

namespace LogBarrierIPM.Curvature

/-- The turning angle `∠UVW` of three points of `ℝ^d` (p. 21): the angle in `[0, π]` between the
vectors `UV = V - U` and `VW = W - V`, with `cos ∠ = ⟨UV, VW⟩ / (‖UV‖ ‖VW‖)` for the Euclidean inner
product. The paper defines it only for `U ≠ V` and `V ≠ W`; for a degenerate triple it is set to `0`
here, so that repeated points never contribute to a total curvature. -/
noncomputable def turningAngle {d : ℕ} (U V W : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if U = V ∨ V = W then 0 else InnerProductGeometry.angle (V - U) (W - V)

/-- `μ 0, …, μ p` is an admissible subdivision of the parameter set `I`: every `μ k` (`k ≤ p`) lies
in `I` and `μ 0 < μ 1 < ⋯ < μ p`. Values of `μ` beyond `p` are ignored. -/
def IsInscribedSubdivision (I : Set ℝ) (p : ℕ) (μ : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, k ≤ p → μ k ∈ I) ∧ ∀ k : ℕ, k < p → μ k < μ (k + 1)

/-- Total curvature of the polygonal curve inscribed in `σ` with vertices
`σ (μ 0), …, σ (μ p)`: the sum of the turning angles at its interior vertices,
`∑_{k=1}^{p-1} ∠ σ(μ_{k-1}) σ(μ_k) σ(μ_{k+1})` (written here with the index shifted by one). -/
noncomputable def inscribedPolygonCurvature {d : ℕ} (σ : ℝ → EuclideanSpace ℝ (Fin d)) (p : ℕ)
    (μ : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p - 1), turningAngle (σ (μ k)) (σ (μ (k + 1))) (σ (μ (k + 2)))

/-- Total curvature `κ(σ, I)` of a curve `σ` parameterized over `I ⊆ ℝ` (p. 21): the supremum, in
`EReal`, of the total curvatures of all polygonal curves inscribed in `σ`, i.e. over all
`μ_0 < μ_1 < ⋯ < μ_p` in `I`. For `I = [a, b]` this is the paper's `κ(σ, [a, b])`. -/
noncomputable def totalCurvature {d : ℕ} (σ : ℝ → EuclideanSpace ℝ (Fin d)) (I : Set ℝ) : EReal :=
  ⨆ (p : ℕ) (μ : ℕ → ℝ) (_ : IsInscribedSubdivision I p μ),
    ((inscribedPolygonCurvature σ p μ : ℝ) : EReal)

end LogBarrierIPM.Curvature


