-- Prove2me | Definitions.Def_HryniewiczCriterion_SelfLinking
-- name    : HryniewiczCriterion_SelfLinking
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T18:28:50.566026+00:00
-- url     : https://prove2.me/theorems/3b688271-e472-4637-8dac-deb441e06af6
-- title:
--   Linking numbers in $S^3$ and the self-linking number of a periodic orbit
-- statement:
--   **Linking number.** Orient $\mathbb{R}^4$ by $dq_1\wedge dp_1\wedge dq_2\wedge dp_2$ and $S^3$ as the boundary of the unit ball. For a unit vector $N$, stereographic projection $\sigma_N(y)=(y-\langle y,N\rangle N)/(1-\langle y,N\rangle)$ maps $S^3\setminus\{N\}$ onto $N^\perp\cong\mathbb{R}^3$. It preserves orientation when $N^\perp$ is oriented by $\det(-N,\cdot,\cdot,\cdot)$. For two disjoint $1$-periodic loops $\gamma_1,\gamma_2$ in $S^3$ that miss $N$, put $A=\sigma_N\circ\gamma_1$ and $B=\sigma_N\circ\gamma_2$. The Gauss integral is
--   $$\operatorname{lk}_N(\gamma_1,\gamma_2)=\frac{1}{4\pi}\int_0^1\!\!\int_0^1\frac{\det\big(-N,\,A'(s),\,B'(t),\,A(s)-B(t)\big)}{|A(s)-B(t)|^3}\,dt\,ds.$$
--   The integer $n$ is **the linking number** of $\gamma_1,\gamma_2$ if some unit $N$ misses both loops and $\operatorname{lk}_N=n$ for every such $N$.
--
--   **Self-linking number** (Definition 1.5). For a periodic orbit $P=(x,T)$ on a star-shaped $S$, let $\gamma(s)=x(Ts)/|x(Ts)|$. Let $\gamma_\epsilon(s)$ be the radial projection of $x(Ts)+\epsilon Z_1(x(Ts))$, the push-off of $P$ along the global section $Z_1$ of $\xi$. Then $\operatorname{sl}(P)=n$ means that $\gamma$ and $\gamma_\epsilon$ have linking number $n$ for every sufficiently small $\epsilon>0$.
--
--   Hryniewicz defines $\operatorname{sl}$ by pushing off along a non-vanishing section of $\xi$ over a Seifert surface and intersecting with that surface. The section $Z_1$ is global, so it restricts to such a section over every spanning disk, and the intersection number equals the linking number in $S\cong S^3$. With these orientations a Hopf fibre of the round sphere has $\operatorname{sl}=-1$, and two Hopf fibres have linking number $+1$.
--
--   Two periodic orbits **link non-trivially** if their loops have a linking number and it is non-zero.
--
--   **Formalization Note** Linking is computed after radial projection $S\to S^3$, which is a diffeomorphism for star-shaped $S$. The definition quantifies over every admissible projection point $N$ and also asserts that one exists, so it cannot hold vacuously.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Definition 1.5, p. 3

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Linking numbers in `S³` and the self-linking number of a periodic orbit

Hryniewicz, arXiv:1105.2077, Definition 1.5 (p. 3). For a periodic orbit `P` on
`S = H⁻¹(1)`, `sl(P)` is the linking number of `P` with its push-off along a
non-vanishing section of `ξ`. Since `ξ` has the global frame `Z₁, Z₂`, which extends
over every spanning disk, the push-off is taken along `Z₁`. Linking numbers are
computed in `S³` (after radial projection `S → S³`, a diffeomorphism) by the Gauss
integral after stereographic projection.

Orientation: `S³` is oriented as the boundary of the unit ball of `ℝ⁴`, and `ℝ⁴` by
`dq₁ ∧ dp₁ ∧ dq₂ ∧ dp₂ = ½ ω₀ ∧ ω₀`. Stereographic projection from `N` onto `N^⊥` is
orientation preserving when `N^⊥` is oriented by `det(-N, ·, ·, ·)`. With these
conventions a Hopf fibre of the round sphere has `sl = -1`.
-/

namespace HryniewiczCriterion

noncomputable section

/-- Radial projection `x ↦ x / |x|` to the unit sphere `S³`. -/
def radialNormalize (x : R4) : R4 := (euclidNorm x)⁻¹ • x

/-- Stereographic projection of `S³ \ {N}` from the unit vector `N` onto the
hyperplane `N^⊥ ≅ ℝ³`: `y ↦ (y - ⟨y, N⟩ N) / (1 - ⟨y, N⟩)`. -/
def stereographicFrom (N y : R4) : R4 :=
  (1 - dot4 y N)⁻¹ • (y - dot4 y N • N)

/-- The oriented volume of `a, b, c ∈ N^⊥`: `det(-N, a, b, c)` (rows). -/
def volumeIn (N a b c : R4) : ℝ :=
  Matrix.det (Matrix.of ![-N, a, b, c])

/-- The Gauss linking integral of two `1`-periodic loops `γ₁, γ₂` in `S³`, after
stereographic projection from `N`:
`(4π)⁻¹ ∫₀¹ ∫₀¹ vol(A'(s), B'(t), A(s) - B(t)) / |A(s) - B(t)|³ dt ds`,
`A = σ_N ∘ γ₁`, `B = σ_N ∘ γ₂`. -/
def gaussLinkingIntegral (N : R4) (γ₁ γ₂ : ℝ → R4) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
    volumeIn N (deriv (fun s => stereographicFrom N (γ₁ s)) s)
      (deriv (fun t => stereographicFrom N (γ₂ t)) t)
      (stereographicFrom N (γ₁ s) - stereographicFrom N (γ₂ t)) /
    euclidNorm (stereographicFrom N (γ₁ s) - stereographicFrom N (γ₂ t)) ^ 3

/-- `n` is the linking number of the loops `γ₁, γ₂` in `S³`: some unit vector `N`
misses both loops, and the Gauss integral from every such `N` equals `n`. -/
def IsLinkingNumber (γ₁ γ₂ : ℝ → R4) (n : ℤ) : Prop :=
  (∃ N : R4, euclidNorm N = 1 ∧ ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) ∧
  ∀ N : R4, euclidNorm N = 1 → (∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) →
    gaussLinkingIntegral N γ₁ γ₂ = n

/-- The loop `s ↦ x(Ts)/|x(Ts)|`, `s ∈ ℝ/ℤ`, of a periodic orbit, in `S³`. -/
def orbitLoop {H : R4 → ℝ} (P : PeriodicOrbit H) : ℝ → R4 :=
  fun s => radialNormalize (P.x (P.T * s))

/-- The push-off `s ↦ (x(Ts) + ε Z₁(x(Ts))) / |·|` of `P` along `ξ`, in `S³`. -/
def pushOffLoop (H : R4 → ℝ) (P : PeriodicOrbit H) (ε : ℝ) : ℝ → R4 :=
  fun s => radialNormalize (P.x (P.T * s) + ε • xiFrame1 H (P.x (P.T * s)))

/-- `sl(P) = n`: for all small `ε > 0`, `P` and its push-off along `ξ` have linking
number `n`. -/
def HasSelfLinkingNumber (H : R4 → ℝ) (P : PeriodicOrbit H) (n : ℤ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    IsLinkingNumber (orbitLoop P) (pushOffLoop H P ε) n

/-- Two periodic orbits are linked non-trivially: their loops have a linking number,
and it is non-zero. -/
def LinksNontrivially {H : R4 → ℝ} (P Q : PeriodicOrbit H) : Prop :=
  ∃ n : ℤ, n ≠ 0 ∧ IsLinkingNumber (orbitLoop P) (orbitLoop Q) n

end

end HryniewiczCriterion


