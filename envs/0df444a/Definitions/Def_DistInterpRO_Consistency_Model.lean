-- Prove2me | Definitions.Def_DistInterpRO_Consistency_Model
-- name    : DistInterpRO_Consistency_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:47:33.394787+00:00
-- url     : https://prove2.me/theorems/8f55e520-cf45-4c5a-91e3-348dd04c66df
-- title:
--   Boxes $\mathcal Z_i$, the set $\mathcal P_n$, the uniform box kernel, the kernel density estimator $h_n$, the box-robust objective and the modulus $d(\epsilon)$
-- statement:
--   Throughout, $\mathbb R^m$ carries the sup norm $\|z\|_\infty=\max_{1\le k\le m}|z_k|$ and its Borel $\sigma$-algebra, and $dx$ is Lebesgue measure. This file defines the objects of §3 of Xu, Caramanis and Mannor (2012).
--
--   1. **Boxes.** For a point $x_i\in\mathbb R^m$ and a radius $\epsilon$, the box
--   $$\mathcal Z_i=\{x_i+\delta \mid \|\delta\|_\infty\le\epsilon\},$$
--   the closed sup-norm ball of radius $\epsilon$ centred at $x_i$.
--   2. **The distribution set $\mathcal P_n$** of Eq. (6): given sets $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$, the Borel probability measures $\mu$ on $\mathbb R^m$ such that
--   $$\mu\Big(\bigcup_{i\in S}\mathcal Z_i\Big)\ \ge\ \frac{|S|}{n}\qquad\text{for every } S\subseteq\{1,\dots,n\}.$$
--   3. **The uniform box kernel**
--   $$K(z)=\frac{\mathbf 1(\|z\|_\infty\le1)}{2^m}.$$
--   4. **The kernel density estimator** built from a sample $x_1,\dots,x_n\in\mathbb R^m$ with bandwidth $\epsilon$:
--   $$h_n(x)=(n\epsilon^m)^{-1}\sum_{i=1}^n K\Big(\frac{x-x_i}{\epsilon}\Big).$$
--   5. **The box-robust sample objective** of a utility $f:V\times\mathbb R^m\to\mathbb R$ at a decision $v\in V$:
--   $$J_n(v)=\frac1n\sum_{i=1}^n\ \inf_{\|\delta_i\|_\infty\le\epsilon} f(v,x_i+\delta_i)=\sum_{i=1}^n\frac1n\inf_{x_i'\in\mathcal Z_i}f(v,x_i').$$
--   6. **The equicontinuity modulus**
--   $$d(\epsilon)=\sup_{v,\,x,\ \|\delta\|_\infty\le\epsilon}|f(v,x)-f(v,x+\delta)|.$$
--
--   These are the objects in terms of which Theorem 3.1 and its proof are stated: the RO problem maximises $J_n$, and the proof shows that $h_n$ is (the density of) a member of $\mathcal P_n$.
--
--   **Formalization Note** $\mathbb R^m$ is `Fin m → ℝ`, whose Mathlib norm is the sup norm, so `Metric.closedBall` is the $\ell_\infty$ box and $K$ integrates to $1$. Indices $1,\dots,n$ become `Fin n` $=\{0,\dots,n-1\}$. The kernel density estimator divides by the bandwidth $\epsilon$ passed to it; the paper's display on p. 98 prints $K((x-x_i)/\epsilon)$, which the proof on p. 99 writes as $K((x-x_i)/\epsilon(n))$, and the bandwidth is $\epsilon(n)$ wherever the estimator is used. For $n=0$ both $h_n$ and $J_n$ are $0$ (Lean's $1/0=0$ and the empty sum); every statement using them assumes $n\ge1$ or takes a limit. The infima in $J_n$ and the suprema in $d$ are real `⨅`/`⨆` over nonempty index sets (take $\delta=0$), and every statement using them assumes $|f|\le C$, so they are the true infimum and supremum. The paper's "max" in $d(\epsilon)$ is read as a supremum.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 98, Theorem 3.1 (d(ϵ) and the RO formulation), proof of Theorem 3.1 (the sets 𝒵ᵢ, Eq. (6) for 𝒫ₙ, the estimator hₙ and kernel K)

import Mathlib

open MeasureTheory

namespace DistInterpRO.Consistency

/-- The box `𝒵ᵢ = {xᵢ + δ | ‖δ‖∞ ≤ ε}` around a sample point `xᵢ` (Xu–Caramanis–Mannor 2012,
p. 98). On `Fin m → ℝ` the norm is the sup norm `‖·‖∞`, so this is the closed sup-norm ball
of radius `ε` centred at `xᵢ`. -/
def box {m : ℕ} (xi : Fin m → ℝ) (ε : ℝ) : Set (Fin m → ℝ) :=
  Metric.closedBall xi ε

/-- The distribution set `𝒫ₙ` of Eq. (6) (p. 98): the Borel probability measures `μ` on `ℝᵐ`
such that `μ(⋃_{i ∈ S} 𝒵ᵢ) ≥ |S|/n` for every `S ⊆ [1 : n]` (indices are `Fin n`). -/
def distSet {m n : ℕ} (Z : Fin n → Set (Fin m → ℝ)) : Set (Measure (Fin m → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧
    ∀ S : Finset (Fin n), ENNReal.ofReal ((S.card : ℝ) / n) ≤ μ (⋃ i ∈ S, Z i)}

/-- The uniform box kernel `K(z) = 𝟏(‖z‖∞ ≤ 1) / 2ᵐ` (p. 98). -/
noncomputable def kernel {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  if ‖z‖ ≤ 1 then 1 / (2 : ℝ) ^ m else 0

/-- The kernel density estimator
`hₙ(x) = (n ε^m)⁻¹ ∑_{i=1}^n K((x − xᵢ)/ε)` built from the sample `x₁, …, xₙ` (here
`xs : Fin n → ℝᵐ`) with bandwidth `ε` (p. 98, with the printed `/ϵ` read as `/ϵ(n)`, as on
p. 99). For `n = 0` it is the zero function. -/
noncomputable def kde {m n : ℕ} (ε : ℝ) (xs : Fin n → Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ((n : ℝ) * ε ^ m)⁻¹ * ∑ i : Fin n, kernel (ε⁻¹ • (x - xs i))

/-- The box-robust sample objective of Theorem 3.1 (p. 98):
`(1/n) ∑_{i=1}^n inf_{‖δᵢ‖∞ ≤ ε} f(v, xᵢ + δᵢ)`.
Each infimum is over the nonempty index set `{δ | ‖δ‖∞ ≤ ε}` when `ε ≥ 0`. -/
noncomputable def roObjective {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ) (ε : ℝ)
    (xs : Fin n → Fin m → ℝ) (v : V) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xs i + δ.1)

/-- The equicontinuity modulus of Theorem 3.1 (ii) (p. 98):
`d(ε) = sup_{v, x, ‖δ‖∞ ≤ ε} |f(v, x) − f(v, x + δ)|` (the printed `max` read as `sup`). -/
noncomputable def modulus {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ⨆ v : V, ⨆ x : Fin m → ℝ, ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, |f v x - f v (x + δ.1)|

end DistInterpRO.Consistency


