-- Prove2me | Definitions.Def_RegMCBSDE_Projection_Projection
-- name    : RegMCBSDE_Projection_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:02.327178+00:00
-- url     : https://prove2.me/theorems/5d0cc219-37df-42e4-9096-a71f813dbbff
-- title:
--   §2.2, §3, pp. 5–6, 9 — L2 projections on function bases, residuals and the discrete BSDE (5)–(6)
-- statement:
--   This file defines the $\mathbf L_2$ projections used by the regression scheme and the discrete-time BSDE it approximates.
--
--   **Projection.** For a finite family $\phi=[\phi_1,\dots,\phi_n]^*$ of random variables, $\mathcal P_\phi(U)$ is the orthogonal projection, in $\mathbf L_2(\Omega,\mathbb P)$, of a square-integrable random variable $U$ on the linear span of $\phi_1,\dots,\phi_n$, and
--   $$\mathcal R_\phi(U)=U-\mathcal P_\phi(U)$$
--   is the projection error.
--
--   **Function bases.** For $0\le l\le q$ and $0\le k\le N-1$, a measurable map $p_{l,k}:\mathbb R^{d'}\to\mathbb R^{n_{l,k}}$ gives the basis $p_{l,k}(P^N_{t_k})$ at time $t_k$. It is required that $\mathbb E|p_{l,k}(P^N_{t_k})|^2<\infty$ and that the Gram matrix $\mathbb E(p_{l,k}p_{l,k}^*)$ is invertible. The basis $p_{0,k}$ serves $Y$, and $p_{l,k}$, $1\le l\le q$, serves the $l$-th component of $Z$.
--
--   **Discrete BSDE.** With $h=T/N$ and $\mathbb E_k=\mathbb E(\cdot\mid\mathcal F_k)$, a pair $(Y^N,Z^N)$ solves (5)–(6) if $Y^N_{t_N}=\Phi^N(P^N_{t_N})$, each $Y^N_{t_k}$ ($k\le N$) and $Z^N_{t_k}\in\mathbb R^q$ ($k<N$) is $\mathcal F_k$-measurable and square integrable, and for $k<N$, $1\le l\le q$,
--   $$Z^N_{l,t_k}=\frac1h\,\mathbb E_k\big(Y^N_{t_{k+1}}\Delta W_{l,k}\big),\qquad Y^N_{t_k}=\mathbb E_k\big(Y^N_{t_{k+1}}\big)+h\,f\big(t_k,S^N_{t_k},Y^N_{t_k},Z^N_{t_k}\big),$$
--   almost surely. Equation (6) is implicit in $Y^N_{t_k}$; for $h$ small enough it has exactly one solution.
--
--   The discrete BSDE is the reference against which the projection scheme of §4 is compared; the residuals $\mathcal R_{p_{l,k}}$ of its solution measure how well the bases represent it.
--
--   **Formalization Note** The projection is the orthogonal projection of $\mathbf L_2(\Omega,\mathbb P)$ onto the (closed, finite-dimensional) span of the basis coordinates; it is not defined through the normal equations. For a $U$ that is not square integrable it is set to $0$, a value no statement of this mission evaluates. The discrete BSDE is a relation, not a constructed object: the theorems hold for every solution.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 5–6, §2.2 (projection on function bases), and p. 9, §3, Eqs. (5)–(6)

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Setting

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- The subspace of `𝐋₂(Ω, P)` spanned by the coordinates `φ_1, …, φ_n` of a finite family
`φ = [φ_1, …, φ_n]^*` of random variables (a coordinate that is not square integrable contributes
nothing). It is finite dimensional, hence closed; the closure is taken only so that Lean sees the
orthogonal projection onto it. -/
noncomputable abbrev basisSpace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (φ : Ω → Fin n → ℝ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ j, (g : Ω → ℝ) =ᵐ[P] fun ω => φ ω j}).topologicalClosure

/-- **The projection `𝒫_φ(U)`** (§2.2, p. 5): the `𝐋₂(Ω, P)` orthogonal projection of the
random variable `U` on the finite family `φ`. It is defined for square-integrable `U` (for any
other `U` it is set to `0`, a value never used by the statements of this mission). -/
noncomputable def proj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (φ : Ω → Fin n → ℝ) (U : Ω → ℝ) : Ω → ℝ := by
  classical
  exact if hU : MemLp U 2 P then ⇑((basisSpace P φ).starProjection (hU.toLp U)) else 0

/-- **The projection error `ℛ_φ(U) = U - 𝒫_φ(U)`** (§2.2, p. 5). -/
noncomputable def resid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (φ : Ω → Fin n → ℝ) (U : Ω → ℝ) : Ω → ℝ :=
  fun ω => U ω - proj P φ U ω

/-- The function basis `p_{l,k}(P^N_{t_k})` at time `t_k`, as a random vector. -/
def basisAt {Ω : Type*} {d' q : ℕ} {n : Fin (q + 1) → ℕ → ℕ}
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (l : Fin (q + 1)) (k : ℕ) :
    Ω → Fin (n l k) → ℝ :=
  fun ω => p l k (PN k ω)

/-- **The function bases** (§2.2, pp. 5–6). For `0 ≤ l ≤ q` (indexed by `Fin (q + 1)`) and
`0 ≤ k ≤ N - 1`, `p l k : ℝ^{d'} → ℝ^{n l k}` is measurable, `𝔼|p_{l,k}(P^N_{t_k})|^2 < ∞`, and the
Gram matrix `𝔼(p_{l,k} p_{l,k}^*)` is invertible. The basis `l = 0` serves `Y`; the basis
`l = m + 1` (`m : Fin q`) serves `Z_{m+1}` and is paired with component `m` of `ΔW k`. -/
structure IsBasis {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d' q : ℕ} (N : ℕ)
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (n : Fin (q + 1) → ℕ → ℕ)
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ) : Prop where
  measurable : ∀ l, ∀ k < N, Measurable (p l k)
  memLp : ∀ l, ∀ k < N, ∀ j, MemLp (fun ω => p l k (PN k ω) j) 2 P
  gram_det_ne_zero : ∀ l, ∀ k < N,
    (Matrix.of fun i j => ∫ ω, p l k (PN k ω) i * p l k (PN k ω) j ∂P).det ≠ 0

/-- **The discrete BSDE (5)–(6)** (§3, p. 9), as a relation. `(Y, Z)` solves it if, with
`h = T/N`, `t_k = k h` and `𝔼_k = 𝔼(· | 𝓕_k)`:

* `Y_{t_N} = Φ^N(P^N_{t_N})`;
* for `k ≤ N`, `Y_{t_k}` is `𝓕_k`-measurable and square integrable; for `k < N`, `Z_{t_k} ∈ ℝ^q`
  is `𝓕_k`-measurable and square integrable;
* for `k < N` and each component `m : Fin q` (the paper's `l = m + 1`),
  `Z_{l,t_k} = h⁻¹ 𝔼_k(Y_{t_{k+1}} ΔW_{l,k})` (5), and
  `Y_{t_k} = 𝔼_k(Y_{t_{k+1}}) + h f(t_k, S^N_{t_k}, Y_{t_k}, Z_{t_k})` (6),

all equalities almost surely. For `h` small enough a solution exists and is unique (p. 9). -/
structure IsDiscreteBSDE {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℕ mΩ) {d q d' : ℕ} (T : ℝ) (N : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (S0 : EuclideanSpace ℝ (Fin d)) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ)
    (Y : ℕ → Ω → ℝ) (Z : ℕ → Ω → EuclideanSpace ℝ (Fin q)) : Prop where
  terminal : Y N =ᵐ[P] fun ω => ΦN (PN N ω)
  Y_measurable : ∀ k ≤ N, StronglyMeasurable[𝓕 k] (Y k)
  Y_memLp : ∀ k ≤ N, MemLp (Y k) 2 P
  Z_measurable : ∀ k < N, StronglyMeasurable[𝓕 k] (Z k)
  Z_memLp : ∀ k < N, MemLp (Z k) 2 P
  eq_5 : ∀ k < N, ∀ m : Fin q,
    (fun ω => Z k ω m) =ᵐ[P]
      fun ω => (T / N)⁻¹ * (P[fun ω' => Y (k + 1) ω' * ΔW k ω' m | 𝓕 k]) ω
  eq_6 : ∀ k < N,
    Y k =ᵐ[P] fun ω => (P[Y (k + 1) | 𝓕 k]) ω
      + (T / N) * f (gridTime T N k) (euler T N b σ S0 ΔW k ω) (Y k ω) (Z k ω)

end RegMCBSDE.Projection


