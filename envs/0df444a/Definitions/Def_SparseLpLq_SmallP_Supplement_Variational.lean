-- Prove2me | Definitions.Def_SparseLpLq_SmallP_Supplement_Variational
-- name    : SparseLpLq_SmallP_Supplement_Variational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:09:21.561863+00:00
-- url     : https://prove2.me/theorems/96cdc0b7-7a0c-43d0-a2e1-473de238fdbb
-- title:
--   p. 3 and Definition 3.1 — horizon subdifferential, Φ and δ_FEA, the normal cone, and stationary points of (1.4)
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,+\infty]$, with $\mathbb R^n$ carrying the Euclidean inner product. Following [33, Definition 8.3] (p. 3), the regular subdifferential $\widehat\partial f(x)$ and the limiting subdifferential $\partial f(x)$ at $x\in\mathrm{dom}\,f$ are the published definitions `NAPPAL.VPEB.frechetSubdiff` and `NAPPAL.VPEB.limSubdiff`. This file adds:
--
--   1. **Horizon subdifferential**
--   $$\partial^\infty f(x):=\big\{d : \exists\,x^k\xrightarrow{f}x,\ \lambda_kd^k\to d,\ \lambda_k\downarrow0\ \text{with}\ d^k\in\widehat\partial f(x^k)\big\},$$
--   where $x^k\xrightarrow{f}x$ means $x^k\to x$ and $f(x^k)\to f(x)$.
--   2. $\Phi(x)=\|x\|_p^p$ and the indicator $\delta_{\mathrm{FEA}(A,b,\sigma,1)}$ ($0$ on the set, $+\infty$ off it) as extended-real-valued functions.
--   3. **Normal cone** $\mathcal N_{\mathrm{FEA}(A,b,\sigma,1)}(x)=\partial\delta_{\mathrm{FEA}(A,b,\sigma,1)}(x)$.
--   4. **Stationary point** (Definition 3.1, p. 12): $x^*$ is a stationary point of (1.4) with $0<p<1$ if $x^*\in\mathrm{FEA}(A,b,\sigma,1)$ and
--   $$0\in\partial\big(\Phi+\delta_{\mathrm{FEA}(A,b,\sigma,1)}\big)(x^*). \tag{3.2}$$
--
--   These enter Algorithm 1 (condition (3.8)) and Theorem 3.1 (condition (3.14) and its conclusion).
--
--   **Formalization Note** $\lambda_k\downarrow0$ is written $\lambda_k>0$, $\lambda_k\to0$ (a positive null sequence has a decreasing subsequence, along which the other limits persist). The functions live on `EuclideanSpace ℝ (Fin n)`. The normal cone is the limiting subdifferential of the indicator; since $\mathrm{FEA}(A,b,\sigma,1)$ is convex it coincides with the normal cone of convex analysis.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 3 (subdifferentials), p. 4 (indicator δ), p. 12 (Φ, (3.2), Definition 3.1), p. 14 ((3.14), 𝒩)

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff
import Definitions.Def_NAPPAL_VPEB_limSubdiff

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP

/-! ### Subdifferentials, normal cone, stationarity (pp. 3, 12, 14) -/

/-- **Horizon subdifferential** `∂^∞f(x)` (p. 3, [33, Definition 8.3]): `d` with `x ∈ dom f` and
sequences `xₖ → x`, `f(xₖ) → f(x)`, `dₖ ∈ ∂̂f(xₖ)`, `λₖ > 0`, `λₖ → 0`, `λₖ dₖ → d`. The regular
subdifferential `∂̂f` is the published `NAPPAL.VPEB.frechetSubdiff`. -/
def horizonSubdiff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : Set X :=
  {d | f x ≠ ⊤ ∧ ∃ (xs ds : ℕ → X) (lam : ℕ → ℝ),
    Filter.Tendsto xs Filter.atTop (𝓝 x) ∧
    Filter.Tendsto (fun k => f (xs k)) Filter.atTop (𝓝 (f x)) ∧
    (∀ k, ds k ∈ NAPPAL.VPEB.frechetSubdiff f (xs k)) ∧
    (∀ k, 0 < lam k) ∧ Filter.Tendsto lam Filter.atTop (𝓝 0) ∧
    Filter.Tendsto (fun k => lam k • ds k) Filter.atTop (𝓝 d)}

/-- `Φ(x) = ‖x‖_p^p` on Euclidean space `ℝⁿ`, as an extended-real-valued function. -/
noncomputable def PhiE {n : ℕ} (p : ℝ) (z : EuclideanSpace ℝ (Fin n)) : EReal :=
  ((lpObj p (WithLp.ofLp z) : ℝ) : EReal)

/-- The indicator `δ_{FEA(A,b,σ,1)}` on Euclidean space: `0` on the set, `+∞` off it. -/
noncomputable def indFEA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : EReal :=
  by classical exact if WithLp.ofLp z ∈ FEA A b σ 1 then 0 else ⊤

/-- The normal cone `𝒩_{FEA(A,b,σ,1)}(x) = ∂δ_{FEA(A,b,σ,1)}(x)` (limiting subdifferential of the
indicator; `FEA(A,b,σ,1)` is convex, so this is the normal cone of convex analysis). -/
def normalConeFEA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (x : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  NAPPAL.VPEB.limSubdiff (indFEA A b σ) (WithLp.toLp 2 x)

/-- Definition 3.1: `x*` is a stationary point of (1.4) with `0 < p < 1` if
`x* ∈ FEA(A,b,σ,1)` and `0 ∈ ∂(Φ + δ_{FEA(A,b,σ,1)})(x*)` (3.2), `∂` the limiting subdifferential. -/
def IsStationary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p : ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ FEA A b σ 1 ∧
    (0 : EuclideanSpace ℝ (Fin n)) ∈
      NAPPAL.VPEB.limSubdiff (fun z => PhiE p z + indFEA A b σ z) (WithLp.toLp 2 x)

end SparseLpLq.SmallP.Supplement


