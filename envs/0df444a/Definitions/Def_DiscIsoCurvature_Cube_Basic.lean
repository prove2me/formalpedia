-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_Basic
-- name    : DiscIsoCurvature_Cube_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:06:52.006081+00:00
-- url     : https://prove2.me/theorems/c862a875-06e9-4a53-9d1e-2fb12de6cac6
-- title:
--   The Boolean cube {±1}^n, distributions, expectation, variance, entropy, L^p norms, and the matrix norms ‖·‖₁, ‖·‖₂ and λ_min
-- statement:
--   The **Boolean hypercube** $\Omega=\{\pm1\}^n$ is encoded as $\mathtt{BoolCube}\ n=\mathtt{Fin}\ n\to\mathtt{Bool}$ ($\mathtt{true}\leftrightarrow+1$), and for $x\in\Omega$ and a coordinate $i$, $x^i$ is $x$ with its $i$-th coordinate flipped; $x^{ij}=(x^i)^j$.
--
--   A **distribution** on a finite set $\Omega$ is $\mu:\Omega\to\mathbb R$ with $\mu(x)\ge0$ and $\sum_x\mu(x)=1$; it is **fully supported** if $\mu(x)>0$ for every $x$. For $f:\Omega\to\mathbb R$,
--   $$\mathbb E_\mu[f]=\sum_x\mu(x)f(x),\qquad \mathrm{Var}_\mu(f)=\mathbb E_\mu[f^2]-(\mathbb E_\mu f)^2,\qquad \mathrm{Ent}_\mu[f]=\mathbb E_\mu[f\log f]-\mathbb E_\mu[f]\log\mathbb E_\mu[f],$$
--   with $0\log0=0$, and $\|f\|_{p,\mu}=(\mathbb E_\mu|f|^p)^{1/p}$.
--
--   For vectors and $n\times n$ real matrices: $\|v\|_2=(\sum_iv_i^2)^{1/2}$; $\|M\|_1=\max_j\sum_i|M_{ij}|$ (maximum column sum); $\|M\|_2=\sup_{v\ne0}\|Mv\|_2/\|v\|_2$ (spectral norm); $\lambda_{\min}(A)=\inf_{v\ne0}v^\top Av/v^\top v$, the minimum eigenvalue of a symmetric $A$.
--
--   These are the basic objects of §1.1, §3 and the matrix-norm conventions of p. 4.
--
--   **Formalization Note.** Coordinates are `Fin n` (the paper's $[n]$ shifted to start at $0$). The entropy uses `f * Real.log f`, which is $0$ at $f=0$, so $0\log0=0$ holds. $\|M\|_2$ and $\lambda_{\min}$ are a supremum and an infimum over the nonzero vectors, a nonempty bounded set for $n\ge1$; at $n=0$ both are $0$, and so is $\|M\|_1$.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 1 §1.1, p. 4 (matrix norms), p. 13 §3.1, p. 17 Definition 3.11, p. 35 Theorem 6.4 (λ_min)

import Mathlib

namespace DiscIsoCurvature.Cube

/-!
# The Boolean cube, distributions on a finite set, expectation, variance, entropy, `L^p` norms,
# and the matrix norms `‖·‖₁`, `‖·‖₂`, `λ_min`

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…): §1.1 (p. 1), p. 4 (matrix norms), §3.1 (p. 13),
Definition 3.11 (p. 17), Theorem 3.16 (p. 17), Theorem 6.4 (p. 35).

* `BoolCube n = Fin n → Bool` encodes `{±1}^n` (`true` ↔ `+1`, `false` ↔ `−1`); coordinates are
  indexed by `Fin n` (the paper's `[n]`, shifted to start at `0`).
* `flip x i` is `x^i` (coordinate `i` flipped); `x^{ij} = flip (flip x i) j`.
* A distribution on a finite set `Ω` is a function `μ : Ω → ℝ` with nonnegative values summing to
  `1` (`IsDist`); it is fully supported (`IsFullDist`) when every value is positive.
* `expect μ f = ∑ₓ μ(x) f(x)`, `var μ f = E_μ[f²] − (E_μ f)²`,
  `ent μ f = E_μ[f log f] − E_μ[f] log E_μ[f]` (Lean's `0 * log 0 = 0` is the paper's convention
  `0 log 0 = 0`), `lpNorm μ p f = (E_μ |f|^p)^{1/p}`.
* `l2norm v = (∑ᵢ vᵢ²)^{1/2}` on `ℝ^n`; `colSumNorm R = max_j ∑ᵢ |R_ij|` (the paper's `‖R‖₁`);
  `specNorm R = sup_{v ≠ 0} ‖Rv‖₂/‖v‖₂` (the paper's `‖R‖₂`); `lambdaMin A = inf_{v ≠ 0} vᵀAv / vᵀv`,
  which is the minimum eigenvalue of a symmetric `A` (Rayleigh–Ritz).
-/

/-- The Boolean hypercube `{±1}^n`, encoded as `Fin n → Bool` (`true` ↔ `+1`, `false` ↔ `−1`). -/
abbrev BoolCube (n : ℕ) := Fin n → Bool

/-- `x^i`: the point obtained from `x` by flipping its `i`-th coordinate (§1.1, p. 1). -/
def flip {n : ℕ} (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)

/-- `μ` is a probability distribution on the finite set `Ω`: `μ(x) ≥ 0` and `∑ₓ μ(x) = 1`. -/
def IsDist {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- `μ` is a fully supported probability distribution on `Ω`: `μ(x) > 0` and `∑ₓ μ(x) = 1`. -/
def IsFullDist {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : Prop :=
  (∀ x, 0 < μ x) ∧ ∑ x, μ x = 1

/-- Expectation `E_μ[f] = ∑ₓ μ(x) f(x)` (§1.1, p. 1). -/
noncomputable def expect {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ x * f x

/-- Variance `Var_μ(f) = E_μ[f²] − (E_μ[f])²` (§1.1, p. 1; Definition 3.11, p. 17). -/
noncomputable def var {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  expect μ (fun x => f x ^ 2) - expect μ f ^ 2

/-- Entropy `Ent_μ[f] = E_μ[f log f] − E_μ[f] log E_μ[f]` (Definition 3.11, p. 17), used for
`f ≥ 0`; `0 log 0 = 0` holds in Lean because `0 * Real.log 0 = 0`. -/
noncomputable def ent {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  expect μ (fun x => f x * Real.log (f x)) - expect μ f * Real.log (expect μ f)

/-- The `L^p(μ)` norm `‖f‖_{p,μ} = (E_μ |f|^p)^{1/p}` (real powers). -/
noncomputable def lpNorm {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (p : ℝ) (f : Ω → ℝ) : ℝ :=
  (expect μ (fun x => |f x| ^ p)) ^ (1 / p)

/-- Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` on `ℝ^n`. -/
noncomputable def l2norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- `‖M‖₁ = max_j ∑ᵢ |M_ij|`, the maximum column sum (p. 4). -/
noncomputable def colSumNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ j, ∑ i, |M i j|

/-- `‖M‖₂ = sup_{v ≠ 0} ‖Mv‖₂ / ‖v‖₂`, the spectral (`ℓ² → ℓ²` operator) norm (p. 4). The
supremum is over a set of reals bounded above (finite dimension); it is `0` when `n = 0`. -/
noncomputable def specNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ v : {v : Fin n → ℝ // v ≠ 0}, l2norm (M.mulVec v.1) / l2norm v.1

/-- `λ_min(A) = inf_{v ≠ 0} vᵀAv / vᵀv`; for a symmetric matrix `A` this is its minimum
eigenvalue (Theorem 6.4, p. 35). It is `0` when `n = 0`. -/
noncomputable def lambdaMin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨅ v : {v : Fin n → ℝ // v ≠ 0}, (v.1 ⬝ᵥ A.mulVec v.1) / (v.1 ⬝ᵥ v.1)

end DiscIsoCurvature.Cube


