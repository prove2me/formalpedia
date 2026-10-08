-- Prove2me | Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
-- name    : HomogBiLimit_OutputFeedback_Homogeneity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:15.02599+00:00
-- url     : https://prove2.me/theorems/0bfda470-ec15-4dea-9df9-bab1701195ae
-- title:
--   Definitions 2.1, 2.3, 2.5 — homogeneity in the 0-limit, the ∞-limit and the bi-limit of functions and vector fields
-- statement:
--   For a weight $r=(r_1,\dots,r_n)$ with all $r_i>0$ and $\lambda>0$, the **dilation** of $x\in\mathbb R^n$ is $\lambda^r\diamond x=(\lambda^{r_1}x_1,\dots,\lambda^{r_n}x_n)$.
--
--   1. A function $\phi:\mathbb R^n\to\mathbb R$ is **homogeneous in the 0-limit** with associated triple $(r_0,d_0,\phi_0)$, where $r_0\in(\mathbb R_+\setminus\{0\})^n$ is the weight, $d_0\ge 0$ the degree and $\phi_0:\mathbb R^n\to\mathbb R$ the approximating function, if $\phi$ and $\phi_0$ are continuous, $\phi_0$ is not identically zero, and for every compact set $C\subseteq\mathbb R^n\setminus\{0\}$ and every $\varepsilon>0$ there is $\lambda_0>0$ such that
--   $$\max_{x\in C}\left|\frac{\phi(\lambda^{r_0}\diamond x)}{\lambda^{d_0}}-\phi_0(x)\right|\le\varepsilon\qquad\forall\lambda\in(0,\lambda_0].$$
--   2. **Homogeneity in the ∞-limit** with triple $(r_\infty,d_\infty,\phi_\infty)$ is the same with "there is $\lambda_\infty>0$ such that the bound holds for all $\lambda\ge\lambda_\infty$".
--   3. A vector field $f=(f_1,\dots,f_n):\mathbb R^n\to\mathbb R^n$ is homogeneous in the 0-limit (resp. ∞-limit) with triple $(r,\mathfrak d,f_0)$, with degree $\mathfrak d\in\mathbb R$, if for each $i$ we have $\mathfrak d+r_i\ge0$ and the component $f_i$ is homogeneous in the 0-limit (resp. ∞-limit) with triple $(r,\mathfrak d+r_i,f_{0,i})$.
--   4. A function or vector field is **homogeneous in the bi-limit** with triples $(r_0,d_0,\phi_0)$ and $(r_\infty,d_\infty,\phi_\infty)$ if it is homogeneous in the 0-limit with the first and in the ∞-limit with the second.
--
--   The approximating functions describe the behaviour of $\phi$ near the origin and near infinity; these notions are the vocabulary of every statement in the mission.
--
--   **Formalization Note** Points of $\mathbb R^n$ are functions `Fin n → ℝ`, and $\lambda^{r_i}$ is the real power `Real.rpow`. The maximum over $C$ is written as a bound for every $x\in C$. The vector-field predicates `IsHomogZeroVF`, `IsHomogInftyVF`, `IsHomogBiLimitVF` are applied componentwise as on p. 3 of the paper; every clause of the paper's definition (positive weights, nonnegative function degree, continuity, approximating function not identically zero, uniformity over compact subsets of $\mathbb R^n\setminus\{0\}$) is kept.
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, pp. 2–4, notation (dilation), Definitions 2.1, 2.3, 2.5

import Mathlib

noncomputable section

namespace HomogBiLimit.OutputFeedback

/-- Andrieu–Praly–Astolfi, notation (p. 2): the dilation `λ^r ⋄ x = (λ^{r₁} x₁, …, λ^{rₙ} xₙ)`
of `x ∈ ℝⁿ` with weight `r`, for `λ > 0` (real powers `Real.rpow`). Coordinates are indexed
by `Fin n`; the paper's `xᵢ` is `x ⟨i - 1, _⟩`. -/
def dil {n : ℕ} (r : Fin n → ℝ) (l : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => l ^ (r i) * x i

/-- Definition 2.1 (first bullet), p. 3: `φ : ℝⁿ → ℝ` is homogeneous in the 0-limit with
associated triple `(r, d, φ₀)`: the weight `r` has all entries `> 0`, the degree `d ≥ 0`,
`φ` and `φ₀` are continuous, `φ₀` is not identically zero, and for every compact
`C ⊆ ℝⁿ ∖ {0}` and every `ε > 0` there is `λ₀ > 0` with
`|φ(λ^r ⋄ x) / λ^d − φ₀(x)| ≤ ε` for all `x ∈ C` and all `λ ∈ (0, λ₀]`. -/
def IsHomogZero {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) (d : ℝ)
    (φ₀ : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, 0 < r i) ∧ 0 ≤ d ∧ Continuous φ ∧ Continuous φ₀ ∧ (∃ x, φ₀ x ≠ 0) ∧
    ∀ C : Set (Fin n → ℝ), IsCompact C → (0 : Fin n → ℝ) ∉ C →
      ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧
        ∀ l : ℝ, 0 < l → l ≤ l₀ → ∀ x ∈ C, |φ (dil r l x) / l ^ d - φ₀ x| ≤ ε

/-- Definition 2.3 (first bullet), pp. 3–4: `φ : ℝⁿ → ℝ` is homogeneous in the ∞-limit with
associated triple `(r, d, φ∞)`: as `IsHomogZero`, but the estimate
`|φ(λ^r ⋄ x) / λ^d − φ∞(x)| ≤ ε` on `C` holds for all `λ ≥ λ∞`, for some `λ∞ > 0`. -/
def IsHomogInfty {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) (d : ℝ)
    (φinf : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, 0 < r i) ∧ 0 ≤ d ∧ Continuous φ ∧ Continuous φinf ∧ (∃ x, φinf x ≠ 0) ∧
    ∀ C : Set (Fin n → ℝ), IsCompact C → (0 : Fin n → ℝ) ∉ C →
      ∀ ε : ℝ, 0 < ε → ∃ linf : ℝ, 0 < linf ∧
        ∀ l : ℝ, linf ≤ l → ∀ x ∈ C, |φ (dil r l x) / l ^ d - φinf x| ≤ ε

/-- Definition 2.5, p. 4 (functions): homogeneous in the bi-limit with associated triples
`(r₀, d₀, φ₀)` (0-limit) and `(r∞, d∞, φ∞)` (∞-limit). -/
def IsHomogBiLimit {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (r₀ : Fin n → ℝ) (d₀ : ℝ) (φ₀ : (Fin n → ℝ) → ℝ)
    (rinf : Fin n → ℝ) (dinf : ℝ) (φinf : (Fin n → ℝ) → ℝ) : Prop :=
  IsHomogZero φ r₀ d₀ φ₀ ∧ IsHomogInfty φ rinf dinf φinf

/-- Definition 2.1 (second bullet), p. 3: the vector field `f = Σ fᵢ ∂/∂xᵢ` on `ℝⁿ` is
homogeneous in the 0-limit with associated triple `(r, 𝔡, f₀)` (`𝔡 ∈ ℝ`): the weight has all
entries `> 0` and, for each `i`, `𝔡 + rᵢ ≥ 0` and the component `fᵢ` is homogeneous in the
0-limit with associated triple `(r, 𝔡 + rᵢ, f₀,ᵢ)`. -/
def IsHomogZeroVF {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (r : Fin n → ℝ) (𝔡 : ℝ)
    (f₀ : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  (∀ i, 0 < r i) ∧
    ∀ i : Fin n, 0 ≤ 𝔡 + r i ∧ IsHomogZero (fun x => f x i) r (𝔡 + r i) (fun x => f₀ x i)

/-- Definition 2.3 (second bullet), p. 4: vector field homogeneous in the ∞-limit with
associated triple `(r, 𝔡, f∞)`. -/
def IsHomogInftyVF {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (r : Fin n → ℝ) (𝔡 : ℝ)
    (finf : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  (∀ i, 0 < r i) ∧
    ∀ i : Fin n, 0 ≤ 𝔡 + r i ∧ IsHomogInfty (fun x => f x i) r (𝔡 + r i) (fun x => finf x i)

/-- Definition 2.5, p. 4 (vector fields): homogeneous in the bi-limit with associated triples
`(r₀, 𝔡₀, f₀)` and `(r∞, 𝔡∞, f∞)`. -/
def IsHomogBiLimitVF {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (r₀ : Fin n → ℝ) (𝔡₀ : ℝ) (f₀ : (Fin n → ℝ) → (Fin n → ℝ))
    (rinf : Fin n → ℝ) (𝔡inf : ℝ) (finf : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  IsHomogZeroVF f r₀ 𝔡₀ f₀ ∧ IsHomogInftyVF f rinf 𝔡inf finf

end HomogBiLimit.OutputFeedback


