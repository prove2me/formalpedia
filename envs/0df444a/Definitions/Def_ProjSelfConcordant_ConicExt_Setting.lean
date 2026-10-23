-- Prove2me | Definitions.Def_ProjSelfConcordant_ConicExt_Setting
-- name    : ProjSelfConcordant_ConicExt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:20.079107+00:00
-- url     : https://prove2.me/theorems/eac93140-6cd3-4057-aad7-9bbe07ee96a7
-- title:
--   Definitions 1.1 and 1.4, Theorem 1.5, pp. 1, 3 — affine and projective self-concordance conditions (1), (3), the conic extension K and F(t, x) = ν(−log t + f(t⁻¹x))
-- statement:
--   This file fixes the vocabulary of Hildebrand's characterization of projective self-concordance.
--
--   Let $E$ be a real normed space (in the mission, $E=\mathbb R^n$) and $g:E\to\mathbb R$. For $k\in\{1,2,3\}$ write
--   $$g^{(k)}(x)[h,\dots,h] = D^k g(x)[h,\dots,h]$$
--   for the $k$-th Fréchet derivative of $g$ at $x$, evaluated on the diagonal $(h,\dots,h)$; in the notation of the paper these are $g'(x)[h]$, $g''(x)[h,h]$ and $g'''(x)[h,h,h]$.
--
--   1. **Projective conditions (Definition 1.4).** A function $f$ satisfies *condition (1)* on a set $D$ if the affine metric $G(x)[h,h] = f''(x)[h,h]-(f'(x)[h])^2$ is positive definite, i.e. $f''(x)[h,h]-(f'(x)[h])^2>0$ for all $x\in D$ and all $h\neq 0$. It satisfies *condition (3) with parameter $\gamma$* if
--   $$\bigl|f'''(x)[h,h,h]-6f''(x)[h,h]f'(x)[h]+4(f'(x)[h])^3\bigr| \le 2\gamma\bigl(f''(x)[h,h]-(f'(x)[h])^2\bigr)^{3/2}$$
--   for all $x\in D$ and all $h$.
--   2. **Affine conditions (Definition 1.1).** A function $F$ satisfies *condition (1)* on a set $K$ if $F''(x)[h,h]>0$ for all $x\in K$, $h\ne0$, and *condition (3)* if $|F'''(x)[h,h,h]|\le 2(F''(x)[h,h])^{3/2}$ for all $x\in K$ and all $h$.
--   3. **Conic extension.** For $D\subset E$, $K=\{(t,x)\in\mathbb R\times E \mid t>0,\ t^{-1}x\in D\}$.
--   4. **Logarithmically homogeneous extension.** For $\nu\in\mathbb R$ and $f$, $F(t,x)=\nu\bigl(-\log t+f(t^{-1}x)\bigr)$.
--   5. **The sextic.** $p_\mu(t)=4(\nu-1)t^6+12(\nu-2)t^4+4\mu t^3+12(\nu-3)t^2+12\mu t+4\nu-\mu^2$ (Section 2, p. 5).
--
--   Only conditions (1) and (3) of the two definitions enter Theorem 1.5; the barrier condition (2) and the parameter condition (4) are not part of these predicates.
--
--   **Formalization Note** The functions $f:E\to\mathbb R$ and $F:\mathbb R\times E\to\mathbb R$ are total; the paper's $f:D\to\mathbb R$ and $F:K\to\mathbb R$ are read only at points of the open sets $D$ and $K$, where the Fréchet derivatives depend only on values near the point. Derivatives are `iteratedFDeriv ℝ k g x (fun _ => h)`. $\mathbb R^{n+1}$ is `ℝ × EuclideanSpace ℝ (Fin n)` with first coordinate $t$; its product norm differs from the Euclidean one, which does not affect derivatives. The power $3/2$ is `Real.rpow`, which returns $0$ on negative bases; the theorems using condition (3) always pair it with condition (1), under which the bases are nonnegative. Openness, convexity and $C^3$ regularity are hypotheses of the theorems, not part of these predicates. The related published predicate `ConvexOptimization.IsSelfConcordantOn` bundles convexity and $C^3$ and has no strict positivity, so it is not condition (1)+(3) of Definition 1.1 and is not reused.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, pp. 1, 3, 5, Definition 1.1 (1), (3), Definition 1.4 (1), (3), Theorem 1.5, §2 (the polynomial p_µ)

import Mathlib

namespace ProjSelfConcordant.ConicExt

/-- `D^k g(x)[h, …, h]`, the `k`-th derivative of `g` at `x` evaluated on the diagonal `(h, …, h)`. -/
noncomputable def dk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (g : E → ℝ) (x h : E) : ℝ :=
  iteratedFDeriv ℝ k g x (fun _ => h)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 1.4 (1), p. 3: `f″(x) − f′(x)f′(x)ᵀ ≻ 0` for all `x ∈ D`. -/
def ProjCond1 (D : Set E) (f : E → ℝ) : Prop :=
  ∀ x ∈ D, ∀ h : E, h ≠ 0 → 0 < dk 2 f x h - (dk 1 f x h) ^ 2

/-- Definition 1.4 (3), p. 3, with parameter `γ`:
`|f‴(x)[h,h,h] − 6f″(x)[h,h]f′(x)[h] + 4(f′(x)[h])³| ≤ 2γ(f″(x)[h,h] − (f′(x)[h])²)^{3/2}`. -/
def ProjCond3 (γ : ℝ) (D : Set E) (f : E → ℝ) : Prop :=
  ∀ x ∈ D, ∀ h : E,
    |dk 3 f x h - 6 * dk 2 f x h * dk 1 f x h + 4 * (dk 1 f x h) ^ 3|
      ≤ 2 * γ * (dk 2 f x h - (dk 1 f x h) ^ 2) ^ (3 / 2 : ℝ)

/-- Definition 1.1 (1), p. 1: `F″(x) ≻ 0` for all `x ∈ K`. -/
def AffCond1 (K : Set E) (F : E → ℝ) : Prop :=
  ∀ x ∈ K, ∀ h : E, h ≠ 0 → 0 < dk 2 F x h

/-- Definition 1.1 (3), p. 1: `|F‴(x)[h,h,h]| ≤ 2(F″(x)[h,h])^{3/2}` for all `x ∈ K` and all `h`. -/
def AffCond3 (K : Set E) (F : E → ℝ) : Prop :=
  ∀ x ∈ K, ∀ h : E, |dk 3 F x h| ≤ 2 * (dk 2 F x h) ^ (3 / 2 : ℝ)

/-- Theorem 1.5, p. 3: the conic extension `K = {(t, x) | t > 0, t⁻¹x ∈ D}`. -/
def conicExt (D : Set E) : Set (ℝ × E) := {q | 0 < q.1 ∧ q.1⁻¹ • q.2 ∈ D}

/-- Theorem 1.5, p. 3: `F(t, x) = ν(−log t + f(t⁻¹x))`. -/
noncomputable def homExt (ν : ℝ) (f : E → ℝ) : ℝ × E → ℝ :=
  fun q => ν * (-Real.log q.1 + f (q.1⁻¹ • q.2))

/-- §2, p. 5: `p_μ(t) = 4(ν − 1)t⁶ + 12(ν − 2)t⁴ + 4μt³ + 12(ν − 3)t² + 12μt + 4ν − μ²`. -/
def pmu (ν μ t : ℝ) : ℝ :=
  4 * (ν - 1) * t ^ 6 + 12 * (ν - 2) * t ^ 4 + 4 * μ * t ^ 3 + 12 * (ν - 3) * t ^ 2
    + 12 * μ * t + 4 * ν - μ ^ 2

end ProjSelfConcordant.ConicExt


