-- Prove2me | Definitions.Def_TalagrandConc_ConvexHull_Basic
-- name    : TalagrandConc_ConvexHull_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:07.004986+00:00
-- url     : https://prove2.me/theorems/0ffa1114-540f-4cf3-b943-a2258c7ee155
-- title:
--   $U_A(x)$, $V_A(x)$, $f_c(A,x)$, $A_t^c$, $\xi(\alpha,u)$ and $f_\alpha(A,x)$ of Sections 4.1–4.2
-- statement:
--   Let $\Omega$ be a set, $N\ge 0$ an integer, $A\subseteq\Omega^N$ and $x\in\Omega^N$.
--
--   1. The set $U_A(x)\subseteq\{0,1\}^N\subseteq\mathbb R^N$ consists of the $0$–$1$ vectors $s$ for which some $y\in A$ satisfies $x_i=y_i$ whenever $s_i=0$:
--   $$U_A(x)=\{(s_i)_{i\le N}\in\{0,1\}^N;\ \exists y\in A,\ s_i=0\Rightarrow x_i=y_i\}.$$
--   2. $V_A(x)$ is the convex hull of $U_A(x)$ in $\mathbb R^N$. It contains $0$ exactly when $x\in A$.
--   3. The **convex hull distance** $f_c(A,x)$ is the Euclidean ($\ell^2$) distance from $0$ to $V_A(x)$:
--   $$f_c(A,x)=\inf\Big\{\Big(\sum_{i\le N}s_i^2\Big)^{1/2};\ s\in V_A(x)\Big\}.$$
--   4. For a real $t$, the **enlargement** of $A$ is $A_t^c=\{x\in\Omega^N;\ f_c(A,x)\le t\}$ (the superscript $c$ stands for "convexity", not for a complement).
--   5. For $\alpha\ge0$ and $u\in[0,1]$,
--   $$\xi(\alpha,u)=\alpha(1-u)\log(1-u)-(\alpha+1-\alpha u)\log\Big(\frac{1+\alpha-\alpha u}{1+\alpha}\Big),$$
--   with $(1-u)\log(1-u)=0$ at $u=1$, so that $\xi(\alpha,1)=\log(1+\alpha)$.
--   6. $f_\alpha(A,x)=\inf\{\sum_{i\le N}\xi(\alpha,s_i);\ s\in V_A(x)\}$, a "distance" from $x$ to $A$ that plays the role of $f_c^2(A,x)$.
--
--   These objects carry the whole of Chapter 4 of the paper and are the substrate of its Part II applications: Theorem 4.1.1 bounds $\int\exp\frac14 f_c^2(A,x)\,dP(x)$ and Theorem 4.2.4 bounds $\int\exp f_\alpha(A,x)\,dP(x)$ under a product probability $P$.
--
--   **Formalization Note** $\Omega^N$ is `Fin N → Ω`; $U_A(x)$ is a set of functions `Fin N → ℝ` with values in $\{0,1\}$ and $V_A(x)$ is Mathlib's `convexHull ℝ`. The Euclidean norm is written out (Mathlib's norm on `Fin N → ℝ` is the sup norm). $f_c$ and $f_\alpha$ take values in $[0,\infty]$; both are $+\infty$ when $A=\varnothing$ (empty infimum). $f_\alpha$ wraps each sum in `ENNReal.ofReal`, which loses nothing for $\alpha\ge0$ since $\xi(\alpha,\cdot)\ge0$ on $[0,1]$. Membership in $A_t^c$ compares $f_c(A,x)$ with $t$ in the extended reals, so $A_t^c=\varnothing$ for $t<0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 123, Section 4.1, Eq. (4.1.1); p. 126, Section 4.2, Eq. (4.2.1)

import Mathlib

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 123, §4.1: for `A ⊆ Ω^N` and `x ∈ Ω^N`,
`U_A(x) = { (s_i)_{i ≤ N} ∈ {0,1}^N ; ∃ y ∈ A, s_i = 0 ⇒ x_i = y_i }`,
seen as a subset of `ℝ^N`. -/
def U {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧ ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

/-- Talagrand (1995), p. 123, §4.1: `V_A(x)` is the convex hull of `U_A(x)` in `ℝ^N`. -/
def V {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  convexHull ℝ (U A x)

/-- Talagrand (1995), p. 123, §4.1: `f_c(A, x)` is the `ℓ²` (Euclidean) distance from `0` to
`V_A(x)`, i.e. `inf { (Σ_i s_i²)^{1/2} ; s ∈ V_A(x) }`. The Euclidean norm is written out
(Mathlib's norm on `Fin N → ℝ` is the sup norm). Values in `ℝ≥0∞`: for `A = ∅`,
`V_A(x) = ∅` and `f_c(A, x) = ⊤ = +∞`. -/
noncomputable def fc {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ s ∈ V A x, ENNReal.ofReal (Real.sqrt (∑ i, s i ^ 2))

/-- Talagrand (1995), Eq. (4.1.1), p. 123: the enlargement
`A_t^c = { x ∈ Ω^N ; f_c(A, x) ≤ t }` (the superscript `c` refers to "convexity"; this is not
a complement). The comparison is made in `EReal`, so `A_t^c = ∅` for `t < 0` and points with
`f_c(A, x) = +∞` never belong to it. -/
def enlarge {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (t : ℝ) : Set (Fin N → Ω) :=
  {x | ((fc A x : ℝ≥0∞) : EReal) ≤ (t : EReal)}

/-- Talagrand (1995), Eq. (4.2.1), p. 126:
`ξ(α, u) = α (1 − u) log(1 − u) − (α + 1 − α u) log((1 + α − α u)/(1 + α))`.
At `u = 1` the term `(1 − u) log(1 − u)` is `0` (Mathlib's `Real.log 0 = 0`), so
`ξ(α, 1) = log(1 + α)`. Intended for `α ≥ 0` and `u ∈ [0, 1]`. -/
noncomputable def xi (α u : ℝ) : ℝ :=
  α * (1 - u) * Real.log (1 - u) - (α + 1 - α * u) * Real.log ((1 + α - α * u) / (1 + α))

/-- Talagrand (1995), p. 126, §4.2:
`f_α(A, x) = inf { Σ_{i ≤ N} ξ(α, s_i) ; s ∈ V_A(x) }`.
Values in `ℝ≥0∞` (for `α ≥ 0`, `ξ(α, ·) ≥ 0` on `[0, 1] ⊇` the coordinates of `V_A(x)`, so
`ENNReal.ofReal` loses nothing); for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def fAlpha {Ω : Type*} {N : ℕ} (α : ℝ) (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ s ∈ V A x, ENNReal.ofReal (∑ i, xi α (s i))

end TalagrandConc.ConvexHull


