-- Prove2me | Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
-- name    : ProjSelfConcordant_ConicExt_Supplement_Barrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:15:34.603678+00:00
-- url     : https://prove2.me/theorems/0f7f05fd-4534-4c0a-82cd-3f8fdbb6762c
-- title:
--   Definitions 1.1, 1.4, 4.2, eq. (5), pp. 1, 3, 9–11 — regular convex sets, projectively self-concordant barriers, affine metric G, cubic form C, boundary gauges σ, π, negative curvature
-- statement:
--   This file adds the barrier-side vocabulary of §§1, 3, 4 of Hildebrand's paper on top of the published predicates $\mathrm{ProjCond1}$, $\mathrm{ProjCond3}$, the conic extension and the logarithmically homogeneous extension $F(t,x)=\nu(-\log t+f(t^{-1}x))$.
--
--   Let $E$ be a real normed space (in the theorems $E=\mathbb R^n$), $X\subset E$ and $f:E\to\mathbb R$; write $X^o$ for the interior of $X$.
--
--   1. **Regular convex set (Definition 1.1).** $X$ is closed and convex, has nonempty interior, and contains no line: there are no $x$ and $d\neq0$ with $x+td\in X$ for every $t\in\mathbb R$.
--   2. **Projectively self-concordant function and barrier (Definition 1.4).** $f$ is a *projectively self-concordant function* on $X$ with parameter $\gamma\ge0$ if it is $C^3$ on $X^o$ and satisfies there condition (1), $f''(x)-f'(x)f'(x)^T\succ0$, and condition (3) with parameter $\gamma$. It is a *projectively self-concordant barrier* if in addition (condition (2)) $f(x)\to+\infty$ as $x\to y$ within $X^o$, for every boundary point $y$ of $X$.
--   3. **Affine metric and cubic form (Definition 1.4).** For directions $u,v,w$,
--   $$G(x)[u,v]=f''(x)[u,v]-f'(x)[u]\,f'(x)[v],$$
--   $$C(x)[u,v,w]=f'''(x)[u,v,w]-2f''(x)[u,v]f'(x)[w]-2f''(x)[u,w]f'(x)[v]-2f''(x)[v,w]f'(x)[u]+4f'(x)[u]f'(x)[v]f'(x)[w].$$
--   On the diagonal these are the quadratic polynomial $f''[h,h]-(f'[h])^2$ and the cubic polynomial $f'''[h,h,h]-6f''[h,h]f'[h]+4(f'[h])^3$ of condition (3).
--   4. **Boundary gauges (equation (5)).** $\sigma_x(h)=\inf\{t^{-1}\mid t>0,\ x+th\in X\}$ and $\pi_x(h)=\max(\sigma_x(h),\sigma_x(-h))$.
--   5. **Negative curvature (§4 and Definition 4.2).** A function $F$ on a cone $K$ has negative curvature if $F'''(z)[v,v,u]\le0$ for all directions $v$, all $z\in K^o$ and all $u\in K$. The function $f$ has negative curvature (with parameter $\nu$) if $F(t,x)=\nu(-\log t+f(t^{-1}x))$, the $\nu$-logarithmically homogeneous extension of $\nu f$, has negative curvature on the conic extension $K$ of $X$, the closed cone $K=\overline{\{(t,x)\mid t>0,\ t^{-1}x\in X^o\}}$.
--
--   These objects are used by Corollary 4.1 and Theorem 4.3 and by the duality results of §5.
--
--   **Formalization Note** Functions are total; $f$ is read only on the open set $X^o$ and $F$ only on the open cone $K^o$, where Fréchet derivatives depend only on nearby values. Mixed derivatives are `iteratedFDeriv ℝ k f x ![u, v, …]` and $f'(x)[u]$ is `fderiv ℝ f x u`. The infimum defining $\sigma_x(h)$ is a real `sInf`; for $x\in X^o$ the set is nonempty and bounded below by $0$, so it is the genuine infimum (it is $0$ when the ray $x+th$ stays in $X$). The conic extension of the closed set $X$ is taken as the closure of the open cone over $X^o$, which is the closed cone over $X$ together with its recession directions at $t=0$.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, pp. 1, 3, 9, 10, 11, Definition 1.1, Definition 1.4, equation (5), §4 (negative curvature of cone barriers), Definition 4.2

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt.Supplement

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 1.1, p. 1: a regular convex set is closed, convex, has nonempty interior and
contains no (affine) line `{x + t d | t ∈ ℝ}` with `d ≠ 0`. -/
def RegularConvexSet (X : Set E) : Prop :=
  IsClosed X ∧ Convex ℝ X ∧ (interior X).Nonempty ∧
    ∀ x d : E, d ≠ 0 → ¬ ∀ t : ℝ, x + t • d ∈ X

/-- Definition 1.4 without condition (2), p. 3 (as used in Lemma 5.3, p. 13): a projectively
self-concordant function on `X` with parameter `γ ≥ 0` is `C³` on the interior `Xᵒ` and satisfies
conditions (1) and (3) of Definition 1.4 there. -/
def ProjSCFun (γ : ℝ) (X : Set E) (f : E → ℝ) : Prop :=
  0 ≤ γ ∧ ContDiffOn ℝ 3 f (interior X) ∧ ProjCond1 (interior X) f ∧
    ProjCond3 γ (interior X) f

/-- Definition 1.4, p. 3: a projectively self-concordant barrier on `X` with parameter `γ`:
a projectively self-concordant function which tends to `+∞` at every boundary point of `X`,
approached from the interior (condition (2)). -/
def ProjBarrier (γ : ℝ) (X : Set E) (f : E → ℝ) : Prop :=
  ProjSCFun γ X f ∧ ∀ y ∈ frontier X, Tendsto f (𝓝[interior X] y) atTop

/-- Mixed second derivative `f″(x)[u, v]`. -/
noncomputable def d2 (f : E → ℝ) (x u v : E) : ℝ :=
  iteratedFDeriv ℝ 2 f x ![u, v]

/-- Mixed third derivative `f‴(x)[u, v, w]`. -/
noncomputable def d3 (f : E → ℝ) (x u v w : E) : ℝ :=
  iteratedFDeriv ℝ 3 f x ![u, v, w]

/-- The affine metric of Definition 1.4, p. 3, as a bilinear form:
`G(x)[u, v] = f″(x)[u, v] − f′(x)[u] f′(x)[v]`. -/
noncomputable def affMetric (f : E → ℝ) (x u v : E) : ℝ :=
  d2 f x u v - fderiv ℝ f x u * fderiv ℝ f x v

/-- The cubic form of Definition 1.4, p. 3, as a symmetric trilinear form:
`C(x)[u, v, w] = f‴[u,v,w] − 2f″[u,v]f′[w] − 2f″[u,w]f′[v] − 2f″[v,w]f′[u] + 4f′[u]f′[v]f′[w]`. -/
noncomputable def cubicForm (f : E → ℝ) (x u v w : E) : ℝ :=
  d3 f x u v w - 2 * d2 f x u v * fderiv ℝ f x w - 2 * d2 f x u w * fderiv ℝ f x v
    - 2 * d2 f x v w * fderiv ℝ f x u
    + 4 * fderiv ℝ f x u * fderiv ℝ f x v * fderiv ℝ f x w

/-- Equation (5), p. 9: `σₓ(h) = inf {t⁻¹ | t > 0, x + t h ∈ X}`. -/
noncomputable def sigmaGauge (X : Set E) (x h : E) : ℝ :=
  sInf {s : ℝ | ∃ t : ℝ, 0 < t ∧ x + t • h ∈ X ∧ s = t⁻¹}

/-- Equation (5), p. 9: `πₓ(h) = max(σₓ(h), σₓ(−h))`. -/
noncomputable def piGauge (X : Set E) (x h : E) : ℝ :=
  max (sigmaGauge X x h) (sigmaGauge X x (-h))

/-- §4, p. 10: a function `F` on a convex cone `K` has negative curvature if
`F‴(z)[v, v, u] ≤ 0` for all `v`, all `z ∈ Kᵒ` and all `u ∈ K`. -/
def ConeNegCurv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set V) (F : V → ℝ) : Prop :=
  ∀ z ∈ interior K, ∀ u ∈ K, ∀ v : V, iteratedFDeriv ℝ 3 F z ![v, v, u] ≤ 0

/-- Definition 4.2, p. 11: `f` has negative curvature if the `ν`-logarithmically homogeneous
extension `F(t, x) = ν(−log t + f(t⁻¹x))` of `ν·f` has negative curvature on the conic extension
`K` of `X`, the closed cone `K = cl{(t, x) | t > 0, t⁻¹x ∈ Xᵒ}`. -/
def ProjNegCurv (ν : ℝ) (X : Set E) (f : E → ℝ) : Prop :=
  ConeNegCurv (closure (conicExt (interior X))) (homExt ν f)

end ProjSelfConcordant.ConicExt.Supplement


