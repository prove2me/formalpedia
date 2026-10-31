-- Prove2me | Definitions.Def_DecDepSO_Assumption7ab
-- name    : DecDepSO_Assumption7ab
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:53.640994+00:00
-- url     : https://prove2.me/theorems/5100836b-a057-4909-99ee-828841d4d359
-- title:
--   Assumption 7 (a)–(b) — $\varphi=f+r$ with $f$ $\alpha$-strongly convex and $L$-smooth, $r$ closed convex, and its minimizer $\bar x$
-- statement:
--   Let $E$ be a Euclidean space (a real inner product space). Consider the composite problem
--   $$
--   \min_x\ \varphi(x):=f(x)+r(x),
--   $$
--   and let $L,B,\alpha>0$ be constants. The predicate holds when:
--
--   1. $f:E\to\mathbb R$ is $\alpha$-strongly convex and differentiable, and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$;
--   2. $r:E\to\mathbb R\cup\{\infty\}$ is proper, closed and convex; it is given by its domain $D=\operatorname{dom} r$ and its finite values on $D$;
--   3. $\bar x\in D$ is a minimizer of $\varphi$: $\varphi(\bar x)\le\varphi(y)$ for every $y\in D$ (points outside $D$ have $\varphi=+\infty$).
--
--   These are parts (a) and (b) of Assumption 7 and the minimizer $\bar x$ named there. The constant $B$, which bounds the bias of the stochastic gradient oracle in part (c), is recorded here so that $B>0$ is stated once. Part (c) is the definition `IsBiasedProxSGDRun`. The paper sets $\rho:=B/\alpha$ and $\kappa:=L/\alpha$.
--
--   **Formalization Note** $\alpha$-strong convexity is Mathlib's `StrongConvexOn univ α f`, i.e. $f-\frac\alpha2\|\cdot\|^2$ is convex. The extended-valued $r$ is the pair $(D,r)$ with the published predicate `GoldenRatioVI.IsProperConvexLsc D r`: $D$ is nonempty, $r$ is convex on the convex set $D$, and the function equal to $r$ on $D$ and $+\infty$ off $D$ is lower semicontinuous ("closed"). Properness is implicit in the paper, since $\varphi$ has a minimizer. By strong convexity the minimizer is unique.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Assumption 7 (a)–(b), p.25; notation (Euclidean space, prox), p.5

import Mathlib
import Definitions.Def_GoldenRatioVI_IsProperConvexLsc

namespace DecDepSO

/-- **Assumption 7 (a)–(b): the composite problem `min φ = f + r` and its minimizer `x̄`.**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Assumption 7 (Biased stochastic gradient oracle), p.25: "Consider the
optimization problem min_x φ(x) := f(x) + r(x), and denote its minimizer by x̄. We suppose that
there exist constants L, B, α > 0 satisfying the following. (a) The function f : Rd → R is
α-strongly convex and differentiable with L-Lipschitz gradient. (b) The function
r: Rd → R ∪ {∞} is closed and convex."

`Assumption7ab f D r L B α xbar` says: `L, B, α > 0`; `f` is `α`-strongly convex on the whole
space, differentiable, with `L`-Lipschitz gradient; the extended-valued `r` (domain `D`, finite
values `r` on `D`) is proper, convex and closed (lower semicontinuous); and `xbar ∈ D` minimizes
`φ = f + r` over `D` (and hence over the whole space, since `φ = +∞` off `D`).

Part (c) of Assumption 7, the stochastic oracle, is part of `IsBiasedProxSGDRun`.

**Formalization Note.** The paper's `Rd` is "a Euclidean space" (p.5): here any real inner product
space `E` (finite-dimensional in every theorem of this mission). Mathlib's
`StrongConvexOn univ α f` means `f − (α/2)‖·‖²` is convex, i.e. the paper's α-strong convexity.
`r : E → R ∪ {∞}` is the pair `(D, r)` with `GoldenRatioVI.IsProperConvexLsc D r` (`D` nonempty,
`r` convex on the convex set `D`, the `+∞`-extension lower semicontinuous); "closed" is lower
semicontinuity of the extended function, and properness (`D ≠ ∅`) is implicit in the paper since
`φ` has a minimizer. Values of `r` off `D` are irrelevant. The minimizer is unique by strong
convexity, so "its minimizer" is pinned down by `xbar_mem` and `xbar_isMin`. The constant `B`
enters only through part (c); it is kept here so that `B > 0` is stated once, as on the page. -/
structure Assumption7ab {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (D : Set E) (r : E → ℝ) (L B α : ℝ) (xbar : E) : Prop where
  L_pos : 0 < L
  B_pos : 0 < B
  α_pos : 0 < α
  strongConvex : StrongConvexOn Set.univ α f
  differentiable : Differentiable ℝ f
  lipschitz_gradient : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  closed_convex : GoldenRatioVI.IsProperConvexLsc D r
  xbar_mem : xbar ∈ D
  xbar_isMin : ∀ y ∈ D, f xbar + r xbar ≤ f y + r y

end DecDepSO


