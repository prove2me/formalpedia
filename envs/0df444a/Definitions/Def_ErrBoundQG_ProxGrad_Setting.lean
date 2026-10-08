-- Prove2me | Definitions.Def_ErrBoundQG_ProxGrad_Setting
-- name    : ErrBoundQG_ProxGrad_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:27.454397+00:00
-- url     : https://prove2.me/theorems/5ae5217f-94c7-4183-9248-a8fcf8d75030
-- title:
--   §2–§3, pp. 3–9 — the composite problem (3.1), minimizers, sublevel sets, the prox-gradient step, quadratic growth (3.12), the error bound (3.13), and the error bounds (3.7)–(3.9)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean norm, and let $\overline{\mathbb R} = \mathbb R\cup\{\pm\infty\}$. This file fixes the objects of §§2–3 of Drusvyatskiy–Lewis.
--
--   1. **Minimizers and sublevel sets.** For $\varphi:\mathbb R^n\to\overline{\mathbb R}$, the set of minimizers is $S = \{x : \varphi(x)\le\varphi(y)\ \text{for all } y\}$, and for a real $r$ the sublevel set is $[\varphi\le r] = \{x : \varphi(x)\le r\}$.
--   2. **The composite objective** (3.1): for $f:\mathbb R^n\to\mathbb R$ and $g:\mathbb R^n\to\overline{\mathbb R}$, $\varphi := f + g$.
--   3. **The proximal gradient step.** For $t>0$, a point $p$ is a proximal gradient step from $x$ when
--   $$p = \operatorname{prox}_{tg}\big(x - t\nabla f(x)\big),\qquad \operatorname{prox}_{tg}(z) = \operatorname*{argmin}_y \Big\{ g(y) + \tfrac{1}{2t}\|y - z\|^2\Big\},$$
--   and the prox-gradient mapping is $\mathcal G_t(x) = t^{-1}(x - p)$.
--   4. **Quadratic growth** (3.12), and (3.6) for a general $h$: with minimizer set $S$ and minimal value $\varphi^*$, for all $x\in[\varphi\le\varphi^*+\nu]$,
--   $$\varphi(x)\ \ge\ \varphi^* + \frac{\alpha}{2}\,\operatorname{dist}^2(x;S).$$
--   5. **The error bound condition** (Definition 3.1, (3.13)) with parameters $(\gamma,\nu)$: $\operatorname{dist}(x;S)\le\gamma\,\|\mathcal G_t(x)\|$ for all $x\in[\varphi\le\varphi^*+\nu]$.
--   6. **The subdifferential error bound** (3.7)/(3.8): $\operatorname{dist}(x;S)\le L\cdot\operatorname{dist}(0;\partial h(x))$ for all $x\in[h\le h^*+\nu]$, where $\partial h$ is the convex subdifferential.
--   7. **The proximal error bound** (3.9): $\operatorname{dist}(x;S)\le \widehat L\cdot t^{-1}\|x - \operatorname{prox}_{th}(x)\|$ for all $x\in[h\le h^*+\nu]$.
--
--   These conditions are the vocabulary of the paper's main equivalence (Corollary 3.6): quadratic growth of $\varphi$ holds if and only if the error bound condition for the proximal gradient method does, with explicit constants.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\overline{\mathbb R}$-valued functions are `EReal`-valued, and $\operatorname{dist}(x;S)$ is `Metric.infDist x S` (every theorem assumes $S\neq\emptyset$). The proximal point is the predicate `GoldenRatioVI.Shared.IsProxPoint (fun y => t * g y) z p`, which says that $p$ minimizes $t\,g(y)+\tfrac12\|y-z\|^2$; for $t>0$ this is the same argmin as $g(y)+\tfrac1{2t}\|y-z\|^2$ (and $t\cdot(+\infty)=+\infty$). The conditions quantify over every such $p$, which is faithful because the minimizer exists and is unique for proper closed convex $g$ and $t>0$. The conditions involving $\operatorname{dist}(0;\partial h(x))$ are written as "$\operatorname{dist}(x;S)\le L\|v\|$ for every $v\in\partial h(x)$", which keeps the convention $\operatorname{dist}(0;\emptyset)=+\infty$ (the condition holds trivially where $\partial h(x)=\emptyset$). The subdifferential is the published `ProxAlg.FixedPoint.subdifferential`.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 3–9, §2, (3.1), Definition 3.1, (3.6)–(3.9), (3.12), (3.13)

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace ErrBoundQG.ProxGrad

/-- The set `S` of minimizers of `φ : ℝⁿ → R̄` (§3, p. 5). -/
def minSet {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ y, φ x ≤ φ y}

/-- The sublevel set `[φ ≤ r] := {x : φ(x) ≤ r}` (§2, p. 3). -/
def sublevel {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | φ x ≤ (r : EReal)}

/-- The composite objective `φ := f + g` of (3.1), with `f` real valued and `g` extended
real valued (p. 4). -/
noncomputable def compositeObj {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal) : EuclideanSpace ℝ (Fin n) → EReal :=
  fun x => ((f x : ℝ) : EReal) + g x

/-- `p = prox_{tg}(x - t∇f(x))`, the proximal gradient step from `x` (p. 4). The argmin of
`t·g(y) + ½‖y - z‖²` is that of `g(y) + ‖y - z‖²/(2t)` for `t > 0`. The prox-gradient
mapping is then `𝒢_t(x) = t⁻¹(x - p)`. -/
def IsProxGradStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal) (t : ℝ) (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  GoldenRatioVI.Shared.IsProxPoint (fun y => ((t : ℝ) : EReal) * g y) (x - t • gradient f x) p

/-- Quadratic growth (3.12) (and (3.6) for a general `h`): `φ(x) ≥ φ* + (α/2)·dist²(x; S)`
for all `x ∈ [φ ≤ φ* + ν]`. -/
def QuadGrowth {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (φstar α ν : ℝ) : Prop :=
  ∀ x ∈ sublevel φ (φstar + ν),
    (((φstar + α / 2 * Metric.infDist x S ^ 2 : ℝ)) : EReal) ≤ φ x

/-- The error bound condition (Definition 3.1, (3.13)) with parameters `(γ, ν)`:
`dist(x, S) ≤ γ‖𝒢_t(x)‖` for all `x ∈ [φ ≤ φ* + ν]`, with `𝒢_t(x) = t⁻¹(x - p)` and
`p = prox_{tg}(x - t∇f(x))`. -/
def ErrorBound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (t : ℝ) (S : Set (EuclideanSpace ℝ (Fin n))) (φstar γ ν : ℝ) : Prop :=
  ∀ x ∈ sublevel (compositeObj f g) (φstar + ν), ∀ p, IsProxGradStep f g t x p →
    Metric.infDist x S ≤ γ * ‖t⁻¹ • (x - p)‖

/-- The subdifferential error bound (3.7)/(3.8): `dist(x; S) ≤ L·dist(0; ∂h(x))` for all
`x ∈ [h ≤ h* + ν]`, written as `dist(x; S) ≤ L‖v‖` for every `v ∈ ∂h(x)` (the distance to
the empty set is `+∞`). -/
def SubdiffErrorBound {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hstar L ν : ℝ) : Prop :=
  ∀ x ∈ sublevel h (hstar + ν), ∀ v ∈ ProxAlg.FixedPoint.subdifferential h x,
    Metric.infDist x S ≤ L * ‖v‖

/-- The proximal error bound (3.9): `dist(x; S) ≤ L̂·t⁻¹‖x - prox_{th}(x)‖` for all
`x ∈ [h ≤ h* + ν]`. -/
def ProxErrorBound {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hstar Lhat t ν : ℝ) : Prop :=
  ∀ x ∈ sublevel h (hstar + ν), ∀ p,
    GoldenRatioVI.Shared.IsProxPoint (fun y => ((t : ℝ) : EReal) * h y) x p →
    Metric.infDist x S ≤ Lhat * (t⁻¹ * ‖x - p‖)

end ErrBoundQG.ProxGrad


