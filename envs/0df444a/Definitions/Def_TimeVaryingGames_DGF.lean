-- Prove2me | Definitions.Def_TimeVaryingGames_DGF
-- name    : TimeVaryingGames_DGF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:35.735536+00:00
-- url     : https://prove2.me/theorems/5c464051-7535-469a-b1fb-be7843c4fa1e
-- title:
--   Distance-generating functions, Bregman divergence, prox-mapping, reciprocity condition
-- statement:
--   Let $\mathcal C$ be a compact convex subset of a finite-dimensional real normed space $\mathcal X$ with dual $\mathcal Y$, and let $h$ be a real function on $\mathcal C$ (extended by $+\infty$ off $\mathcal C$).
--
--   1. The **subdifferential** of $h$ at $x$ is $\partial h(x)=\{y\in\mathcal Y: h(x')\ge h(x)+\langle y,x'-x\rangle\ \text{for all }x'\in\mathcal C\}$, and the **prox-domain** is $\mathcal C_h=\{x\in\mathcal C:\partial h(x)\ne\varnothing\}$.
--   2. $h$ is a **distance-generating function (DGF)** on $\mathcal C$ with modulus $K>0$ and selection $\nabla h$ if $h$ is continuous on $\mathcal C$, $K$-strongly convex on $\mathcal C$,
--   $$h(\lambda x+(1-\lambda)x')\le\lambda h(x)+(1-\lambda)h(x')-\tfrac12K\lambda(1-\lambda)\|x'-x\|^2\quad(x,x'\in\mathcal C,\ \lambda\in[0,1]),$$
--   and $\nabla h:\mathcal C_h\to\mathcal Y$ is continuous with $\nabla h(x)\in\partial h(x)$ for all $x\in\mathcal C_h$.
--   3. The **Bregman divergence** is $D(p,x)=h(p)-h(x)-\langle\nabla h(x),p-x\rangle$ for $p\in\mathcal C$, $x\in\mathcal C_h$.
--   4. The **prox-mapping** sends $x\in\mathcal C_h$ and $y\in\mathcal Y$ to
--   $$\mathcal P(x;y)=\operatorname*{arg\,min}_{x'\in\mathcal C}\{\langle y,x-x'\rangle+D(x',x)\}.$$
--   5. The **reciprocity condition** (RC) holds if $D(p,x_t)\to0$ whenever $x_t\to p$, for every $p\in\mathcal C$ and every sequence $x_t\in\mathcal C_h$.
--
--   These are the ingredients of mirror descent in a general norm: the Euclidean projection ($h=\frac12\|x\|^2$) and the entropic (Hedge) update on the simplex, whose prox-domain is the relative interior, are both instances.
--
--   **Formalization Note** $h$ is a real function on the whole space of which only the values on $\mathcal C$ are used; the selection $\nabla h$ is a parameter, because $D$ and $\mathcal P$ depend on it. The prox-mapping is the relation `IsProxPoint` ($x^+\in\mathcal C$ minimizes the objective of item 4). Strong convexity is Mathlib's `StrongConvexOn`, which is exactly the displayed inequality.
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Definition 1 and eqs. (11), (13), footnote 3, p.8; (RC), p.9

import Mathlib

open Filter Topology

namespace TimeVaryingGames

/-- **Subdifferential of `h` at `x`, relative to `C`.**
arXiv:1809.03066v3, footnote 3, p.8: "∂h(x) = {y ∈ Y : h(x') ≥ h(x) + ⟨y, x' − x⟩ for all
x' ∈ X}".

**Formalization Note.** In the paper `h = +∞` off `C`, so the inequality is automatic for
`x' ∉ C`; here `h : E → ℝ` is real-valued and only its values on `C` are used, so the test points
`x'` range over `C`. This is the same set. -/
def subdiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (h : E → ℝ)
    (x : E) : Set (E →L[ℝ] ℝ) :=
  {y | ∀ x' ∈ C, h x + y (x' - x) ≤ h x'}

/-- **Prox-domain** `C_h := dom ∂h`.
arXiv:1809.03066v3, Definition 1, p.8: "we will refer to C_h := dom ∂h as the prox-domain of h";
footnote 3: "dom ∂h := {x ∈ dom h : ∂h(x) ≠ ∅}". Here `dom h = C`. -/
def proxDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (h : E → ℝ) :
    Set E :=
  {x ∈ C | (subdiffOn C h x).Nonempty}

/-- **Distance-generating function** (Definition 1).
arXiv:1809.03066v3, Definition 1, p.8: "Let C be a compact convex subset of X ≅ ℝ^d. A convex
function h : X → ℝ ∪ {∞} is said to be a distance-generating function (DGF) on C if
(1) h is continuous and supported on C, i.e., dom h := {x ∈ X : h(x) < ∞} = C.
(2) h is K-strongly convex relative to ‖·‖ on C, i.e., h(λx + (1 − λ)x') ≤ λh(x) + (1 − λ)h(x')
− ½Kλ(1 − λ)‖x' − x‖² (12) for all x, x' ∈ C and all λ ∈ [0, 1].
(3) The subdifferential ∂h of h admits a continuous selection, i.e., there exists a continuous
mapping ∇h : dom ∂h → Y such that ∇h(x) ∈ ∂h(x) for all x ∈ dom ∂h."

`IsDGF C Kc h gradh` says that `h` is a DGF on `C` with strong-convexity modulus `Kc` and that
`gradh` is a continuous selection of its subdifferential on the prox-domain.

**Formalization Note.**
* `h : E → ℝ` is real-valued; only its values on `C` matter (the paper's `h` is `+∞` off `C`).
  Continuity is continuity on `C`.
* Mathlib's `StrongConvexOn C Kc h` is exactly (12) (it also contains convexity of `C`).
* The strong-convexity modulus is positive (`0 < Kc`), as the paper's divisions by `K` require.
* The selection `∇h` is part of the data (`gradh`), because the Bregman divergence and the
  prox-mapping depend on it; its values off the prox-domain are irrelevant.
* The pairing `⟨y, x⟩` is evaluation of `y : E →L[ℝ] ℝ`; no inner product is assumed. -/
structure IsDGF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (Kc : ℝ)
    (h : E → ℝ) (gradh : E → E →L[ℝ] ℝ) : Prop where
  /-- `C` is compact. -/
  isCompact : IsCompact C
  /-- The strong-convexity modulus is positive. -/
  modulus_pos : 0 < Kc
  /-- `h` is continuous on `C`. -/
  continuousOn : ContinuousOn h C
  /-- (12): `h` is `Kc`-strongly convex on `C` (this includes convexity of `C`). -/
  strongConvexOn : StrongConvexOn C Kc h
  /-- The selection is continuous on the prox-domain. -/
  continuousOn_gradh : ContinuousOn gradh (proxDomain C h)
  /-- The selection is a subgradient at every point of the prox-domain. -/
  gradh_mem : ∀ x ∈ proxDomain C h, gradh x ∈ subdiffOn C h x

/-- **Bregman divergence** `D(p, x) = h(p) − h(x) − ⟨∇h(x), p − x⟩`.
arXiv:1809.03066v3, eq. (11), p.8: "D(x', x) = h(x') − h(x) − ⟨∇h(x), x' − x⟩". It is used for
`p ∈ C` and `x` in the prox-domain. -/
def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (gradh : E → E →L[ℝ] ℝ) (p x : E) : ℝ :=
  h p - h x - gradh x (p - x)

/-- **Prox-mapping**, as a relation: `xp = P(x; y)`.
arXiv:1809.03066v3, eq. (13), p.8: "P(x; y) = arg min_{x'∈C} {⟨y, x − x'⟩ + D(x', x)} for all
x ∈ C_h, y ∈ Y."

**Formalization Note.** `IsProxPoint C h gradh x y xp` says that `xp ∈ C` minimizes
`x' ↦ ⟨y, x − x'⟩ + D(x', x)` over `C`. The minimizer exists and is unique for a DGF; the relation
form avoids a choice function. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (h : E → ℝ)
    (gradh : E → E →L[ℝ] ℝ) (x : E) (y : E →L[ℝ] ℝ) (xp : E) : Prop :=
  xp ∈ C ∧ ∀ x' ∈ C, y (x - xp) + bregman h gradh xp x ≤ y (x - x') + bregman h gradh x' x

/-- **Reciprocity condition** (RC).
arXiv:1809.03066v3, §4.1, p.9: "D(p, x_t) → 0 whenever x_t → p (RC) for every sequence of actions
x_t ∈ K_h."

Here `p` ranges over `C` (the first argument of `D` lives in `C`) and the sequence over the
prox-domain. -/
def ReciprocityCondition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (h : E → ℝ) (gradh : E → E →L[ℝ] ℝ) : Prop :=
  ∀ p ∈ C, ∀ x : ℕ → E, (∀ t, x t ∈ proxDomain C h) → Tendsto x atTop (𝓝 p) →
    Tendsto (fun t => bregman h gradh p (x t)) atTop (𝓝 0)

end TimeVaryingGames


