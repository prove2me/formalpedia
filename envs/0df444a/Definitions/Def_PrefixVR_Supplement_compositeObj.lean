-- Prove2me | Definitions.Def_PrefixVR_Supplement_compositeObj
-- name    : PrefixVR_Supplement_compositeObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:49:22.282234+00:00
-- url     : https://prove2.me/theorems/40fef3c4-9d06-441b-8522-ae94b8c73a8a
-- title:
--   Composite objective $F=f+g$, its infimum $F_*$ and $\partial F=\nabla f+\partial g$
-- statement:
--   Let $f=\frac1n\sum_{i=1}^n f_i:\mathbb R^d\to\mathbb R$ and $g:\mathbb R^d\to\mathbb R\cup\{+\infty\}$. The **composite objective** of problem (16) is
--   $$
--   F(x):=f(x)+g(x),
--   $$
--   its optimal value is $F_*:=\inf_x F(x)$, and its subdifferential is
--   $$
--   \partial F(x):=\nabla f(x)+\partial g(x)=\{\nabla f(x)+s:\ s\in\partial g(x)\},
--   $$
--   where $\partial g(x)=\{s:\ g(x)<+\infty,\ g(y)\ge g(x)+\langle s,y-x\rangle\ \forall y\}$ is the convex subdifferential. These are the objects in which the stationarity guarantee (21) of the proximal method is stated.
--
--   **Formalization Note** $g$ is `EReal`-valued and $f(x)$ enters by coercion; $F_*$ is an `EReal` infimum, so $F_*>-\infty$ reads `compositeStar fi g ≠ ⊥`. $\partial g$ is the published `DCAExtrap.convexSubdiff`, and $\nabla f$ is Mathlib's `gradient` of the published `KatyushaNs.favg fi`. $\partial F(x)$ is empty off $\operatorname{dom} g$.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §6, Eq. (16) and the definition of ∂F, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_DCAExtrap_convexSubdiff

namespace PrefixVR.Supplement

/-- **The composite objective** `F(x) := f(x) + g(x)` of problem (16).
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), §6, Eq. (16), p.9:
"min_{x ∈ ℝᵈ} F(x) := f(x) + g(x), where function g : ℝᵈ → ℝ ∪ {+∞} is proper, closed, convex".

`compositeObj fi g x = f(x) + g(x)` with `f = (1/n) ∑ᵢ fᵢ` (the published `KatyushaNs.favg`).

**Formalization Note.** `g` is `EReal`-valued (so `g = +∞` off `dom g`) and `f(x)` enters by
coercion; for proper `g` (never `−∞`) the sum is the paper's extended-real sum. -/
noncomputable def compositeObj {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EReal) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  (KatyushaNs.favg fi x : EReal) + g x

/-- **The optimal value** `F_* := inf_x F(x)` (§6, p.9), in `EReal` (so `F_* > −∞` is
`compositeStar fi g ≠ ⊥`). -/
noncomputable def compositeStar {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EReal) : EReal :=
  ⨅ x, compositeObj fi g x

/-- **The subdifferential of `F`**, `∂F(x) := ∇f(x) + ∂g(x)` (§6, p.9: "∂F(x) := ∇f(x) + ∂g(x).
Here ∂g is the convex subdifferential").

`subdiffF fi g x = {∇f(x) + s | s ∈ ∂g(x)}`, with `∂g` the convex subdifferential (the published
`DCAExtrap.convexSubdiff`: `s ∈ ∂g(x)` iff `g x ≠ +∞` and `g(y) ≥ g(x) + ⟨s, y − x⟩` for all `y`)
and `∇f` Mathlib's `gradient` of `f = (1/n) ∑ᵢ fᵢ`.

**Formalization Note.** This is the paper's definition, a translate of the convex
subdifferential of `g`; it is empty off `dom g`. -/
noncomputable def subdiffF {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EReal) (x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {w | ∃ s ∈ DCAExtrap.convexSubdiff g x, w = gradient (KatyushaNs.favg fi) x + s}

end PrefixVR.Supplement


