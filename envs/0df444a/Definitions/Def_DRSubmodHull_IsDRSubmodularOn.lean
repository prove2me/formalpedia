-- Prove2me | Definitions.Def_DRSubmodHull_IsDRSubmodularOn
-- name    : DRSubmodHull_IsDRSubmodularOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:39.146319+00:00
-- url     : https://prove2.me/theorems/dd822742-74c8-4fcd-b992-f2eee5fed441
-- title:
--   DR-submodularity on a set (Definition 1.1) and concavity along each coordinate
-- statement:
--   Let $V$ be a finite index set and $e^i\in\mathbb R^V$ the $i$-th unit vector. A function $f:\mathbb R^V\to\mathbb R$ is **DR-submodular on** $X\subseteq\mathbb R^V$ if
--
--   $$
--   f(x+\alpha e^i)-f(x)\;\ge\; f(y+\alpha e^i)-f(y)
--   $$
--
--   for every coordinate $i$, all $x,y\in X$ with $x\le y$ componentwise, and every $\alpha\ge 0$ with $x+\alpha e^i,\ y+\alpha e^i\in X$. This is Definition 1.1 of the paper: increments along a coordinate shrink as the base point grows (diminishing returns).
--
--   The module also defines **concavity along each coordinate on $X$**: for every $z\in X$ and every coordinate $i$, the one-variable function $s\mapsto f(z_{-i},s)$ (replace the $i$-th coordinate of $z$ by $s$) is concave on the section $\{s : (z_{-i},s)\in X\}$. This is the property that the proof of the paper's Lemma 3.2 claims to derive from DR-submodularity; it is the correction hypothesis of this mission (continuous DR-submodular functions on a box have it).
--
--   **Formalization Note** $\alpha e^i$ is `Pi.single i α`; the values of $f$ outside $X$ play no role. `ConcaveOn` also asks that the section be convex, which holds on a box.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Definition 1.1, p.1; coordinate concavity from the proof of Lemma 3.2, p.33

import Mathlib

set_option autoImplicit false

namespace DRSubmodHull

/-- **DR-submodularity on a set** (Yu, Küçükyavuz, *On Constrained Mixed-Integer DR-Submodular
Minimization*, arXiv:2211.07726v2, Definition 1.1, p.1).

A function `f : (V → ℝ) → ℝ` is DR-submodular on `X ⊆ ℝ^V` if
`f (x + α eⁱ) - f x ≥ f (y + α eⁱ) - f y` for every coordinate `i`, all `x, y ∈ X` with `x ≤ y`
component-wise, and all `α ≥ 0` such that `x + α eⁱ, y + α eⁱ ∈ X`.

**Formalization Note.** The coordinates are indexed by an arbitrary finite type `V` (the paper's
`{1, …, n}`); `α eⁱ` is `Pi.single i α`. The values of `f` off `X` are irrelevant. -/
def IsDRSubmodularOn {V : Type*} [DecidableEq V] (X : Set (V → ℝ)) (f : (V → ℝ) → ℝ) : Prop :=
  ∀ i : V, ∀ x ∈ X, ∀ y ∈ X, x ≤ y → ∀ α : ℝ, 0 ≤ α →
    x + Pi.single i α ∈ X → y + Pi.single i α ∈ X →
      f (y + Pi.single i α) - f y ≤ f (x + Pi.single i α) - f x

/-- **Concavity along each coordinate on a set** (the correction hypothesis of this mission; it is
what the proof of Lemma 3.2, arXiv:2211.07726v2, p.33, claims to derive: "f is concave in `𝒳_i`").

For every `z ∈ X` and every coordinate `i`, the one-variable function `s ↦ f (z with zᵢ := s)` is
concave on the section `{s | (z with zᵢ := s) ∈ X}`.

**Formalization Note.** `ConcaveOn` also requires the section to be convex; for a box
`X = Set.Icc a b` the section through a point of `X` is the interval `[aᵢ, bᵢ]`. -/
def IsCoordConcaveOn {V : Type*} [DecidableEq V] (X : Set (V → ℝ)) (f : (V → ℝ) → ℝ) : Prop :=
  ∀ z ∈ X, ∀ i : V,
    ConcaveOn ℝ {s : ℝ | Function.update z i s ∈ X} (fun s => f (Function.update z i s))

end DRSubmodHull


