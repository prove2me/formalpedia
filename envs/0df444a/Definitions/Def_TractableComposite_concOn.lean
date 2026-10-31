-- Prove2me | Definitions.Def_TractableComposite_concOn
-- name    : TractableComposite_concOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:46.097562+00:00
-- url     : https://prove2.me/theorems/cac2c57f-5183-4338-8175-ba38fd2a47ad
-- title:
--   The concave envelope $\operatorname{conc}_{\operatorname{conv}X}(g|_X)$
-- statement:
--   For a set $X$ in a real vector space, a function $g$ and a point $x$,
--
--   $$\operatorname{concOn}(X,g)(x)=\sup\Big\{\sum_{k}w_k\,g(p_k)\ \Big|\ p_k\in X,\ w_k\ge0,\ \sum_k w_k=1,\ \sum_k w_kp_k=x\Big\},$$
--
--   the supremum over finite convex combinations. With $X=D$ this is the concave envelope $\operatorname{conc}_D(g)$; with $X\subseteq D$ it is the concave envelope of the restriction $g|_X$ ($g$ on $X$, $-\infty$ elsewhere) of Definition 1.
--
--   **Formalization Note.** Lean's supremum of an empty or unbounded set is $0$, so the value is meaningful only at points of $\operatorname{conv}X$ at which $g$ is bounded above on $X$. Every statement of the mission evaluates it at points of its domain, where the set is nonempty; for a continuous $g$ on a polytope it is bounded.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Notation, p.3, and Definition 1, p.6

import Mathlib

namespace TractableComposite

/-- **The concave envelope `conc_{conv X}(g|_X)`.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Notation, p.3 (`conc_S(f)`), and
Definition 1, p.6 (`g|_X = g` on `X`, `−∞` otherwise).

`concOn X g x` is the supremum of `∑ₖ wₖ g(pₖ)` over all finite convex combinations `∑ₖ wₖ pₖ = x`
of points `pₖ ∈ X`. With `X = D` this is the concave envelope `conc_D(g)` of `g` over `D`; with
`X ⊆ D` it is the concave envelope of the restriction `g|_X` (the value `−∞` off `X` never helps a
supremum).

**Formalization Note.** The envelope is the supremum over finite convex combinations (the concave
envelope of a function on a convex set). Lean's `sSup` returns `0` on an empty or unbounded-above
set, so `concOn X g x` is meaningful only at points `x ∈ conv X` where `g` is bounded above on `X`:
every use in this mission evaluates it at points of the domain (`x ∈ D = conv X`), where the set is
nonempty, and for a continuous `g` on a polytope it is bounded. -/
noncomputable def concOn {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E) (g : E → ℝ)
    (x : E) : ℝ :=
  sSup {y : ℝ | ∃ (m : ℕ) (w : Fin m → ℝ) (p : Fin m → E), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
    (∀ k, p k ∈ X) ∧ ∑ k, w k • p k = x ∧ y = ∑ k, w k * g (p k)}

end TractableComposite


