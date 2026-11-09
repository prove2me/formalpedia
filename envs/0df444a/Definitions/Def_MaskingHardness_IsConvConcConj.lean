-- Prove2me | Definitions.Def_MaskingHardness_IsConvConcConj
-- name    : MaskingHardness_IsConvConcConj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:19.191301+00:00
-- url     : https://prove2.me/theorems/84fdb0c5-1b44-43ba-8ade-d772c59471b6
-- title:
--   Convex–concave conjugates on $\mathbb R^n$ (Definition 2.6)
-- statement:
--   Two functions $g,h:\mathbb R^n\to\overline{\mathbb R}$ are **convex–concave conjugates** if $g$ is a closed proper convex function, $h$ is a closed proper concave function, and
--
--   $$
--   g(a)=\sup_{b\in\mathbb R^n} h(b)-\langle a,b\rangle,\qquad h(b)=\inf_{a\in\mathbb R^n} g(a)+\langle a,b\rangle .
--   $$
--
--   Equivalently, $a\mapsto g(-a)$ and $b\mapsto -h(b)$ are convex conjugates in the usual sense. Two-input functions $g,h:\mathcal Y\times\mathbb R^n\to\overline{\mathbb R}$ are convex–concave conjugates (Definition 2.7) when $g(y,\cdot)$ and $h(y,\cdot)$ are, for every $y$. A function given only on a subset $S\subseteq\mathbb R^n$, such as a fidelity function on the simplex $\Delta_k$, is judged by its extension by $-\infty$ (concave case) or $+\infty$ (convex case) outside $S$ (Definition 2.2).
--
--   This is the hypothesis relating a loss $g$ and a fidelity function $h$ in the main theorem.
--
--   **Formalization Note** $\mathbb R^n$ is a finite-index function space `n → ℝ` with the dot product; the predicate is the dot-product instance of `IsConvConcConjWith`: the two formulas plus properness of $g$ and $h$, which together are equivalent to Definition 2.6.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 2.6, p.17 (PDF p.19); Definition 2.7, p.17 (PDF p.19); Definition 2.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConjWith

namespace MaskingHardness

/-- **Convex–concave conjugates** on `ℝⁿ` (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 2.6,
printed p.17 = PDF p.19): `g, h : ℝⁿ → ℝ̄` with
`g(a) = sup_b h(b) − ⟨a, b⟩`, `h(b) = inf_a g(a) + ⟨a, b⟩`,
`g` proper convex and `h` proper concave. The two-input version (Definition 2.7) is
`∀ y, IsConvConcConj (g y) (h y)`.

**Formalization Note** `ℝⁿ` is `n → ℝ` for a finite index type `n`, with the dot product
`a ⬝ᵥ b`; closedness and (con)vexity follow from the two formulas (see `IsConvConcConjWith`).
A function `h` defined only on a subset `S` (such as `h : Δ_k → ℝ̄`) is extended by `−∞` off `S`,
as Definition 2.2 prescribes. -/
def IsConvConcConj {n : Type*} [Fintype n] (g h : (n → ℝ) → EReal) : Prop :=
  IsConvConcConjWith (fun a b => a ⬝ᵥ b) g h

end MaskingHardness


