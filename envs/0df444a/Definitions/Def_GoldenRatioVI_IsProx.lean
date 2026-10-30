-- Prove2me | Definitions.Def_GoldenRatioVI_IsProx
-- name    : GoldenRatioVI_IsProx
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:33.345183+00:00
-- url     : https://prove2.me/theorems/2c99c64d-3d30-409b-aad3-ffc8959f2c07
-- title:
--   Proximal point $p=\operatorname{prox}_h(w)$ (argmin predicate)
-- statement:
--   Let $h:\mathcal E\to(-\infty,+\infty]$ have domain $D$ (finite values $h$ on $D$), and let $w\in\mathcal E$. A point $p$ is **the proximal point of $w$ under $h$**, written $p=\operatorname{prox}_h(w)$, if
--   $$p\in\operatorname*{argmin}_{x}\Big\{h(x)+\tfrac12\|x-w\|^2\Big\},$$
--   that is, $p\in D$ and $h(p)+\tfrac12\|p-w\|^2\le h(x)+\tfrac12\|x-w\|^2$ for every $x\in D$. For $\lambda>0$, $\operatorname{prox}_{\lambda g}$ uses $h=\lambda g$, which has the same domain as $g$.
--
--   The proximal step is the only place where $g$ enters Algorithm 1.
--
--   **Formalization Note** This is a predicate, not a function. For $h$ proper convex lsc on a finite-dimensional space the minimizer exists and is unique, so the predicate determines exactly the paper's $\operatorname{prox}_h(w)$.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), Preliminaries, p. 3 (definition of prox_g)

import Mathlib

namespace GoldenRatioVI

/-- **`p = prox_h(w)`: `p` minimizes `h(x) + ½‖x − w‖²`.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), Preliminaries,
p. 3: "The proximal operator prox_g for a proper lsc convex function g: E → (−∞, +∞] is defined as
prox_g(z) = argmin_x{g(x) + 1/2‖x − z‖²}."

`IsProx D h w p` says: `p ∈ D` and `h p + ‖p − w‖²/2 ≤ h x + ‖x − w‖²/2` for every `x ∈ D`, where
the extended-valued function is given by its domain `D` and finite values `h` on `D`.
For `λ > 0`, `prox_{λg}(w) = p` is `IsProx D (fun x => λ * g x) w p` (`λg` has domain `D`).

**Formalization Note.** The prox is a minimizer predicate, not a function. For a proper convex lsc
function on a finite-dimensional space the minimizer exists and is unique (the objective is
strongly convex and lsc with nonempty domain), so under (C2) the predicate determines exactly the
paper's `prox`. Points `x ∉ D` have objective `+∞` and are never minimizers. -/
def IsProx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (h : E → ℝ) (w p : E) : Prop :=
  p ∈ D ∧ ∀ x ∈ D, h p + ‖p - w‖ ^ 2 / 2 ≤ h x + ‖x - w‖ ^ 2 / 2

end GoldenRatioVI


