-- Prove2me | Definitions.Def_GoldenRatioVI_extVal
-- name    : GoldenRatioVI_extVal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:12.741204+00:00
-- url     : https://prove2.me/theorems/acd3c01d-bb51-490a-9025-2e46c29fccce
-- title:
--   Extended-valued function $g:\mathcal E\to(-\infty,+\infty]$ from its domain and finite values
-- statement:
--   Let $D\subseteq\mathcal E$ and $g:\mathcal E\to\mathbb R$. The **extended-valued function determined by $(D,g)$** is
--   $$\tilde g(x)=\begin{cases} g(x), & x\in D,\\ +\infty, & x\notin D.\end{cases}$$
--   Every function $\mathcal E\to(-\infty,+\infty]$ arises this way with $D=\operatorname{dom} g=\{x: g(x)<+\infty\}$.
--
--   It is the device by which the paper's extended-valued $g$ in the variational inequality (1) is represented: $D$ is its effective domain and $g$ its finite values.
--
--   **Formalization Note** The function takes values in `EReal` and is used only inside lower semicontinuity (in the definition of condition (C2)); no extended-real arithmetic is performed with it.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §1, p. 1, condition (C2), and Preliminaries, p. 3 (definition of dom g)

import Mathlib

namespace GoldenRatioVI

/-- **The extended-valued function `g : E → (−∞, +∞]` determined by its domain and finite values.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §1, p. 1,
condition (C2): "g: E → (−∞, +∞] is a proper convex lower semicontinuous (lsc) function"; and
Preliminaries, p. 3: "by dom g we denote the domain of g, i.e., the set {x: g(x) < +∞}".

`extVal D g x` is `g x` (as an extended real) when `x ∈ D` and `+∞` otherwise. It is the paper's
extended-valued `g`, given by its effective domain `D = dom g` and its finite values `g` on `D`.

**Formalization Note.** Values of `g : E → ℝ` off `D` are irrelevant. This function is used only
inside `LowerSemicontinuous` (in `IsProperConvexLsc`); no extended-real arithmetic is ever done
with it. -/
noncomputable def extVal {E : Type*} (D : Set E) (g : E → ℝ) : E → EReal :=
  open Classical in fun x => if x ∈ D then ((g x : ℝ) : EReal) else ⊤

end GoldenRatioVI


