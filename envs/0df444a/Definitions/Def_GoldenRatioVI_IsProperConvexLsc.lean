-- Prove2me | Definitions.Def_GoldenRatioVI_IsProperConvexLsc
-- name    : GoldenRatioVI_IsProperConvexLsc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:43.581911+00:00
-- url     : https://prove2.me/theorems/a2718032-4d72-4546-9340-a42c42218321
-- title:
--   Condition (C2): $g$ proper, convex and lower semicontinuous
-- statement:
--   Let $\mathcal E$ be a real inner product space. A function $g:\mathcal E\to(-\infty,+\infty]$, given by its domain $D=\operatorname{dom} g$ and its finite values on $D$, satisfies **(C2)** if
--
--   1. $g$ is **proper**: $D\neq\emptyset$ (and $g$ never takes the value $-\infty$);
--   2. $g$ is **convex**: $D$ is convex and $g$ is convex on $D$;
--   3. $g$ is **lower semicontinuous** as a function $\mathcal E\to(-\infty,+\infty]$ (with value $+\infty$ off $D$).
--
--   This is the standing assumption (C2) on the nonsmooth part of the variational inequality (1); it covers indicator functions $\delta_C$ of nonempty closed convex sets as well as general proper closed convex functions.
--
--   **Formalization Note** Lower semicontinuity is that of the extended function, so no separate closedness of $D$ is assumed.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §1, p. 1, condition (C2)

import Mathlib
import Definitions.Def_GoldenRatioVI_extVal

namespace GoldenRatioVI

/-- **Condition (C2): `g` is a proper convex lower semicontinuous function `E → (−∞, +∞]`.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §1, p. 1,
(C2): "g: E → (−∞, +∞] is a proper convex lower semicontinuous (lsc) function".

`IsProperConvexLsc D g` says: the domain `D` is nonempty (proper), `g` is convex on `D`
(`D` is a convex set and `g` is convex on it), and the extended-valued function
`extVal D g` (equal to `g` on `D`, `+∞` off `D`) is lower semicontinuous on `E`.

**Formalization Note.** The paper's `g : E → (−∞, +∞]` is encoded as the pair `(D, g)` with
`D = dom g` and `g : E → ℝ` its finite values on `D`. "Proper" (not identically `+∞`, never `−∞`)
is `D.Nonempty` together with real values. An extended-valued function is convex exactly when its
domain is convex and it is convex there, which is `ConvexOn ℝ D g`. Lower semicontinuity is that of
the extended function, so it forces `g → +∞` at boundary points of `D` not in `D`; no separate
closedness of `D` is assumed. -/
def IsProperConvexLsc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (g : E → ℝ) : Prop :=
  D.Nonempty ∧ ConvexOn ℝ D g ∧ LowerSemicontinuous (extVal D g)

end GoldenRatioVI


