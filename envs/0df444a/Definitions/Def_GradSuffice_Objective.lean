-- Prove2me | Definitions.Def_GradSuffice_Objective
-- name    : GradSuffice_Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:19.776094+00:00
-- url     : https://prove2.me/theorems/028b7dea-1767-4bbb-aa29-7397beb29e13
-- title:
--   Admissible objective on a domain $W$
-- statement:
--   Fix a domain $W\subseteq X$. An **objective** on $W$ is a pair $(U,f)$ where
--   1. $U\subseteq X$ is open and convex and contains $W$;
--   2. $f:X\to\mathbb R$ is convex on $U$ and $1$-Lipschitz on $U$: $|f(w_1)-f(w_2)|\le\|w_1-w_2\|$ for $w_1,w_2\in U$.
--
--   This is the paper's standing assumption that objectives are convex and 1-Lipschitz and "defined on an open neighborhood of the domain $W$", which makes the subdifferential nonempty at every point of $W$. Only the values of $f$ on $U$ matter.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, pp.3–4

import Mathlib

namespace GradSuffice

/-- **Admissible objective on a domain `W`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, pp.3–4: objectives are convex and
1-Lipschitz with respect to the given norm, and "We will assume that the objective is defined on an
open neighborhood of the domain `W`, and hence that its subdifferential is nonempty at every point
of `W`"; p.3: subgradients exist for "`f` convex and 1-Lipschitz on an open convex domain".

**Formalization Note.** An objective is a pair `(U, f)`: `U` an open convex set containing `W`, and
`f : X → ℝ` convex and 1-Lipschitz on `U` (its values off `U` play no role). -/
structure Objective (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) where
  /-- The open convex neighbourhood of `W` on which the objective is defined. -/
  U : Set X
  /-- The objective function (only its values on `U` matter). -/
  f : X → ℝ
  isOpen_U : IsOpen U
  convex_U : Convex ℝ U
  subset_U : W ⊆ U
  convexOn : ConvexOn ℝ U f
  lipschitzOn : LipschitzOnWith 1 f U

end GradSuffice


