-- Prove2me | Definitions.Def_NearestDSM_equivClass
-- name    : NearestDSM_equivClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:04.84058+00:00
-- url     : https://prove2.me/theorems/e0b9594a-0b09-489b-8d15-3e631ae76fd5
-- title:
--   The equivalence class $[y]$
-- statement:
--   Two vectors $y,y'\in\mathbb R^{2n-1}$ are **equivalent**, written $y\sim y'$, if
--   $$
--   (\hat x+A^Ty)_+=(\hat x+A^Ty')_+ ,
--   $$
--   that is, they produce the same primal matrix $X$. The equivalence class of $y$ is
--   $$
--   [y]:=\{y'\in\mathbb R^{2n-1}\mid y\sim y'\}.
--   $$
--   Each class is a polyhedron (Theorem 3.9), and the modified Newton method moves every iterate to a vertex of its class before taking a Newton step.
--
--   **Formalization Note** The paper's $n$ is $n+1$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Definition 3.1, p.12

import Mathlib
import Definitions.Def_NearestDSM_Xmat

namespace NearestDSM

/-- The equivalence class `[y]` of Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, Definition 3.1, p.12: `y ∼ y'` if
`(x̂ + Aᵀy)₊ = (x̂ + Aᵀy')₊`, and `[y] := {y' ∈ ℝ^{2n−1} | y ∼ y'}`. -/
def equivClass {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) : Set (Dual n) :=
  {y' | Xmat Xh y' = Xmat Xh y}

end NearestDSM


