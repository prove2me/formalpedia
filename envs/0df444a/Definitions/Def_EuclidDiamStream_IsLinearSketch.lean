-- Prove2me | Definitions.Def_EuclidDiamStream_IsLinearSketch
-- name    : EuclidDiamStream_IsLinearSketch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:18.701886+00:00
-- url     : https://prove2.me/theorems/234553ae-dafd-4b3e-ae5e-7ee9067f0ef7
-- title:
--   $(s,\lambda)$-linear sketch (Definition 2.2)
-- statement:
--   For $s,\lambda\in\mathbb N$, an **$(s,\lambda)$-linear sketch** is a pair $(T,\mathrm{Dec})$, where $T$ is an $s\times N$ integer matrix with $\|T\|_\infty\le\lambda$ and $\mathrm{Dec}:\mathbb Z^s\to\{0,1\}$ is a function. On a frequency vector $v$, the sketch outputs $\mathrm{Dec}(Tv)$.
--
--   Streaming algorithms reduce to these sketches, which turns the lower bound into a question of linear algebra.
--
--   **Formalization Note** The definition records the entry bound on $T$; $\mathrm{Dec}$ is an arbitrary function, so the theorems simply quantify over it.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7, Def. 2.2

import Mathlib
import Definitions.Def_EuclidDiamStream_Point

namespace EuclidDiamStream

/-- Definition 2.2 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7: the matrix part of an `(s,λ)`-linear sketch. `T` is an `s × N` integer
matrix, with rows indexed by `Fin s` and columns by the grid, and `‖T‖_∞ ≤ λ` (the maximum absolute value
of an entry).

**Formalization Note.** The decoder `Dec : ℤ^s → {0,1}` is an arbitrary function `(Fin s → ℤ) → Bool`, on
which the definition puts no condition; each theorem quantifies over it, and the sketch's output on `v` is
`Dec (T.mulVec v)`. -/
def IsLinearSketch {s d Δ : ℕ} (T : Matrix (Fin s) (Point d Δ) ℤ) (lam : ℕ) : Prop :=
  ∀ i x, |T i x| ≤ (lam : ℤ)

end EuclidDiamStream


