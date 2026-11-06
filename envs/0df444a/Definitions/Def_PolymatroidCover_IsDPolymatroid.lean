-- Prove2me | Definitions.Def_PolymatroidCover_IsDPolymatroid
-- name    : PolymatroidCover_IsDPolymatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:20.015372+00:00
-- url     : https://prove2.me/theorems/144362af-db4f-4e14-9c91-a02becbf4bbc
-- title:
--   $d$-polymatroid
-- statement:
--   A polymatroid $f : 2^E \to \mathbb Z_{\ge 0}$ is a **$d$-polymatroid** if
--
--   $$
--   f(e) \le d \qquad \text{for every } e \in E.
--   $$
--
--   Matroid rank functions are the $1$-polymatroids, and the sum of the rank functions of $d$ matroids on $E$ is a $d$-polymatroid. The approximation factor of the mission's main theorem is linear in $d$.
--
--   **Formalization Note** $d$ is a natural number.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PolymatroidCover_IsPolymatroid

namespace PolymatroidCover

/-- A `d`-polymatroid (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.2 = PDF p.4): a polymatroid
`f : 2^E → ℤ_{≥0}` with `f(e) := f({e}) ≤ d` for every `e ∈ E`.

**Formalization Note** `d` is a natural number and `E = Fin n`. -/
def IsDPolymatroid {n : ℕ} (d : ℕ) (f : Finset (Fin n) → ℕ) : Prop :=
  IsPolymatroid f ∧ ∀ e : Fin n, f {e} ≤ d

end PolymatroidCover


