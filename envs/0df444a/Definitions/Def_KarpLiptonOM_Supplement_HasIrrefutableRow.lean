-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_HasIrrefutableRow
-- name    : KarpLiptonOM_Supplement_HasIrrefutableRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:41:53.091882+00:00
-- url     : https://prove2.me/theorems/ad86a82a-9a69-420c-a1e2-a8658db906fe
-- title:
--   Irrefutable row of the matrix of a circuit
-- statement:
--   The matrix of a circuit $V:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ has an **irrefutable row** if some row beats every column:
--
--   $$
--   \exists y\in\{0,1\}^a\;\forall z\in\{0,1\}^b\;\; V(y,z)=1 .
--   $$
--
--   If there is an irrefutable row, no set of columns beats it, so no column-side certificate exists.
--
--   **Formalization Note** $V(y,z)$ is the value of the circuit with $a+b$ inputs on $yz$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.5 ("Matrices [CR11, Def. 4.6]"), p.32; p.12

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace KarpLiptonOM.Supplement

/-- The matrix of a circuit `V : {0,1}^a × {0,1}^b → {0,1}` has an **irrefutable row** (§A.5,
"Matrices [CR11, Def. 4.6]", Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.32: "A row is irrefutable if it beats every column"): some
`y ∈ {0,1}^a` with `V(y, z) = 1` for every `z ∈ {0,1}^b`.

**Formalization Note** `V(y, z) = V.eval (y ++ z)` for a circuit with `a + b` inputs. -/
def HasIrrefutableRow (a b : ℕ) (V : Circuit (a + b)) : Prop :=
  ∃ y : List Bool, y.length = a ∧ ∀ z : List Bool, z.length = b → V.eval (y ++ z) = true

end KarpLiptonOM.Supplement


