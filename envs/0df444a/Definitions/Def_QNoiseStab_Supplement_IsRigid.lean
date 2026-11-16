-- Prove2me | Definitions.Def_QNoiseStab_Supplement_IsRigid
-- name    : QNoiseStab_Supplement_IsRigid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:20:51.692472+00:00
-- url     : https://prove2.me/theorems/8353ac91-f0ee-4532-8f96-6715103f5d17
-- title:
--   $(g,h,c)$-rigid matrix
-- statement:
--   An $m\times n$ matrix $M$ over a field $F$ is **$(g,h,c)$-rigid** if every submatrix $M_{R,C}$, with $R$ a set of $k$ rows and $C$ a set of $w$ columns, satisfying $k\le g$ and $w\ge n-h$ has
--
--   $$
--   \operatorname{rank}_F M_{R,C}\ \ge\ c\,k .
--   $$
--
--   $(g,h,1)$-rigid matrices are called $(g,h)$-rigid. The $n\times n$ discrete Fourier transform matrix is $(n/4,n/4,1/2)$-rigid, and most square matrices over a finite set are $(\gamma n,\gamma n)$-rigid.
--
--   **Formalization Note** $g,h,c$ are real numbers with no constraint, as in the definition; rows and columns are arbitrary subsets.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 6.1, p.41

import Mathlib

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- A **`(g, h, c)`-rigid matrix** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 6.1, p.41: "An m × n matrix is
(g, h, c)-rigid iff every k × w submatrix where k ≤ g and w ≥ n − h has rank at least ck"): for
every set `R` of rows and every set `C` of columns with `|R| ≤ g` and `|C| ≥ n − h`, the
submatrix `M_{R,C}` has rank (over the field `F`) at least `c · |R|`.

**Formalization Note** `g, h, c` are real and unconstrained, as in the definition; theorems
that need `c > 0` say so. Rows and columns are arbitrary subsets (not contiguous blocks). -/
def IsRigid {F : Type} [Field F] {m n : ℕ} (M : Matrix (Fin m) (Fin n) F) (g h c : ℝ) : Prop :=
  ∀ (R : Finset (Fin m)) (C : Finset (Fin n)), (R.card : ℝ) ≤ g → (n : ℝ) - h ≤ C.card →
    c * R.card ≤ ((M.submatrix (fun i : R => (i : Fin m)) (fun j : C => (j : Fin n))).rank : ℝ)

end QNoiseStab.Supplement


