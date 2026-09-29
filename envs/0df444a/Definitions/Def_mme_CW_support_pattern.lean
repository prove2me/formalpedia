-- Prove2me | Definitions.Def_mme_CW_support_pattern
-- name    : mme_CW_support_pattern
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T18:06:03.665067+00:00
-- url     : https://prove2.me/theorems/7f6d94a7-2c21-4f05-9990-72e1c97bdf0d
-- statement:
--   **The canonical Coppersmith–Winograd support pattern.**
--
--   `CWSupportPattern : Finset (Fin 3 × Fin 3 × Fin 3)` is the explicit 6-element subset
--
--   $$S \;=\; \{(0,1,1),\; (1,0,1),\; (1,1,0),\; (0,0,2),\; (0,2,0),\; (2,0,0)\}$$
--
--   of type-triples in $(\mathrm{Fin}\,3)^3$. These are precisely the type-triples appearing in the rank-one expansion of the CW tensor $T_q$ under the canonical 3-grading partitioning each mode's basis as $\{0\} \sqcup \{1, \ldots, q\} \sqcup \{q{+}1\}$:
--
--   * $(0, 1, 1), (1, 0, 1), (1, 1, 0)$ — the "middle" terms $e_0 \otimes e_i \otimes e_i + e_i \otimes e_0 \otimes e_i + e_i \otimes e_i \otimes e_0$ for $i = 1, \ldots, q$, in which exactly one mode carries the boundary index $0$ and the other two carry middle indices.
--
--   * $(0, 0, 2), (0, 2, 0), (2, 0, 0)$ — the three "boundary" terms $e_0 \otimes e_0 \otimes e_{q+1}, e_0 \otimes e_{q+1} \otimes e_0, e_{q+1} \otimes e_0 \otimes e_0$, in which two modes carry the left-boundary index and one carries the right-boundary index.
--
--   The set is `LaserSymmetric` — closed under the cyclic permutation $(\alpha, \beta, \gamma) \mapsto (\beta, \gamma, \alpha)$ — which is the structural property that enables the *symmetric* laser-method analysis (every type-triple in the support contributes equally to the three cyclic factor positions of the matrix-multiplication blocks).
--
--   **Standalone Definition vs inline literal.** Defined as a standalone `Finset` rather than inlined into the CW witness theorem so that downstream nodes (CW alignment lemma, CW value bound, etc.) can refer to it by name and so that the symmetry property `mme_CW_support_pattern_symmetric` is statable as a focused stand-alone leaf.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

/-! # The canonical Coppersmith–Winograd support pattern

`CWSupportPattern : Finset (Fin 3 × Fin 3 × Fin 3)` is the explicit 6-element
finite subset

  `{(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)}`

of type-triples. These are precisely the type-triples appearing in the rank-one
expansion of the CW tensor `T_q` under the canonical 3-grading partitioning
each mode's basis as `{0} ⊔ {1, …, q} ⊔ {q+1}`:

* `(0, 1, 1), (1, 0, 1), (1, 1, 0)` — the "middle" terms
  `e_0 ⊗ e_i ⊗ e_i + e_i ⊗ e_0 ⊗ e_i + e_i ⊗ e_i ⊗ e_0` for `i = 1, …, q`,
  in which one mode carries the boundary index `0` and the other two carry
  the middle indices.
* `(0, 0, 2), (0, 2, 0), (2, 0, 0)` — the three "boundary" terms
  `e_0 ⊗ e_0 ⊗ e_{q+1}, e_0 ⊗ e_{q+1} ⊗ e_0, e_{q+1} ⊗ e_0 ⊗ e_0`,
  in which two modes carry the left-boundary index and one carries the
  right-boundary index.

The set is `LaserSymmetric` — closed under the cyclic permutation
`(α, β, γ) ↦ (β, γ, α)` — which is what enables the symmetric laser-method
analysis. -/

namespace MME

/-- The canonical CW support pattern. -/
def CWSupportPattern : Finset (Fin 3 × Fin 3 × Fin 3) :=
  {(0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0)}

end MME


