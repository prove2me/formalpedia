-- Prove2me | Definitions.Def_SparseDisc_degeneracy
-- name    : SparseDisc_degeneracy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:11.352444+00:00
-- url     : https://prove2.me/theorems/d7e38256-1d77-40f0-bebf-a9232d1b5929
-- title:
--   Degeneracy $\mathrm{dgn}(H)$
-- statement:
--   The **degeneracy** $\operatorname{dgn}(H)$ of a finite graph $H$ is the least $d$ such that $H$ is $d$-degenerate.
--
--   **Formalization Note** It is the infimum of $\{d : H \text{ is } d\text{-degenerate}\}$, a nonempty set of naturals on a finite vertex type (every ordering works with $d = |V|$), so the infimum is attained.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8, p.29; also p.4

import Mathlib
import Definitions.Def_SparseDisc_HasDegenOrdering

namespace SparseDisc

/-- The **degeneracy** `dgn(H)`: the least `d` such that `H` is `d`-degenerate
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Section 8, p.29; also p.4).

**Formalization Note** On a finite vertex type the set `{d | HasDegenOrdering H d}` is nonempty
(any ordering works with `d = |V|`), so the `sInf` is attained and is not the junk value. -/
noncomputable def degeneracy {V : Type} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sInf {d : ℕ | HasDegenOrdering H d}

end SparseDisc


