-- Prove2me | Definitions.Def_IntADSat_Supplement_catTypeCount
-- name    : IntADSat_Supplement_catTypeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:54:37.802638+00:00
-- url     : https://prove2.me/theorems/ab83cf6a-bac9-40d7-b810-76fcbc26ee4a
-- title:
--   Number of isomorphism types in $\mathcal F_n$
-- statement:
--   The number of isomorphism types of graphs in $\mathcal F_n$, i.e. the number of isomorphism classes of caterpillars of diameter at most seven with at most $m_n$ vertices. Theorem 1.2 asserts it is $O(n^3(\log n)^3)$.
--
--   **Formalization Note** Counted as the classes, modulo graph isomorphism, of the members of $\mathcal F_n$ on the vertex sets $\{0,\dots,k-1\}$, $k\le m_n$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem 1.2, p.2 (PDF 3); Corollary C.2, p.21 (PDF 22)

import Mathlib
import Definitions.Def_IntADSat_Supplement_InCatFamily

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The number of **isomorphism types** in `F_n` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem 1.2, p.2 (PDF 3); Corollary C.2, p.21
(PDF 22)).

**Formalization Note** Every graph with at most `m_n` vertices is isomorphic to one on `Fin k` with
`k ≤ m_n`; the count is the number of classes of the members `T : SimpleGraph (Fin k)`, `k ≤ m_n`, of
`F_n` modulo graph isomorphism (`Quot` by the isomorphism relation, an equivalence). -/
noncomputable def catTypeCount (n : ℕ) : ℕ :=
  Nat.card (Quot fun (T T' : {T : Σ k : Fin (catBound n + 1), SimpleGraph (Fin k) // InCatFamily n T.2}) =>
    Nonempty (T.1.2 ≃g T'.1.2))

end IntADSat.Supplement


