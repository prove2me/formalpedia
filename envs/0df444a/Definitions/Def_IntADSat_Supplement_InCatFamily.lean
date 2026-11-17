-- Prove2me | Definitions.Def_IntADSat_Supplement_InCatFamily
-- name    : IntADSat_Supplement_InCatFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:53:17.839209+00:00
-- url     : https://prove2.me/theorems/1ba0ab46-18e2-43b3-b6c4-f00dc23c77d1
-- title:
--   Membership in the test family $\mathcal F_n$
-- statement:
--   A graph $T$ belongs to $\mathcal F_n$ if $T$ is a caterpillar, $\operatorname{diam}T\le7$, and $|V(T)|\le m_n$. The family includes $K_1$.
--
--   **Formalization Note** $T$ has vertex set $\{0,\dots,k-1\}$, so $|V(T)|=k$; the diameter is Mathlib's graph diameter, which is the usual one for connected finite graphs such as caterpillars.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Corollary C.2, p.21 (PDF 22); Theorem 1.2, p.2 (PDF 3)

import Mathlib
import Definitions.Def_IntADSat_Supplement_IsCaterpillar
import Definitions.Def_IntADSat_Supplement_catBound

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `T ∈ F_n`: `T` is a caterpillar of diameter at most seven with at most `m_n` vertices
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Corollary C.2, p.21 (PDF 22); Theorem 1.2, p.2 (PDF 3)). `K_1` belongs to every `F_n` with
`m_n ≥ 1` (always, since `m_n ≥ 6`).

**Formalization Note** `T` has vertex set `Fin k`, so `|V(T)| = k`; `diam` is Mathlib's
`SimpleGraph.diam` (caterpillars are connected and finite, so it is the graph diameter). -/
def InCatFamily (n : ℕ) {k : ℕ} (T : SimpleGraph (Fin k)) : Prop :=
  IsCaterpillar T ∧ T.diam ≤ 7 ∧ k ≤ catBound n

end IntADSat.Supplement


