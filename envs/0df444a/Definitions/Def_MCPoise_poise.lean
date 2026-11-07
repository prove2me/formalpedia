-- Prove2me | Definitions.Def_MCPoise_poise
-- name    : MCPoise_poise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:54.063554+00:00
-- url     : https://prove2.me/theorems/bd7958a0-5a3a-4a7c-9f5f-45d166aab13b
-- title:
--   The poise of a subgraph
-- statement:
--   For demand pairs $D$ and a subgraph $H \subseteq G$ connecting every pair, the **poise** of $H$ is
--   $$\mathrm{poise}_D(H) := \max_{v \in V} \deg_H(v) + \max_{i \in [k]} \mathrm{dist}_H(s_i, t_i).$$
--   The poise bounds the multicommodity multicast time from below up to a factor $2$, and from above up to polylogarithmic factors.
--
--   **Formalization Note** A maximum over an empty index set is $0$. Every statement that uses the poise also asks for the connection clause.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_maxDeg

namespace MCPoise

/-- **The poise of a subgraph** `poise_D(H) := max_{v∈V} deg_H(v) + max_{i∈[k]} dist_H(s_i, t_i)`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3.

**Formalization Note.** The source defines poise only for `H` connecting every demand; on such `H` the
Mathlib `dist` is the true distance. Every statement that uses `poise` carries the `Connects` clause, as
`dist` is `0` on an unreachable pair. Both maxima are `Finset.sup`, equal to `0` when `n = 0` or `k = 0`. -/
noncomputable def poise (I : Inst) (H : SimpleGraph (Fin I.n)) : ℕ :=
  maxDeg H + Finset.univ.sup fun i : Fin I.k => H.dist (I.s i) (I.t i)

end MCPoise


