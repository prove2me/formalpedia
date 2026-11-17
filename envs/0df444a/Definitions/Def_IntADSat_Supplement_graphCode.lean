-- Prove2me | Definitions.Def_IntADSat_Supplement_graphCode
-- name    : IntADSat_Supplement_graphCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:50.351849+00:00
-- url     : https://prove2.me/theorems/3669ee5c-0569-4af2-903f-f21545570954
-- title:
--   Adjacency-bit code of a graph
-- statement:
--   The input code of a graph $G$ on the vertex set $\{0,\dots,n-1\}$ is its $n\times n$ adjacency matrix written as $n^2$ bits in row-major order (bit $(i,j)$ is $1$ iff $i\sim j$). Its length $n^2$ is polynomial in the graph order $n$, and $n$ is recovered as the square root of the length. This is the input of the algorithm in Theorem A.6.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.6, p.13 (PDF 14) (input of the algorithm)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The input code of a graph on `Fin n`: its `n × n` adjacency matrix as `n²` bits in row-major order
(entry `(i, j)` is `true` iff `i ~ j`). This is the input of the algorithm in Theorem A.6
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.13 (PDF 14)); its length `n²` is polynomial in the graph order `n`.

**Formalization Note** `n` is recovered as the square root of the length, so the code is injective on
graphs of all orders. Adjacency is decided classically. -/
noncomputable def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact (List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide (G.Adj i j)

end IntADSat.Supplement


