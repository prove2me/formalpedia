-- Prove2me | Definitions.Def_EulerSparsify_Supplement_encClusterIn
-- name    : EulerSparsify_Supplement_encClusterIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:32:48.503844+00:00
-- url     : https://prove2.me/theorems/79be2ccd-2d15-4fbb-9555-ed64fed1451c
-- title:
--   Encoding of an instance $(G,\gamma)$ of Theorem 4.1
-- statement:
--   The binary encoding of an input of the algorithm of Theorem 4.1: a finite graph with rational edge weights (vertices $0,\dots,n-1$, each edge given by its two endpoints and its weight), followed by the rational parameter $\gamma$.
--
--   The graph is written with the base mission's word list `RatDigraph.tok` (the number of vertices, then the edge list with its length first), $\gamma$ is written as a binary rational, and the words are joined by a separator symbol. The alphabet has four symbols: the bits $0$, $1$, a symbol $2$ used inside a rational and the separator $3$. This fixes what a Turing machine reads when it runs the algorithm of Theorem 4.1.
--
--   **Formalization Note** The encoding is `joinW (I.tok ++ [encRat γ])`, the same pattern as the base mission's published `encLevelIn` and `encSparsifyIn`; the length of the encoding is the usual bit size of the instance.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_RatDigraph

namespace EulerSparsify

namespace Supplement

/-- **Encoding of an instance `(G, γ)` of Theorem 4.1** (p.12, PDF p.14).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 4.1: "There is an
algorithm which given any G = (V, E, w) with n = |V| and γ ≥ 100, computes a (ρ, γ)-strong ER
clustering".

The words of the rational weighted graph (published `RatDigraph.tok`), then `γ` as a binary
rational (published `OnlineCRS.Combine.encRat`), joined by the separator `3` (published `joinW`).

**Formalization Note.** Inputs are read in Mathlib's Turing-machine model over the published
alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator), as
in the base mission's `encLevelIn` and `encSparsifyIn`. -/
def encClusterIn (x : RatDigraph × ℚ) : List OnlineCRS.Combine.Sym :=
  joinW (x.1.tok ++ [OnlineCRS.Combine.encRat x.2])

end Supplement

end EulerSparsify


