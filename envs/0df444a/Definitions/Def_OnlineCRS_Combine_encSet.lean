-- Prove2me | Definitions.Def_OnlineCRS_Combine_encSet
-- name    : OnlineCRS_Combine_encSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:22:13.736853+00:00
-- url     : https://prove2.me/theorems/6155d3d8-b6f0-4ce7-994c-13bb0c3ddfa7
-- title:
--   Encoding of a subset $S\subseteq\{0,\dots,k-1\}$
-- statement:
--   A set $S\subseteq\{0,\dots,k-1\}$ is encoded by its characteristic bit string $(\mathbf 1[0\in S],\dots,\mathbf 1[k-1\in S])$, of length $k$. It encodes the queried set in "is a set $S\subseteq N$ in $\mathcal F_{\pi,x}$?".
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit

namespace OnlineCRS.Combine

/-- **Encoding of a subset `S ⊆ {0, …, k − 1}`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): the query "is a set `S ⊆ N` in `F_{π,x}`?".

`encSet S` is the characteristic bit string of `S`, of length `k`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def encSet {k : ℕ} (S : Finset (Fin k)) : List Sym :=
  (List.finRange k).map fun j => bit (decide (j ∈ S))

end OnlineCRS.Combine


