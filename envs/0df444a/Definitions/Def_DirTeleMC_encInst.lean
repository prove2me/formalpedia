-- Prove2me | Definitions.Def_DirTeleMC_encInst
-- name    : DirTeleMC_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:20.654195+00:00
-- url     : https://prove2.me/theorems/5cc7e458-8077-4e89-beea-dd55a7bd0759
-- title:
--   Binary encodings of instances and schedules
-- statement:
--   For the time bound of Theorem 1.1, an instance is written over the four-letter alphabet $\{0,1,2,3\}$ as: $n$ in binary; the $n^2$ entries of the adjacency matrix row by row, one bit each; $s$ in binary; the indicator of $K$, one bit per vertex; $k$ in binary — each field followed by the separator $3$. A schedule (vertices as numbers) is written as its number of rounds, then each round as its number of calls followed by the two endpoints of each call, all in binary and each followed by $3$.
--
--   Both encodings are injective. The input length $m$ of an instance satisfies $n^2 \le m = O(n^2)$, so $(m+2)^{O(\ell)}$ and $n^{O(\ell)}$ are the same bound.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 1.1, p.1 (PDF p.2); proof of Theorem 1.1, "Running time", p.31 (PDF p.32)

import Mathlib
import Definitions.Def_DirTeleMC_Inst
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat

namespace DirTeleMC

open OnlineCRS.Combine

/-- **Encoding of an instance** for the machine of Theorem 1.1.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 1.1, p.1 ("runs in n^{O(ℓ)} time"); proof of Theorem 1.1, "Running time",
p.31.

Over the published alphabet `Sym = Fin 4`, each field followed by the separator `3`: `n` in binary; the `n²`
entries of the adjacency matrix row by row, one bit each; `s` in binary; the indicator of `K`, one bit per
vertex; `k` in binary.

**Formalization Note.** The source names no machine or encoding. The adjacency matrix makes the input length
`m` satisfy `n² ≤ m = O(n² + log n)`, so `(m + 2)^{O(ℓ)}` and `n^{O(ℓ)}` are the same bound for `n ≥ 2`. No
field contains the symbol `3`, so the encoding is injective (`Solutions/verification/DirTeleMC_sanity.lean`). -/
def encInst (I : Inst) : List Sym :=
  encNat I.n ++ [3] ++
    ((List.finRange I.n).flatMap fun i => (List.finRange I.n).map fun j => bit (I.adj i j)) ++ [3] ++
    encNat I.s.val ++ [3] ++ ((List.finRange I.n).map fun v => bit (decide (v ∈ I.K))) ++ [3] ++
    encNat I.k ++ [3]

/-- **Encoding of a schedule** (with vertices as numbers): the number of rounds, then every round as the
number of its calls followed by the two endpoints of every call, all in binary and each followed by the
separator `3`. Injective (`Solutions/verification/DirTeleMC_sanity.lean`). -/
def encSched (S : List (List (ℕ × ℕ))) : List Sym :=
  encNat S.length ++ [3] ++
    S.flatMap fun r => encNat r.length ++ [3] ++ r.flatMap fun c => encNat c.1 ++ [3] ++ encNat c.2 ++ [3]

end DirTeleMC


