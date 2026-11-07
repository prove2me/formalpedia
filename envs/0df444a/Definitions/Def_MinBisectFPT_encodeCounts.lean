-- Prove2me | Definitions.Def_MinBisectFPT_encodeCounts
-- name    : MinBisectFPT_encodeCounts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:17.844136+00:00
-- url     : https://prove2.me/theorems/0d960a4d-381f-40d9-bd6f-b0cc52bb8e6d
-- title:
--   Bit encodings of the graph, the output table and a vertex set
-- statement:
--   The word machines of this mission read and write integers through the published injective self-delimiting integer code (unary bit length, a separator, then the bits).
--
--   1. The **input** of Theorems 1.1 and 1.3 is $n$, then the $n^2$ adjacency bits of $G$ row by row, then $k$.
--   2. The **output** of Theorem 1.1 is the exact integers $C_G(\ell,j)$ in binary, for $\ell=0,\dots,n$ and $j=0,\dots,k$, in that row-major order.
--   3. A **vertex set** is its size, then its elements in increasing order.
--
--   **Formalization Note** The paper fixes no format. The running times of the mission are functions of $n$ and $k$ themselves, not of the input length, so the format changes no statement.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MinBisectFPT_countSets

open scoped Classical

namespace MinBisectFPT

open ExponomialAssortment.FPTAS (encodeNat)

/-- **Input of Theorem 1.1 and Theorem 1.3 on a bit-cost machine.** `n`, then the `n²` adjacency
bits row by row, then `k`, all with the injective self-delimiting published integer code.

**Formalization Note** The paper (STOC 2027 submission, manuscript sha256 8db80a52…, p.2) fixes no
input format. `n` and `k` are written in binary; the time bounds of this mission are in `n` and `k`
themselves, never in the input length, so the choice changes no statement. -/
noncomputable def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : List Bool :=
  encodeNat n ++
    (List.finRange n).flatMap (fun u => (List.finRange n).map fun v => decide (G.Adj u v)) ++
      encodeNat k

/-- **Output of Theorem 1.1.** The exact integers `C_G(ℓ, j)` in binary, for `ℓ = 0, …, n` and
`j = 0, …, k`, in that row-major order (STOC 2027 submission, manuscript sha256 8db80a52…, p.2). -/
noncomputable def encodeCounts {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : List Bool :=
  (List.range (n + 1)).flatMap fun l =>
    (List.range (k + 1)).flatMap fun j => encodeNat (countSets G l j)

/-- A vertex set: its size, then its elements in increasing order, all with the published integer
code. -/
noncomputable def encodeSet {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  encodeNat S.card ++ ((List.finRange n).filter (· ∈ S)).flatMap fun v => encodeNat v.val

end MinBisectFPT


