-- Prove2me | Definitions.Def_MinrankTW_Supplement_thm5Output
-- name    : MinrankTW_Supplement_thm5Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:04:33.048199+00:00
-- url     : https://prove2.me/theorems/c67e7716-14b7-4914-88ba-5497ef788375
-- title:
--   Output layout of the circuit encoding (Theorem 5)
-- statement:
--   The RAM output of the construction of Theorem 5 lists, in consecutive memory cells:
--
--   1. the dimension $n$ of the square fixed/free matrix, the number $N$ of nodes of the path decomposition, and the target rank $r$;
--   2. the $n^2$ entry codes of the fixed/free table, row by row;
--   3. for every node $s$ of the path $0-1-\dots-(N-1)$, the $2n$ membership bits of its bag (row vertices first, then column vertices);
--   4. the $r$ row indices and then the $r$ column indices of the fixed identity block $I_r$;
--   5. for every input $x_1,\dots,x_v$, the row and column of the matrix entry that stores it.
--
--   The last list makes the correspondence between completions and input assignments an explicit read-out map.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 5, p.18, and its proof, pp.18–19

import Mathlib
import Definitions.Def_MinrankTW_Supplement_fixedFree

namespace MinrankTW.Supplement

/-- The RAM output layout of Theorem 5 (Perles–Weinstein, *Efficient Algorithms for Minrank and
Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991),
Theorem 5, p.18: "construct a square fixed/free matrix … The matrix contains a fixed I_r, and a
support path decomposition of width at most w is supplied"). Cells, from `0`:
`n, N, r`; the `n²` entry codes `ffCode e (A i j)` of the `n × n` fixed/free table, row by row;
the `N·2n` bag bits `bag s u` node by node (row vertex `r_i` at offset `i`, column vertex `c_j` at
offset `n + j`), the path being `0 – 1 – ⋯ – (N − 1)`; the `r` row indices and then the `r` column
indices of the fixed identity block; and, for each input `x_1, …, x_v`, the row and column of the
entry of the matrix that stores it.

**Formalization Note** The support vertices `Fin n ⊕ Fin n` are numbered by `finSumFinEquiv`. The
read-out positions make the paper's "rank-r completions correspond bijectively to satisfying input
assignments" an explicit map. -/
def thm5Output {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) (n N r v : ℕ)
    (A : Fin n → Fin n → Option F) (bag : Fin N → Fin n ⊕ Fin n → Bool)
    (rowI colI : Fin r → Fin n) (pos : Fin v → Fin n × Fin n) : List ℕ :=
  [n, N, r] ++
  (List.finRange n).flatMap (fun i => (List.finRange n).map fun j => ffCode e (A i j)) ++
  (List.finRange N).flatMap
    (fun s => (List.finRange (n + n)).map fun u => (bag s (finSumFinEquiv.symm u)).toNat) ++
  (List.finRange r).map (fun a => (rowI a : ℕ)) ++
  (List.finRange r).map (fun a => (colI a : ℕ)) ++
  (List.finRange v).flatMap (fun i => [((pos i).1 : ℕ), ((pos i).2 : ℕ)])

end MinrankTW.Supplement


