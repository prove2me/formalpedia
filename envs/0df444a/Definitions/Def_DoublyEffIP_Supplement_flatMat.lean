-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_flatMat
-- name    : DoublyEffIP_Supplement_flatMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:33.173836+00:00
-- url     : https://prove2.me/theorems/66ac3e2b-e918-4048-b600-18b9dbc2b006
-- title:
--   A matrix as its list of entries, row by row
-- statement:
--   A $k\times L$ matrix $A$ is fed to a circuit on $\mathbb F^{k\times L}$ as the list of its entries row by row, $A_{0,0},\dots,A_{0,L-1},A_{1,0},\dots,A_{k-1,L-1}$, treating "matrices in $\mathbb F^{k\times L}$ as vectors in $\mathbb F^{kL}$".
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section A.2, p.35

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **A matrix as a list of entries, row by row** — the input `x ∈ F^{kL}` of a circuit on
`F^{k×L}` in Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section A.2, p.35 ("treating matrices in F^{k×L} as vectors in F^{kL}").

`flatMat A` lists `A 0 0, …, A 0 (L−1), A 1 0, …, A (k−1) (L−1)`.

**Formalization Note.** Row-major order; any fixed order gives the same circuit classes up to a
relabelling of input wires. -/
def flatMat {α : Type*} {k L : ℕ} (A : Fin k → Fin L → α) : List α :=
  (List.ofFn fun i => List.ofFn fun j => A i j).flatten

end DoublyEffIP.Supplement


