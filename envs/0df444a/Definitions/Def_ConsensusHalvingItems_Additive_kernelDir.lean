-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_kernelDir
-- name    : ConsensusHalvingItems_Additive_kernelDir
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:49.713835+00:00
-- url     : https://prove2.me/theorems/a30a5e3b-3bba-410e-b4bb-4d44939aee3e
-- title:
--   Gaussian elimination: a nonzero solution of a homogeneous system
-- statement:
--   Given a list of rows $r^{(1)}, \dots, r^{(p)} \in \mathbb{Q}^m$, read as the homogeneous linear system $r^{(\ell)} \cdot d = 0$, this procedure runs Gauss–Jordan elimination with every rational operation charged by the cost model:
--
--   1. it copies the rows, charging each entry's bit size;
--   2. it scans the columns $c = 1, \dots, m$; in column $c$ it takes the first remaining row whose entry in column $c$ is nonzero, divides it by that entry, and subtracts suitable multiples of it from every other row so that column $c$ becomes zero elsewhere; columns without such a row are **free**;
--   3. if every column is a pivot column, it reports that $d = 0$ is the only solution;
--   4. otherwise, with $f$ the lowest free column, it returns the vector $d$ with $d_f = 1$, $d_c = 0$ for the other free columns, and $d_p = -R_{p,f}$ for each pivot column $p$, where $R_{p,f}$ is the entry in column $f$ of the reduced pivot row of column $p$.
--
--   The returned $d$ solves the system and is nonzero. This is the Gaussian elimination of footnote 5 of the paper, with the free choice there ("setting one of the non-pivots to be an arbitrary number") fixed as above.
--
--   **Formalization Note** Rows are given as functions `Fin m → ℚ`; the result is `none` (only the trivial solution) or `some d`.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶2 and footnote 5, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize
import Definitions.Def_ConsensusHalvingItems_Additive_qsub
import Definitions.Def_ConsensusHalvingItems_Additive_qmul
import Definitions.Def_ConsensusHalvingItems_Additive_qdiv
import Definitions.Def_ConsensusHalvingItems_Additive_qeq

namespace ConsensusHalvingItems.Additive

/-- **Gaussian elimination: a nonzero solution of a homogeneous system, or none.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, p. 5, and footnote 5: "Finding a solution … can
be done in polynomial time via Gaussian elimination", "Otherwise, Gaussian elimination will yield
a row echelon form; by setting one of the non-pivots yj to be an arbitrary number …".

Input: a list `rows` of vectors `r : Fin m → ℚ`, read as the homogeneous system `r · d = 0`
(one equation per row). The procedure is Gauss–Jordan elimination with every rational operation
ticked:

1. Copy the rows into lists of rationals (charging `bitSize + 1` per entry).
2. Scan the columns `c = 0, …, m - 1` (one tick each). In column `c`, look for the first
   remaining (not yet used as pivot) row whose entry in column `c` is nonzero (`qeq` test, one
   tick per row inspected). If there is none, `c` is a free column. Otherwise divide that row by
   its entry in column `c` (`qdiv`), and subtract from every other row (the earlier pivot rows
   and the remaining rows) its entry in column `c` times the scaled row (`qmul`, `qsub`, one
   tick per entry). The scaled row becomes the pivot row of column `c`.
3. At the end the pivot rows form the reduced row echelon form of the system. If every column is
   a pivot column, return `none`: `d = 0` is the only solution.
4. Otherwise let `f` be the lowest free column and return `some d` with `d f = 1`, `d c = 0`
   for every other free column `c`, and `d p = -R[p, f]` for every pivot column `p`, where
   `R[p, f]` is the entry in column `f` of the pivot row of column `p` (negation computed as
   `qsub 0`). This `d` solves the system and `d f = 1`.

**Formalization Note.** Footnote 5 leaves the non-pivot value "arbitrary"; the mission fixes it to
the canonical kernel vector above (Reading 3). Rows are copied, so the result depends only on the
values of the input functions. The helper `findPivot` returns the pivot row and the other
remaining rows in their original order; `elim c p r` replaces `r` by `r - r[c] • p`. -/
def kernelDir {m : ℕ} (rows : List (Fin m → ℚ)) : StateM ℕ (Option (Fin m → ℚ)) := do
  let mat ← rows.mapM fun r => (List.finRange m).mapM fun c => do
    tick (bitSize (r c) + 1)
    pure (r c)
  let st ← (List.finRange m).foldlM
    (fun (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) => do
      tick 1
      match ← findPivot c.val st.2 with
      | none => pure st
      | some (p, rest) =>
        let pc := p.getD c.val 0
        let p' ← p.mapM fun a => do
          tick 1
          qdiv a pc
        let piv' ← st.1.mapM fun (q, r) => do
          let r' ← elim c.val p' r
          pure (q, r')
        let rest' ← rest.mapM fun r => elim c.val p' r
        pure (piv' ++ [(c, p')], rest'))
    ([], mat)
  let piv := st.1
  tick (m + 1)
  match (List.finRange m).find? (fun c => !(piv.any fun pr => pr.1 == c)) with
  | none => pure none
  | some f =>
    let d ← (List.finRange m).mapM fun c => do
      tick 1
      if c = f then pure 1
      else
        match piv.find? (fun pr => pr.1 == c) with
        | some (_, r) => qsub 0 (r.getD f.val 0)
        | none => pure 0
    pure (some fun c => d.getD c.val 0)
where
  /-- First row of `rs` whose entry in column `c` is nonzero, with the other rows in order. -/
  findPivot (c : ℕ) : List (List ℚ) → StateM ℕ (Option (List ℚ × List (List ℚ)))
    | [] => pure none
    | r :: rs => do
      tick 1
      let z ← qeq (r.getD c 0) 0
      if z then
        match ← findPivot c rs with
        | none => pure none
        | some (p, rest) => pure (some (p, r :: rest))
      else pure (some (r, rs))
  /-- `elim c p r = r - r[c] • p`, entrywise with ticked arithmetic. -/
  elim (c : ℕ) (p r : List ℚ) : StateM ℕ (List ℚ) :=
    (List.zip r p).mapM fun (a, b) => do
      tick 1
      let t ← qmul (r.getD c 0) b
      qsub a t

end ConsensusHalvingItems.Additive


