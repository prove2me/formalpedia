-- Prove2me | Definitions.Def_DetConnSketch_Main_SketchMatrices
-- name    : DetConnSketch_Main_SketchMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:23.786961+00:00
-- url     : https://prove2.me/theorems/0a138652-75c4-466e-bd14-ef10fa62b193
-- title:
--   Adjacency matrices, nonzero counts and vertex covers of a matrix support (§4)
-- statement:
--   For a graph $G$ on $V$, its **adjacency matrix** $A_G$ has entry $1$ at $(i,j)$ when $ij$ is an edge and $0$ otherwise; its entries are read in a ring $R$ (the integers for the sign sketch $A_G X$, a finite field $\mathbb F_q$ for the sketch $A_G P$).
--
--   For a square matrix $M$ indexed by $\{0,\dots,s-1\}$: $\mathrm{nnz}(M)$ is the number of nonzero entries, $\mathrm{nnz}_{>}(M)$ the number of nonzero entries strictly above the diagonal ($i<j$), and $\mathrm{row}_i(M)$, $\mathrm{col}_j(M)$ the numbers of nonzero entries in row $i$ and column $j$.
--
--   The **support** $\mathrm{Supp}(M)$ is the graph whose edges are the positions $(i,j)$ with $M_{ij} \ne 0$. A set $U$ is a **vertex cover** of $\mathrm{Supp}(M)$ when every such position has $i \in U$ or $j \in U$.
--
--   **Formalization Note.** `adjMat R G`, `nnz`, `nnzAboveDiag`, `rowNnz`, `colNnz` and `IsSupportVertexCover M U`; the counts are on `Matrix (Fin s) (Fin s) R`.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 23–28 (PDF 27–32), Lemmas 4.2, 4.4 and Claims 4.7, 4.8

import Mathlib

namespace DetConnSketch.Main

/-!
# Adjacency matrices, nonzero counts and vertex covers of a matrix support (§4)

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 23–28 (Lemmas 4.2, 4.4, Claims 4.7, 4.8).

* `adjMat R G` is the `0/1` adjacency matrix `A_G` of `G`, with entries in a ring `R`
  (`R = ℤ` for the sign sketch `A_G X`, `R = F_q` for the field sketch `A_G P`).
* For a square matrix `M`, `nnz M` counts its nonzero entries, `nnzAboveDiag M` those strictly
  above the diagonal (`i < j`), `rowNnz M i` and `colNnz M j` those in row `i` and column `j`.
* `IsSupportVertexCover M U`: `U` is a vertex cover of `Supp(M)`, the graph whose edges are the
  positions `(i, j)` with `M i j ≠ 0`; every such position has `i ∈ U` or `j ∈ U`.
-/

open Classical in
/-- The adjacency matrix `A_G` of `G`, with entries `1` on edges and `0` elsewhere, in `R`. -/
noncomputable def adjMat {V : Type} (R : Type) [Zero R] [One R] (G : SimpleGraph V) :
    Matrix V V R :=
  fun i j => if G.Adj i j then 1 else 0

open Classical in
/-- The number of nonzero entries of `M`. -/
noncomputable def nnz {s : ℕ} {R : Type} [Zero R] (M : Matrix (Fin s) (Fin s) R) : ℕ :=
  (Finset.univ.filter fun p : Fin s × Fin s => M p.1 p.2 ≠ 0).card

open Classical in
/-- The number of nonzero entries of `M` strictly above the diagonal. -/
noncomputable def nnzAboveDiag {s : ℕ} {R : Type} [Zero R] (M : Matrix (Fin s) (Fin s) R) :
    ℕ :=
  (Finset.univ.filter fun p : Fin s × Fin s => p.1 < p.2 ∧ M p.1 p.2 ≠ 0).card

open Classical in
/-- The number of nonzero entries in row `i` of `M`. -/
noncomputable def rowNnz {s : ℕ} {R : Type} [Zero R] (M : Matrix (Fin s) (Fin s) R)
    (i : Fin s) : ℕ :=
  (Finset.univ.filter fun j : Fin s => M i j ≠ 0).card

open Classical in
/-- The number of nonzero entries in column `j` of `M`. -/
noncomputable def colNnz {s : ℕ} {R : Type} [Zero R] (M : Matrix (Fin s) (Fin s) R)
    (j : Fin s) : ℕ :=
  (Finset.univ.filter fun i : Fin s => M i j ≠ 0).card

/-- `U` is a vertex cover of `Supp(M)`: every nonzero position `(i, j)` of `M` has an endpoint
in `U`. -/
def IsSupportVertexCover {ι R : Type} [Zero R] (M : Matrix ι ι R) (U : Finset ι) : Prop :=
  ∀ i j, M i j ≠ 0 → i ∈ U ∨ j ∈ U

end DetConnSketch.Main


