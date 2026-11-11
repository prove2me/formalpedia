-- Prove2me | Definitions.Def_PosIndexNash_PPADS_ShapleyIndex
-- name    : PosIndexNash_PPADS_ShapleyIndex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:35.172692+00:00
-- url     : https://prove2.me/theorems/03c6403b-c31a-4377-b312-5a05717c8e19
-- title:
--   Bordered determinant Δ(C) and the Shapley index of an equilibrium (eq. (1), Definition 2.3)
-- statement:
--   For a square matrix $C \in \mathbb{R}^{k\times k}$ the **bordered determinant** is
--   $$\Delta(C) := \det\begin{pmatrix} C & -\mathbf 1 \\ \mathbf 1^\top & 0\end{pmatrix}.$$
--   For a pair of mixed strategies $(x, y)$ of the game $(A, B)$ with supports $I = \mathrm{supp}(x)$ and $J = \mathrm{supp}(y)$ of a common size $k$, the **Shapley index** is
--   $$\mathrm{ind}_{A,B}(x, y) := (-1)^{k+1}\,\mathrm{sign}\big(\Delta(A_{I,J})\,\Delta((B_{I,J})^\top)\big),$$
--   where restriction precedes transposition: $(B_{I,J})^\top$ is the transpose of the $I\times J$ submatrix of $B$. At an equilibrium of a nondegenerate game both bordered determinants are nonzero and the index is $\pm 1$; a pure equilibrium has $\Delta = 1$ for both factors and index $+1$.
--
--   **Formalization Note** The index is an integer defined for every pair $(x,y)$. Both supports are listed in increasing order (`Finset.orderEmbOfFin`); the paper notes that the index does not depend on the ordering. When $|I| \ne |J|$ the value is the junk value $0$, and $\mathrm{sign}(0) = 0$; so the value is $\pm1$ exactly when both bordered determinants are nonzero. The bordered matrix is `Matrix.fromBlocks` on `Fin k ⊕ Fin 1`, the border index last.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 12, eq. (1) and Definition 2.3, eq. (3)

import Mathlib
import Definitions.Def_QuasiStrictNE_supp

namespace PosIndexNash.PPADS

/-- **Bordered determinant** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash
Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 12, eq. (1)).

For `C ∈ ℝ^{k×k}`, `Δ(C) := det (C, −1; 1ᵀ, 0)`: the `(k+1) × (k+1)` matrix whose top-left block
is `C`, whose last column is `−1` above a `0`, and whose last row is `1ᵀ` followed by `0`.

**Formalization Note** The bordered matrix is `Matrix.fromBlocks` on the index type
`Fin k ⊕ Fin 1` (the border index last). -/
noncomputable def borderedDet {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (Matrix.fromBlocks C (Matrix.of fun _ _ => (-1 : ℝ)) (Matrix.of fun _ _ => (1 : ℝ))
    (0 : Matrix (Fin 1) (Fin 1) ℝ)).det

/-- **Shapley index of an equilibrium** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive
Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 12, Definition 2.3, eq. (3)).

For a pair of mixed strategies `(x, y)` of the game `(A, B)` with supports `I = supp(x)`,
`J = supp(y)` of the same size `k`,
`ind_{A,B}(x, y) := (−1)^{k+1} · sign(Δ(A_{I,J}) · Δ((B_{I,J})ᵀ))`, where restriction precedes
transposition (`(B_{I,J})ᵀ` is the transpose of the `I × J` submatrix of `B`).

**Formalization Note** The index is an integer for every pair `(x, y)`. Both supports are
enumerated in increasing order (`Finset.orderEmbOfFin`); the paper notes the index does not depend
on the ordering. When `|I| ≠ |J|` the value is the junk value `0`, and `sign 0 = 0`, so the value
lies in `{−1, +1}` exactly when the two bordered determinants are nonzero, which holds at every
equilibrium of a nondegenerate game (p. 12). -/
noncomputable def shapleyIndex {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : ℤ :=
  if h : (QuasiStrictNE.supp y).card = (QuasiStrictNE.supp x).card then
    let eI := (QuasiStrictNE.supp x).orderEmbOfFin rfl
    let eJ := (QuasiStrictNE.supp y).orderEmbOfFin h
    (-1) ^ ((QuasiStrictNE.supp x).card + 1) *
      ((SignType.sign (borderedDet (A.submatrix eI eJ) *
        borderedDet (B.submatrix eI eJ).transpose) : SignType) : ℤ)
  else 0

end PosIndexNash.PPADS


