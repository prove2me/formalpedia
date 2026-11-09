-- Prove2me | Definitions.Def_SublinearPauli_Fidelity_NoisyChannel
-- name    : SublinearPauli_Fidelity_NoisyChannel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:42:28.174159+00:00
-- url     : https://prove2.me/theorems/422b97f6-04b3-4b3e-9116-b1f6e13bbde6
-- title:
--   Lemma 3, p.14 — the binary symmetric channel $\mathrm{BSC}_p^{\otimes 2}$ and the channel matrix $C$
-- statement:
--   For a real number $p$ the **binary symmetric channel** is the real matrix
--   $$\mathrm{BSC}_p=\begin{pmatrix}1-p&p\\p&1-p\end{pmatrix},$$
--   and $\mathrm{BSC}_p^{\otimes2}$ is its Kronecker square, indexed by two bits.
--
--   The **channel matrix** $C$ is indexed by the Pauli letters; in the row and column order $X,Y,Z,I$,
--   $$C=\begin{pmatrix}\tfrac34&0&0&\tfrac14\\0&\tfrac34&0&\tfrac14\\0&0&\tfrac34&\tfrac14\\\tfrac14&\tfrac14&\tfrac14&\tfrac14\end{pmatrix}.$$
--   It is $\tfrac34$ times the per-qubit weighted adjacency matrix of the Pauli graph.
--
--   To compare $C$ with $\mathrm{BSC}_p^{\otimes2}$, the letters are identified with two bits by $I=00$, $X=10$, $Z=01$, $Y=11$.
--
--   **Formalization Note** $C$ is defined by its entries ($\tfrac14$ in the $I$ row and column, $\tfrac34$ on the remaining diagonal, $0$ elsewhere), which is the displayed matrix in any order of the letters. The comparison in Lemma 3 does not depend on the bijection between letters and bit pairs: $\mathrm{BSC}_p^{\otimes 2}$ is invariant under bit translations and the swap of the two bits, $C$ under all permutations fixing $I$, and together these act transitively on the bijections.
--   The matrix entries reuse the published `QAlgorithms.Papers.Independent.Intakethird100.P74.bscProbability`, transporting Boolean indices to `Fin 2`.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, Lemma 3 p.14 (BSC_p, displayed matrix), proof of Theorem 3 p.14 (row/column order X, Y, Z, I), §7 p.17 (C)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace SublinearPauli.Fidelity

/-- The binary symmetric channel `BSC_p = [[1−p, p], [p, 1−p]]` (Lemma 3, p.14), for every real `p`,
reindexed from the published Boolean transition kernel (`0 ↦ false`, `1 ↦ true`). -/
noncomputable def bsc (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => QAlgorithms.Papers.Independent.Intakethird100.P74.bscProbability p
    (decide (a = 1)) (decide (b = 1))

/-- The two-bit product channel `BSC_p^{⊗2}`, indexed by `{0,1}²`. -/
noncomputable def bsc2 (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.kroneckerMap (· * ·) (bsc p) (bsc p)

/-- The single-qubit channel matrix `C` (Lemma 3, p.14; §7, p.17), which in the row/column order
`X, Y, Z, I` is `[[3/4,0,0,1/4],[0,3/4,0,1/4],[0,0,3/4,1/4],[1/4,1/4,1/4,1/4]]`:
`C_{L,L'} = 1/4` if `L = I` or `L' = I`, `3/4` if `L = L' ≠ I`, and `0` otherwise. -/
noncomputable def channelC : Matrix Letter Letter ℝ :=
  fun L L' => if L = Letter.I ∨ L' = Letter.I then 1 / 4 else if L = L' then 3 / 4 else 0

/-- `C` transported to the index set `{0,1}²` of `BSC_p^{⊗2}` through the bit-pair labeling
`Letter.ofBits` (`00 ↦ I`, `10 ↦ X`, `01 ↦ Z`, `11 ↦ Y`). -/
noncomputable def channelCBits : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  channelC.submatrix Letter.ofBits Letter.ofBits

end SublinearPauli.Fidelity


