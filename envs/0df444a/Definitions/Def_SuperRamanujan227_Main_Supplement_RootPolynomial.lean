-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Supplement_RootPolynomial
-- name    : SuperRamanujan227_Main_Supplement_RootPolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:42:40.253213+00:00
-- url     : https://prove2.me/theorems/d65ccde1-b979-4971-9a58-f8367dbfc1d9
-- title:
--   Root characteristic polynomial from independent uniform bipartite matchings
-- statement:
--   For even $n=2m$ and a natural number $d$, choose $d$ independent uniform pairs of $m\times m$ permutation matrices $(P_i,S_i)$. Write $B=\sum_{i=1}^d P_iS_i^{\mathsf T}$. The root characteristic polynomial is the genuine coefficientwise finite average
--
--   $$
--   p_\varnothing(x)=\mathbb E\det\!\left(xI-\begin{pmatrix}0&B\\B^{\mathsf T}&0\end{pmatrix}\right).
--   $$
--
--   Both trivial roots $\pm d$ remain; the second ordered root is supplied by the published root-ordering definition. Each pair of permutations is averaged independently with weight equal to the inverse cardinality of the finite sample space. The block index type is the disjoint union of two copies of $\operatorname{Fin}(m)$. On odd $n$ this expression instead has order $2\lfloor n/2\rfloor$; theorems use only even $n$. This polynomial is defined independently of every spectral inequality.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 14, Definition 4.4

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra

namespace SuperRamanujan227.Main.Supplement

/-- Definition 4.4: coefficientwise average over d independent uniform pairs (P_i,S_i).
The characteristic polynomial of the symmetric block matrix retains both trivial roots ±d.
For odd n this uses 2*floor(n/2) vertices; all theorem uses require even n. -/
noncomputable def rootCharacteristic (n d : ℕ) : Polynomial ℝ := by
  let Ω := Fin d → (Equiv.Perm (Fin (n / 2)) × Equiv.Perm (Fin (n / 2)))
  exact ((Fintype.card Ω : ℝ)⁻¹) • ∑ ω : Ω,
    let B : Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
      ∑ i : Fin d, permMat (ω i).1 * (permMat (ω i).2).transpose
    (Matrix.fromBlocks 0 B B.transpose 0).charpoly

end SuperRamanujan227.Main.Supplement


