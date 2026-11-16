-- Prove2me | Definitions.Def_GeoQAC_Supplement_cutRank
-- name    : GeoQAC_Supplement_cutRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:52.515142+00:00
-- url     : https://prove2.me/theorems/76114d46-1de1-4d1f-9a85-c89fccd3c61c
-- title:
--   Schmidt rank across a column cut; product vectors
-- statement:
--   Regard each column of the grid $[w]\times[h]$ as one subsystem. For $0<j<h$ the **column cut** $j$ separates the columns $<j$ from the columns $\ge j$. The **Schmidt rank** of a vector $\psi$ across this cut is the least number of product vectors (left $\otimes$ right) summing to $\psi$, which equals the rank of its coefficient matrix: rows indexed by configurations of the left columns, columns by configurations of the right columns, entries the amplitudes of the joined configurations. A **product vector** is $\bigotimes_v\varphi_v$, with amplitude $\prod_v\varphi_v(y_v)$ at $y$.
--
--   The minimal columnwise MPS bond dimension at a cut equals the Schmidt rank across it, which is how Theorem A.1 bounds bond dimensions.
--
--   **Formalization Note** The Schmidt rank is the matrix rank over $\mathbb C$ of the coefficient matrix.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Appendix A, p.37; §2.2, p.10

import Mathlib
import Definitions.Def_GeoQAC_Pos

namespace GeoQAC.Supplement

open GeoQAC

/-!
# Schmidt rank across a column cut, and product vectors

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Appendix A, p.37: "Regard each column of
`[w] × [h]` as one subsystem of dimension `2^w`, ordered from left to right. … the bond dimension is
at most `χ` when all `r_j ≤ χ`. We use the standard characterization: the minimal bond dimension at
each cut equals the Schmidt rank across that cut [Vid03]." §2.2, p.10: "The Schmidt rank of a pure
state across a bipartition is the least number of product vectors whose sum equals the state."

**Formalization Note.**
* The cut `j` (`0 < j < h`) separates the columns `< j` from the columns `≥ j`. The Schmidt rank
  across it is the rank of the coefficient matrix whose rows are configurations of the left
  columns, whose columns are configurations of the right columns, and whose entries are the
  amplitudes of the joined configuration. "Columnwise MPS bond dimension at most `χ`" is "every
  cut rank is at most `χ`", by the characterization the paper uses.
* `prodVec φ = ⊗_v φ_v` is the product of one-qubit vectors `φ_v : Bool → ℂ`.
-/

/-- The qubits in the columns `< j`. -/
abbrev LeftOf {w h : ℕ} (j : ℕ) : Type := {v : Pos w h // v.2.val < j}

/-- The qubits in the columns `≥ j`. -/
abbrev RightOf {w h : ℕ} (j : ℕ) : Type := {v : Pos w h // ¬ v.2.val < j}

/-- The configuration of the whole grid with `a` on the columns `< j` and `b` on the others. -/
def joinCut {w h : ℕ} (j : ℕ) (a : LeftOf (w := w) (h := h) j → Bool)
    (b : RightOf (w := w) (h := h) j → Bool) : Pos w h → Bool :=
  fun v => if hv : v.2.val < j then a ⟨v, hv⟩ else b ⟨v, hv⟩

/-- The Schmidt rank of `ψ` across the cut between columns `j − 1` and `j` (Appendix A, p.37; §2.2,
p.10): the rank of its coefficient matrix with respect to the bipartition columns `< j` | `≥ j`. -/
noncomputable def cutRank {w h : ℕ} (ψ : (Pos w h → Bool) → ℂ) (j : ℕ) : ℕ :=
  (Matrix.of fun (a : LeftOf (w := w) (h := h) j → Bool) (b : RightOf (w := w) (h := h) j → Bool) =>
    ψ (joinCut j a b)).rank

/-- The product vector `⊗_v φ_v`: its amplitude at `y` is `∏_v φ_v(y_v)`. -/
noncomputable def prodVec {V : Type} [Fintype V] (φ : V → Bool → ℂ) : (V → Bool) → ℂ :=
  fun y => ∏ v, φ v (y v)

end GeoQAC.Supplement


