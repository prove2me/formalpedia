-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Supplement_ComputesOR
-- name    : SubsetSumPartialMatch_SubsetSum_Supplement_ComputesOR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:14:16.986517+00:00
-- url     : https://prove2.me/theorems/29e68fe9-7bdc-4c6b-810e-1a8d7357650e
-- title:
--   Section 3.1 — OR computation by a depth-2 circuit
-- statement:
--   Let $I,J$ be the input and output index sets of an integer circuit $C=(L_C,R_C)$ with an arbitrary finite middle set. The predicate $\operatorname{ComputesOR}(C,M)$ requires that $M$, $L_C$ and $R_C$ have entries in $\{0,1\}$ and that
--   $$
--   (L_C R_C)_{x,y}\ne0\quad\Longleftrightarrow\quad M_{x,y}=1
--   \qquad(x\in I,\ y\in J).
--   $$
--   The product is over the integers. Overlapping paths through distinct middle gates are permitted, so a positive product entry may exceed one. The predicate adds the OR row of the source's circuit-model table to the published circuit container, without imposing degree bounds. It is reusable for any binary matrix.
--
--   **Formalization Note** The index types can be empty. The published circuit container supplies the finite middle type. Source degree functions are reused unchanged, and no target conclusion is part of the definition.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 15, Section 3.1, circuit-model table (OR row); applied on p. 27, Section 3.5.

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum.Supplement

/-- The OR row of the circuit-model table in §3.1 (p. 15): the matrix and both edge
matrices have 0/1 entries, and the integer product has exactly the support of the matrix.
In particular, distinct middle gates may cover the same 1-entry. -/
def ComputesOR {I J : Type} (C : LinCircuit I J) (M : Matrix I J ℤ) : Prop :=
  (∀ x y, M x y = 0 ∨ M x y = 1) ∧
  (∀ x e, C.L x e = 0 ∨ C.L x e = 1) ∧
  (∀ e y, C.R e y = 0 ∨ C.R e y = 1) ∧
  ∀ x y, (C.L * C.R) x y ≠ 0 ↔ M x y = 1

end SubsetSumPartialMatch.SubsetSum.Supplement


