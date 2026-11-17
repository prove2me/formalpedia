-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_selectedRecords
-- name    : MonoidProdQ_Supplement_selectedRecords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:10:57.370391+00:00
-- url     : https://prove2.me/theorems/4e10d799-b8cb-40ba-8cbe-4ac2ae07f0be
-- title:
--   Selected records with their indices
-- statement:
--   For the canonical minimum-weight basis $B$ of the input records $x_1,\dots,x_n$, the output that lists the record $x_i$ at every selected position $i\in B$ and $\bot$ at every other position. It determines both the selected indices and their records, as in Theorem 33: "The same bound permits returning the selected records as well as their indices."
--
--   **Formalization Note** The output is a vector of optional records indexed by positions.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 33, p.44

import Definitions.Def_MonoidProdQ_Supplement_canonicalBasis

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 33, p.44: "The same bound permits
returning the selected records as well as their indices": the output that lists, at every
position `i` of the canonical minimum-weight basis (`canonicalBasis`), its record `xᵢ`, and `⊥`
(`none`) at every other position. It determines both the selected indices and their records. -/
noncomputable def selectedRecords {E : Type*} (M : Matroid E) (W : Finset ℝ) {n : ℕ}
    (x : Fin n → Option (E × W)) : Fin n → Option (E × W) := by
  classical
  exact fun i => if i ∈ canonicalBasis M W x then x i else none

end MonoidProdQ.Supplement


