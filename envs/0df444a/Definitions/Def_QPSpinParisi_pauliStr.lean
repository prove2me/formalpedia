-- Prove2me | Definitions.Def_QPSpinParisi_pauliStr
-- name    : QPSpinParisi_pauliStr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:52.146004+00:00
-- url     : https://prove2.me/theorems/652adabf-b236-4cbd-a6d4-425f10eeb7cd
-- title:
--   The Pauli string $P^{\bar a}_{\bar i}$
-- statement:
--   For an index $(\bar i,\bar a)$, the Pauli string on $n$ qubits is
--   $$P^{\bar a}_{\bar i}=\prod_{j=1}^p\sigma^{a_j}_{i_j},$$
--   where $\sigma^a_i$ acts as $\sigma^a$ on qubit $i$ and as the identity on the other qubits.
--
--   **Formalization Note** The matrix entry at bit strings $(x,y)$ is written as the product over sites of the single-site entries, the entry of the tensor product.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_Idx
import Definitions.Def_CollectiveDFS_pauli

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Pauli string `P^ā_ī = ∏_j σ^{a_j}_{i_j}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3): the Pauli `σ^{a_j}` on each
site of the tuple and the identity on every other site.

**Formalization Note** The matrix entry at `(x, y)` is the product over sites of the single-site entries. This is
the entry of the tensor product. `σ^a` is the published `CollectiveDFS.pauli` (`Fin 3` index `0, 1, 2` for
`σ¹, σ², σ³`; `false : Bool` is `|0⟩`), the matrices of p.3. -/
def pauliStr {n : ℕ} (i : Idx n) : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ :=
  Matrix.of fun x y => ∏ j : Fin n,
    if h : j ∈ i.1.1 then CollectiveDFS.pauli (i.2 ⟨j, h⟩) (x j) (y j) else if x j = y j then 1 else 0

end QPSpinParisi


