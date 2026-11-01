-- Prove2me | Definitions.Def_AllPhotonicRepeater_treeSize
-- name    : AllPhotonicRepeater_treeSize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:34.198123+00:00
-- url     : https://prove2.me/theorems/4078d49a-145a-443a-8fca-2aae5f04db9e
-- title:
--   Number of qubits $Q_L$ of a tree cluster state
-- statement:
--   For a tree cluster state with branching parameters $b_0,\dots,b_l$, the number of qubits is
--   $$
--   Q_L=\sum_{j=0}^{l}\prod_{i=0}^{j}b_i ,
--   $$
--   the $j$th summand being the number of qubits in level $j+1$ of the tree. For example $b_0=b_1=2$ (Fig. 4 of the paper) gives $Q_L=6$, and $\{b_0,b_1,b_2\}=\{16,14,1\}$ gives $Q_L=464$.
--
--   $Q_L+1$ photons are spent per 1st-leaf qubit in the photon count (C4).
--
--   **Formalization Note** A natural number; only $b_0,\dots,b_l$ are read.
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A1, Eq. (A1), p. 7

import Mathlib

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The number `Q_L` of qubits in a tree cluster state with branching parameters
`b 0, …, b l` (Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. A1,
Eq. (A1), p. 7):

`Q_L = Σ_{j=0}^{l} Π_{i=0}^{j} b_i`.

**Formalization Note** A natural number; only `b 0, …, b l` are read. -/
def treeSize (l : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (l + 1), ∏ i ∈ Finset.range (j + 1), b i

end AllPhotonicRepeater


