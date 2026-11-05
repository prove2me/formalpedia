-- Prove2me | Definitions.Def_BaconOQEC_weight
-- name    : BaconOQEC_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:36.914074+00:00
-- url     : https://prove2.me/theorems/c43123f6-0dc7-49bf-be20-02ed83fa8d86
-- title:
--   Weight of $P(a,b)$
-- statement:
--   The **weight** of the Pauli operator $P(a,b)$ is the number of lattice sites on which it acts nontrivially,
--
--   $$
--   \mathrm{wt}(a,b) = \#\{(i,j) : a_{i,j}\ne 0 \text{ or } b_{i,j}\ne 0\}.
--   $$
--
--   It is the quantity behind the paper's "distance $n$" and "single qubit errors" (p.8), and it does not depend on the phase of the operator.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, p.8

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, p.8 ("has a distance n"; "arbitrary single qubit errors"): the
weight of the Pauli operator `P(a, b)`, the number of lattice sites on which it acts
nontrivially, `#{(i, j) : a_{i,j} ≠ 0 or b_{i,j} ≠ 0}`.

**Formalization Note.** The paper uses the weight (number of qubits an error acts on) without a
symbol. It does not depend on the phase of the Pauli operator. Sites are pairs of 0-based indices
in `Fin (m + 1)`, `n = m + 1`. -/
def weight {m : ℕ} (a b : Bits m) : ℕ :=
  (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => a p.1 p.2 ≠ 0 ∨ b p.1 p.2 ≠ 0).card

end BaconOQEC


