-- Prove2me | Definitions.Def_DepthOneQExp_Supplement_IsRingLocalLayer
-- name    : DepthOneQExp_Supplement_IsRingLocalLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:34:31.50391+00:00
-- url     : https://prove2.me/theorems/e38656cd-d5d4-4da3-9162-b328b9b690f7
-- title:
--   Depth-1 layer of range $r$ on a ring of $n$ qubits
-- statement:
--   Arrange $n$ qubits $0, 1, \dots, n-1$ on a ring, and let the cyclic distance of qubits $i, j$ be
--   $$
--   d_n(i,j) = \min\bigl(|i-j|,\ n-|i-j|\bigr).
--   $$
--   A list $L$ of placed gates is a **depth-1 layer of range $r$ over the gate set $G$** when
--
--   1. $L$ is a depth-one layer over $G$: it is non-empty, every gate is from $G$, and the gates act on pairwise disjoint sets of qubits; and
--   2. any two qubits acted on by the same gate are at cyclic distance at most $r$.
--
--   This makes precise the paper's "depth-1 1D circuit". The paper's expanders live on a 1D ring of qubits ("the expander is defined on a 1D ring so that some of the CNOT gates will have support on qubits 1 and $n$", §4, p.27), and their generators are "constant-range" (p.2).
--
--   **Formalization Note** Condition 1 is the published `MITMSynthesis.IsLayer`. The range $r$ is a parameter here. Requiring it to be independent of $n$ ("1D", constant range) is done in the theorems that use the predicate.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.17, p.15 ("depth-1 1D Clifford circuit"); §4, p.27 (1D ring); p.2 ("constant-range generators")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet

namespace DepthOneQExp.Supplement

/-- **A depth-1 1D layer of range `r` on a ring of `n` qubits** (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.17, p.15:
"depth-1 1D Clifford circuit"; §4, p.27: "the expander is defined on a 1D ring so that some of the
CNOT gates will have support on qubits 1 and n"; Theorem 1.2's context, p.2: "constant-range
generators"): `L` is a depth-one layer over the gate set `G` (a non-empty list of gates from `G` on
pairwise disjoint qubits, `MITMSynthesis.IsLayer`), and any two qubits acted on by the same gate are
at cyclic distance at most `r` on the ring `0, 1, …, n − 1, 0`.

**Formalization Note** The cyclic distance of qubits `i, j < n` is `min(|i − j|, n − |i − j|)`.
"1D" is read as geometric locality on a ring with a range `r` that is fixed independently of `n`
(that uniformity is imposed where the predicate is used). -/
def IsRingLocalLayer (n r : ℕ) (G : Set MITMSynthesis.Gate)
    (L : List (MITMSynthesis.Placement n)) : Prop :=
  MITMSynthesis.IsLayer G L ∧
    ∀ p ∈ L, ∀ a b : Fin p.gate.arity,
      min (Int.natAbs ((p.qubits a : ℤ) - (p.qubits b : ℤ)))
        (n - Int.natAbs ((p.qubits a : ℤ) - (p.qubits b : ℤ))) ≤ r

end DepthOneQExp.Supplement


