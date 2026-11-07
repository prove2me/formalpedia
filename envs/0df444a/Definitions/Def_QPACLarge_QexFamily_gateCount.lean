-- Prove2me | Definitions.Def_QPACLarge_QexFamily_gateCount
-- name    : QPACLarge_QexFamily_gateCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:59.855126+00:00
-- url     : https://prove2.me/theorems/36041380-1b04-45e2-9bb7-e52f36173a32
-- title:
--   Gate count of a quantum learner
-- statement:
--   The **gate count** of the learner at index $i$ is the total number of gates of its circuit, summed over all layers. The paper's "each circuit $Q_n$ contains at most $T(n)$ gates" bounds this number.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16

import Mathlib
import Definitions.Def_QPACLarge_QexFamily

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **The number of gates of a quantum learner at an index.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16: "each circuit `Qₙ` contains at most `T(n)` gates".

The total number of instructions over all layers of the circuit at index `i`. -/
def QexFamily.gateCount {ι : Type} {dim : ι → ℕ} (L : QexFamily ι dim) (i : ι) : ℕ :=
  ((L.circ i).map List.length).sum

end QPACLarge


