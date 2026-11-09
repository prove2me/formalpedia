-- Prove2me | Definitions.Def_AgnosticTNS_bitsBlocks
-- name    : AgnosticTNS_bitsBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:34.40999+00:00
-- url     : https://prove2.me/theorems/2497a7e6-cafd-4234-bf25-9158e72e557b
-- title:
--   Splitting qubits into blocks
-- statement:
--   The $c\cdot q$ qubits $0,\dots,cq-1$ are split into $c$ consecutive blocks of $q$ qubits: wire $kq+t$ is qubit $t$ of block $k$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (3.68), p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace AgnosticTNS

/-- **Splitting `c·q` qubits into `c` blocks of `q` qubits**, for the qudit-on-qubit encoding of
Eq. (3.68), p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Wire `k·q + t` is qubit `t` of block `k` (`finProdFinEquiv`). -/
def bitsBlocks (c q : ℕ) : QAlgorithms.Complexity.Bits (c * q) ≃ (Fin c → QAlgorithms.Complexity.Bits q) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

end AgnosticTNS


