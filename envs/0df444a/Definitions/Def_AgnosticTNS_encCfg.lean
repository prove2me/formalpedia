-- Prove2me | Definitions.Def_AgnosticTNS_encCfg
-- name    : AgnosticTNS_encCfg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:53.783916+00:00
-- url     : https://prove2.me/theorems/f2cc1f2f-9dad-4788-89a9-577689bb8f2a
-- title:
--   Qudit labels on qubits
-- statement:
--   Following Eq. (3.68), each qudit label $x_v\in\{0,\dots,d-1\}$ is written in binary (least significant bit first) on the $\lceil\log_2 d\rceil$ qubits of block $v$, so $n$ qudits occupy $n\lceil\log_2 d\rceil$ qubits. The encoding is injective (proved sanity check).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (3.68), p.26

import Mathlib
import Definitions.Def_AgnosticTNS_bitsBlocks

namespace AgnosticTNS

/-- **Encoding `n` qudits on qubits**, Eq. (3.68), p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): "reversibly encode the
computational-basis labels … on `⌈log₂ D⌉` qubits". Qudit `v` with label `x_v ∈ {0, …, d − 1}` is
written in binary (least significant bit first) on the `⌈log₂ d⌉ = Nat.clog 2 d` qubits of block `v`. -/
def encCfg (n d : ℕ) (x : Fin n → Fin d) : QAlgorithms.Complexity.Bits (n * Nat.clog 2 d) :=
  (bitsBlocks n (Nat.clog 2 d)).symm fun v k => (x v : ℕ).testBit k

end AgnosticTNS


