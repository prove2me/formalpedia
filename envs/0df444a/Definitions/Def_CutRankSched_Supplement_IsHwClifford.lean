-- Prove2me | Definitions.Def_CutRankSched_Supplement_IsHwClifford
-- name    : CutRankSched_Supplement_IsHwClifford
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:41:55.977915+00:00
-- url     : https://prove2.me/theorems/3d2eafaf-bbf3-4ad5-9e23-e2d6656374b4
-- title:
--   Clifford gates implementable on the hardware graph $H$
-- statement:
--   Under the local Clifford hardware interface (Assumption 4.4), a Clifford gate is **implementable on the hardware graph** $H=(Q,E_H)$ if it is a single-qubit generator $H_q$ or $S_q$ on any qubit, or a $\mathrm{CNOT}_{a,b}$ along a hardware edge $\{a,b\}\in E_H$.
--
--   These gates generate, up to global phase, all single-qubit Clifford gates and the adjacent SWAP and CNOT operations of Assumption 4.4. Clifford gates carry no cost in the round objective.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Assumption 4.4, p.7

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Supplement_Gate

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- A Clifford gate **implementable on the hardware graph** `H` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Assumption 4.4, p.7):
a single-qubit Clifford generator `H_q` or `S_q` on any qubit, or `CNOT_{a,b}` along a hardware
edge `{a, b} ∈ E_H`.

**Formalization Note** `{H, S, CNOT on edges}` generates, up to global phase, all single-qubit
Cliffords and the adjacent SWAP/CNOT gates of Assumption 4.4. -/
def IsHwClifford {m : ℕ} (H : SimpleGraph (Fin m)) : Gate m → Prop
  | .H _ => True
  | .S _ => True
  | .CNOT a b _ => H.Adj a b
  | .T _ => False
  | .Tdg _ => False

end Supplement

end CutRankSched


