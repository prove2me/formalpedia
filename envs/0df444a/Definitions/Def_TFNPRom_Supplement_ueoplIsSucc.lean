-- Prove2me | Definitions.Def_TFNPRom_Supplement_ueoplIsSucc
-- name    : TFNPRom_Supplement_ueoplIsSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:25:09.176175+00:00
-- url     : https://prove2.me/theorems/194d9996-4d08-4f60-b2eb-ea8df01dd102
-- title:
--   Successor of a grid node
-- statement:
--   In a grid instance on $[N]\times[N]$, a successor value $\mathrm{Succ}_v=k\neq\bot$ of a node $v=(i,j)$ with $i<N$ names the node $(i+1,k)$ on the next row, which is called the **successor** of $v$. A node of the last row has no successor.
--
--   Proper sinks and proper sources of UEoPL are defined through this relation.
--
--   **Formalization Note** 0-based `Fin N`; $\bot$ is `none`.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, p.20; App. A, p.41

import Mathlib

namespace TFNPRom.Supplement

/-- The successor of a node in a grid instance (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, p.20: "the successor
`Succ_v = k ≠ ⊥` of a node `v = (i, j)` with `i < N` is interpreted as naming the node `(i + 1, k)` on
the next row, and we also call this node the successor of `v`"; App. A, p.41). `ueoplIsSucc N succ v w`
says that `w` is the successor of `v`.

**Formalization Note** 0-based `Fin N`; `⊥` is `none`. A node of the last row has no successor. -/
def ueoplIsSucc (N : ℕ) (succ : Fin N → Fin N → Option (Fin N)) (v w : Fin N × Fin N) : Prop :=
  v.1.val + 1 < N ∧ w.1.val = v.1.val + 1 ∧ succ v.1 v.2 = some w.2

end TFNPRom.Supplement


