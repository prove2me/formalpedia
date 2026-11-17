-- Prove2me | Definitions.Def_CutRankSched_Supplement_HwCircuit
-- name    : CutRankSched_Supplement_HwCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:42:29.923229+00:00
-- url     : https://prove2.me/theorems/bec18fde-7a77-4bd6-a5cf-8cc1b19cb706
-- title:
--   Hardware circuits and their number of non-Clifford rounds
-- statement:
--   A **hardware circuit** is a list of physical rounds followed by a final Clifford block. Each round is a Clifford block followed by one parallel layer of single-qubit $T$ or $T^\dagger$ gates. It **respects** the hardware graph $H$ if every Clifford gate is implementable on $H$ and each non-Clifford layer acts on pairwise distinct qubits.
--
--   Its gates are executed in order: round $1$ (Clifford block, then its layer), round $2$, and so on, then the final block. Its **number of non-Clifford rounds** is the number of rounds whose layer is nonempty; Clifford operations are not counted (Definition 3.1).
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Definition 3.1, p.4, and Section 4.2, p.7

import Mathlib
import Definitions.Def_CutRankSched_Supplement_Gate
import Definitions.Def_CutRankSched_Supplement_IsHwClifford

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- A **hardware circuit** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Definition 3.1, p.4, and §4.2, p.7): a list of physical rounds,
each a Clifford block followed by one parallel layer of single-qubit `T` (`true`) / `T†` (`false`)
gates, and a final Clifford block. -/
structure HwCircuit (m : ℕ) where
  /-- the rounds: (Clifford block, non-Clifford layer) -/
  rounds : List (List (Gate m) × List (Fin m × Bool))
  /-- the final Clifford block -/
  final : List (Gate m)

/-- The circuit respects the hardware graph `H` (Assumption 4.4, p.7): every Clifford gate is
implementable on `H`, and every non-Clifford layer acts on pairwise distinct qubits. -/
def HwCircuit.OnHardware {m : ℕ} (H : SimpleGraph (Fin m)) (c : HwCircuit m) : Prop :=
  (∀ g ∈ c.final, IsHwClifford H g) ∧
    ∀ r ∈ c.rounds, (∀ g ∈ r.1, IsHwClifford H g) ∧ (r.2.map Prod.fst).Nodup

/-- The gate list of a hardware circuit, in execution order (first gate acts first). -/
def HwCircuit.gates {m : ℕ} (c : HwCircuit m) : List (Gate m) :=
  c.rounds.flatMap (fun r => r.1 ++ r.2.map fun e => if e.2 then Gate.T e.1 else Gate.Tdg e.1) ++
    c.final

/-- The number of non-Clifford rounds: the rounds with a nonempty non-Clifford layer
(Definition 3.1, p.4: Clifford operations have zero cost). -/
def HwCircuit.roundCount {m : ℕ} (c : HwCircuit m) : ℕ :=
  (c.rounds.filter fun r => !r.2.isEmpty).length

end Supplement

end CutRankSched


