-- Prove2me | Definitions.Def_CatalyticTreeEval_OracleContracts
-- name    : CatalyticTreeEval_OracleContracts
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:30:45.766406+00:00
-- url     : https://prove2.me/theorems/ef1ba304-b2da-46f8-98cc-3b4c9cd3e5d4
-- title:
--   Positional oracle operation contracts
-- statement:
--   A query boundary certifies a normalized local seam, a retained query packet, and canonical encoded registers. An operation span records the exact successful binary steps and all intermediate restrictions for one literal register operation. A schedule supplies reachable operation boundaries and strictly increasing cuts, enabling trace assembly against the published oracle execution semantics.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Lemma 3.19 and Section 4.2.

import Definitions.Def_CatalyticTreeEval_MachineContracts
import Definitions.Def_CatalyticTreeEval_Main_OracleMachine

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts

/-- The public call boundary of the positional oracle. The normalized local seam
implies the mission's suspension condition; the packet fits in retained work. -/
structure QueryBoundary {m d : ℕ} (P : Main.OracleMachine)
    (R : Main.Registers m d) (a : ZMod m) (ctrl : Bool) (σ : Fin 2)
    (retained : ℕ) (c : Config P.base) : Prop where
  querying : P.querying c = true
  seam : LocalSeam retained c
  packetFits : Main.width m + 2 ≤ retained
  query_eq : P.query c = (a, ctrl, σ)
  registers_eq : c.catalyst = Main.registerCode R
  /-- Supplied by the reusable encode/decode lemma for positive moduli. -/
  decoded_eq : Main.decodeRegisters m d c.catalyst = R

/-- The exact transient-write and query-placement condition in `Realizes`. -/
def OperationInvariant {m d : ℕ} (P : Main.OracleMachine)
    (start : Config P.base) (op : Main.RegisterOp m d) (time : ℕ) :
    ℕ → Config P.base → Prop :=
    fun t c => t < time →
      match op with
      | .query a ctrl σ =>
        (P.querying c = true ↔ t + 1 = time) ∧
        c.catalyst = start.catalyst ∧
        (P.querying c = true → P.query c = (a, ctrl, σ))
      | .target _ =>
        P.querying c = false ∧
        (∀ b, b < 2 * d * Main.width m →
          c.catalyst.getD b false = start.catalyst.getD b false)
      | .swap a b =>
        P.querying c = false ∧
        (∀ j : Fin 3, j ≠ a → j ≠ b → ∀ z, z < d * Main.width m →
          c.catalyst.getD (j.val * d * Main.width m + z) false =
            start.catalyst.getD (j.val * d * Main.width m + z) false)

/-- A literal elementary register-operation span, ready to be concatenated into
`Realizes`. A query occupies exactly the last transition; ordinary operations
keep every register not named by that operation unchanged even transiently.

This is a proof interface over `OracleMachine.step`, not an extra instruction
in the machine. In particular a target vector does not become a free oracle.
-/
structure OperationSpan {m d l : ℕ} (P : Main.OracleMachine)
    (U V : Main.Label l → Main.Vec m d) (x : Fin 2 → Main.Label l)
    (input : List Bool) (R : Main.Registers m d) (op : Main.RegisterOp m d)
    (start finish : Config P.base) (time : ℕ) : Prop where
  positive : 0 < time
  before : start.catalyst = Main.registerCode R
  after : finish.catalyst = Main.registerCode (op.apply U V x R)
  span : Segment (P.step U V x input) (OperationInvariant P start op time) start finish time

/-- A schedule records global reachability at operation boundaries as well as
local spans. Its cuts carry the time charged to each operation, including its
single oracle step. The reachability certificates can be built by `Segment.trans`. -/
structure OperationSchedule {m d l : ℕ} (P : Main.OracleMachine)
    (U V : Main.Label l → Main.Vec m d) (x : Fin 2 → Main.Label l)
    (input : List Bool) (α : ZMod m) (R : Main.Registers m d)
    (ops : List (Main.RegisterOp m d)) (T : ℕ) where
  cuts : Fin (ops.length + 1) → ℕ
  strict : StrictMono cuts
  first : cuts 0 = 0
  last : cuts (Fin.last ops.length) = T
  config : Fin (ops.length + 1) → Config P.base
  reaches : ∀ i, P.run U V x input α R (cuts i) = some (config i)
  operation : ∀ i : Fin ops.length,
    OperationSpan P U V x input (Main.execute U V x R (ops.take i.val)) (ops.get i)
      (config i.castSucc) (config i.succ) (cuts i.succ - cuts i.castSucc)

end CatalyticTreeEval.Contracts


