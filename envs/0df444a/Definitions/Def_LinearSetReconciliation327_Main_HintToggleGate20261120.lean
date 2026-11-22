-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintToggleGate20261120
-- name    : LinearSetReconciliation327_Main_HintToggleGate20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:50:49.141398+00:00
-- url     : https://prove2.me/theorems/726fece3-c732-4575-8107-7766e609d176
-- title:
--   LinearSetReconciliation327 — HintToggleGate (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintToggleGate20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintToggleGateTable (E : RAMEnv) (descriptor gate coordinate detBase payBase control : ℕ) : Prop where
  word : 3 < 2 ^ E.W
  span : descriptor + 3 < 2 ^ E.W
  table_span : detBase + 3 < 2 ^ E.W
  gate_fit : gate < 2 ^ E.W
  coordinate_fit : coordinate < 2 ^ E.W
  payload_fit : payBase < 2 ^ E.W
  control_fit : control < 2 ^ E.W
  gate_address : E.det descriptor = gate
  coordinate_value : E.det (descriptor + 1) = coordinate
  table_address : E.det (descriptor + 2) = detBase
  payload_address : E.det (descriptor + 3) = payBase
  control_address : E.det (detBase + 3) = control

def hintToggleGateSetup : List Instr :=
  [.imm 7 1, .qDet 3 6, .load 1 3, .add 3 6 7, .qDet 0 3, .add 3 3 7, .qDet 14 3,
    .add 3 3 7, .qDet 15 3]

def hintToggleGateRestore : List Instr := [.imm 3 3, .add 3 14 3, .qDet 14 3]

def hintToggleGateBranch : Stmt := .ite (.neqz 1) upSavedSup (.code [])
def hintToggleGateAction : Stmt :=
  .seq (.code hintToggleGateSetup) (.seq hintToggleGateBranch (.code hintToggleGateRestore))

theorem hintToggleGateSetup_spec (E : RAMEnv) (s : RAMState) (descriptor gate coordinate detBase payBase control : ℕ)
    (tbl : HintToggleGateTable E descriptor gate coordinate detBase payBase control)
    (hArg : s.regs 6 = descriptor) (hFlag : s.mem gate < 2 ^ E.W) :
    let out := runBlock hintToggleGateSetup E s
    out.pc = s.pc + 9 ∧ out.mem = s.mem ∧ out.regs 1 = s.mem gate ∧
      out.regs 0 = coordinate ∧ out.regs 14 = detBase ∧ out.regs 15 = payBase := by
  have hS := tbl.span
  have hDS := tbl.table_span
  have hW := tbl.word
  have h1 : 1 < 2 ^ E.W := by omega
  have hA1 : descriptor + 1 < 2 ^ E.W := by omega
  have hA2 : descriptor + 1 + 1 < 2 ^ E.W := by omega
  have hA3 : descriptor + 1 + 1 + 1 < 2 ^ E.W := by omega
  have hDet : detBase < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintToggleGateSetup, runBlock, execInstr, hArg, tbl.gate_address, tbl.coordinate_value,
      tbl.table_address, tbl.payload_address, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hA1, Nat.mod_eq_of_lt hA2,
      Nat.mod_eq_of_lt hA3, Nat.mod_eq_of_lt tbl.gate_fit, Nat.mod_eq_of_lt tbl.coordinate_fit,
      Nat.mod_eq_of_lt hDet, Nat.mod_eq_of_lt tbl.payload_fit, Nat.mod_eq_of_lt hFlag]

theorem hintToggleGateRestore_spec (E : RAMEnv) (s : RAMState) (descriptor gate coordinate detBase payBase control : ℕ)
    (tbl : HintToggleGateTable E descriptor gate coordinate detBase payBase control)
    (hBase : s.regs 14 = detBase) :
    let out := runBlock hintToggleGateRestore E s
    out.pc = s.pc + 3 ∧ out.mem = s.mem ∧ out.regs 14 = control := by
  refine ⟨?_, rfl, ?_⟩ <;>
    simp [hintToggleGateRestore, runBlock, execInstr, hBase, tbl.control_address,
      Nat.mod_eq_of_lt tbl.word, Nat.mod_eq_of_lt tbl.table_span, Nat.mod_eq_of_lt tbl.control_fit]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintToggleGateSetup_spec
#print axioms LinearSetReconciliation327.Main.hintToggleGateRestore_spec


