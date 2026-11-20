-- Prove2me | Definitions.Def_EMRamB000
-- name    : EMRamB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:45.343613+00:00
-- url     : https://prove2.me/theorems/16e26ac1-29ce-4d6c-ae0e-90d1ebe98a5b
-- title:
--   Definitions bundle EMRamB000
-- statement:
--   A definitions bundle of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 304 declarations of that development: 247 definitions, 10 inductive types or structures and 47 theorems. The definitions and types are `EditMulticoloring.Dev.Ram.BevKeep`, `EditMulticoloring.Dev.Ram.CAInv`, `EditMulticoloring.Dev.Ram.CAPlace`, `EditMulticoloring.Dev.Ram.Cmd`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.emits`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.Cmd.reads`, `EditMulticoloring.Dev.Ram.Cmd.stores`, `EditMulticoloring.Dev.Ram.Cmd.wregs`, `EditMulticoloring.Dev.Ram.DCtx`, `EditMulticoloring.Dev.Ram.DHyp`, `EditMulticoloring.Dev.Ram.DInv`, `EditMulticoloring.Dev.Ram.DM`, `EditMulticoloring.Dev.Ram.DOut`, `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.EnInv`, `EditMulticoloring.Dev.Ram.EncS.MInv`, `EditMulticoloring.Dev.Ram.EncS.SInv`, `EditMulticoloring.Dev.Ram.EncS.chooseA`, `EditMulticoloring.Dev.Ram.EncS.chooseC`, `EditMulticoloring.Dev.Ram.EncS.greedyStep`, `EditMulticoloring.Dev.Ram.EncS.initBody`, `EditMulticoloring.Dev.Ram.EncS.mainBody`, `EditMulticoloring.Dev.Ram.EncS.mainD`, `EditMulticoloring.Dev.Ram.EncS.markBody`, `EditMulticoloring.Dev.Ram.EncS.reprW`, `EditMulticoloring.Dev.Ram.EncS.shortCfg`, `EditMulticoloring.Dev.Ram.EncS.shortCost`, `EditMulticoloring.Dev.Ram.EncS.shortM`, `EditMulticoloring.Dev.Ram.EncS.shortW`, `EditMulticoloring.Dev.Ram.EncS.visBound`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.EnumCfg.Agree`, `EditMulticoloring.Dev.Ram.EnumCfg.BodyFrame`, `EditMulticoloring.Dev.Ram.EnumCfg.D`, `EditMulticoloring.Dev.Ram.EnumCfg.Fr`, `EditMulticoloring.Dev.Ram.EnumCfg.IHk`, `EditMulticoloring.Dev.Ram.EnumCfg.Keep`, `EditMulticoloring.Dev.Ram.EnumCfg.LQ` and 217 more.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `RamColor`, `RamColor2`, `RamColor3`, `RamColor4`, `RamCore`, `RamDecode`, `RamDecode2`, `RamDecode3`, `RamDecode4`, `RamEncode`, `RamEncode2`, `RamEncode4`, `RamEncodeS1`, `RamEncodeS2`, `RamEncodeS3`, `RamEncodeS4`, `RamEnum`, `RamEnum2`, `RamEnum3`, `RamGF`, `RamLib`, `RamLib2`, `RamModulus`, `RamParams`, `RamParams2`, `RamParams3`, `RamParams4`, `RamParams5`, `RamParams6`, `RamSim`, `RamTop1`.
--
--   **Imports.** It imports the published bundles `Def_EditMulticoloring_Code_Construction` and `Def_EditMulticoloring_Code_Machine`.
--
--   **Imported by** (directly, in this split): the statements `EditMulticoloring.Dev.Ram.CAInv.stable`, `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_word`, `EditMulticoloring.Dev.Ram.EncS.shortW_inverse`, `EditMulticoloring.Dev.Ram.EncS.shortW_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec`, `EditMulticoloring.Dev.Ram.WordAt.congr`, `EditMulticoloring.Dev.Ram.WordAt.lt`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.ceilLogW_spec`, `EditMulticoloring_Dev_Ram_colorEnum_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorOf_spec`, `EditMulticoloring.Dev.Ram.colorOut_spec`, `EditMulticoloring.Dev.Ram.colorSearch_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.copyW_spec`, `EditMulticoloring.Dev.Ram.copyW_word`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.decPre_spec`, `EditMulticoloring.Dev.Ram.digitsW_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encD_spec`, `EditMulticoloring.Dev.Ram.encE_spec`, `EditMulticoloring.Dev.Ram.encF_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.encProg_spec`, `EditMulticoloring.Dev.Ram.enumScripts_spec`, `EditMulticoloring.Dev.Ram.eqW_spec`, `EditMulticoloring.Dev.Ram.exec_cur_of_reads`, `EditMulticoloring.Dev.Ram.exec_mem_of_stores`, `EditMulticoloring.Dev.Ram.exec_out_of_emits`, `EditMulticoloring.Dev.Ram.foldl_listF`, `EditMulticoloring.Dev.Ram.gfField_spec`, `EditMulticoloring.Dev.Ram.gfRem_spec`, `EditMulticoloring.Dev.Ram.goodW_spec`, `EditMulticoloring.Dev.Ram.kappa_bits_le`, `EditMulticoloring.Dev.Ram.kappa_bits_one_le`, `EditMulticoloring.Dev.Ram.length_le_of_mem_visits`, `EditMulticoloring.Dev.Ram.modulusW_spec`, `EditMulticoloring.Dev.Ram.pA_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC7_spec`, `EditMulticoloring.Dev.Ram.pC8_spec`, `EditMulticoloring.Dev.Ram.pPrime_spec`, `EditMulticoloring.Dev.Ram.paramsW_spec`, `EditMulticoloring.Dev.Ram.powW_spec`, `EditMulticoloring.Dev.Ram.radW_spec`, `EditMulticoloring.Dev.Ram.readW_spec`, `EditMulticoloring.Dev.Ram.runLen_inputAt`, `EditMulticoloring.Dev.Ram.self_mem_visits`, `EditMulticoloring.Dev.Ram.valueW_spec`, `EditMulticoloring.Dev.Ram.valueW_word`, `EditMulticoloring.Dev.Ram.visits_le_visBound`, `EditMulticoloring.Dev.Ram.visits_length_le` and `EditMulticoloring.Dev.Ram.words_eq_iff`; the proofs of `EditMulticoloring.Code.ram_programs`, `EditMulticoloring.Dev.Ram.CAInv.stable`, `EditMulticoloring.Dev.Ram.EncS.greedy_length_le`, `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_word`, `EditMulticoloring.Dev.Ram.EncS.shortW_inverse`, `EditMulticoloring.Dev.Ram.EncS.shortW_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec`, `EditMulticoloring.Dev.Ram.WordAt.congr`, `EditMulticoloring.Dev.Ram.WordAt.lt`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.ceilLogW_spec`, `EditMulticoloring_Dev_Ram_colorEnum_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorOf_spec`, `EditMulticoloring.Dev.Ram.colorOut_spec`, `EditMulticoloring.Dev.Ram.colorSearch_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.copyW_spec`, `EditMulticoloring.Dev.Ram.copyW_word`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.decPre_spec`, `EditMulticoloring.Dev.Ram.digitsW_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encD_spec`, `EditMulticoloring.Dev.Ram.encE_spec`, `EditMulticoloring.Dev.Ram.encF_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.encProg_spec`, `EditMulticoloring.Dev.Ram.enumScripts_spec`, `EditMulticoloring.Dev.Ram.eqW_spec`, `EditMulticoloring.Dev.Ram.exec_cur_of_reads`, `EditMulticoloring.Dev.Ram.exec_mem_of_stores`, `EditMulticoloring.Dev.Ram.exec_out_of_emits`, `EditMulticoloring.Dev.Ram.foldl_listF`, `EditMulticoloring.Dev.Ram.gfField_spec`, `EditMulticoloring.Dev.Ram.gfRem_spec`, `EditMulticoloring.Dev.Ram.goodW_spec`, `EditMulticoloring.Dev.Ram.kappa_bits_le`, `EditMulticoloring.Dev.Ram.kappa_bits_one_le`, `EditMulticoloring.Dev.Ram.length_le_of_mem_visits`, `EditMulticoloring.Dev.Ram.localColor_lt`, `EditMulticoloring.Dev.Ram.modulusW_spec`, `EditMulticoloring.Dev.Ram.pA_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC7_spec`, `EditMulticoloring.Dev.Ram.pC8_spec`, `EditMulticoloring.Dev.Ram.pPrime_spec`, `EditMulticoloring.Dev.Ram.paramsW_spec`, `EditMulticoloring.Dev.Ram.powW_spec`, `EditMulticoloring.Dev.Ram.radW_spec`, `EditMulticoloring.Dev.Ram.readW_spec`, `EditMulticoloring.Dev.Ram.runLen_inputAt`, `EditMulticoloring.Dev.Ram.self_mem_visits`, `EditMulticoloring.Dev.Ram.upd_eq`, `EditMulticoloring.Dev.Ram.valueW_spec`, `EditMulticoloring.Dev.Ram.valueW_word`, `EditMulticoloring.Dev.Ram.visits_le_visBound`, `EditMulticoloring.Dev.Ram.visits_length_le` and `EditMulticoloring.Dev.Ram.words_eq_iff`.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819); definitions carved from that development

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine

section
-- module Solutions.EditMulticoloring.RamCore
/-!
# A structured language over the RAM machine (q379)

`Cmd` is a small structured language whose primitives mirror `RAM.Instruction`, with
arrays addressed through `Nat.pair` and bounded loops (`loop a c` repeats `c` as many times
as register `a` holds on entry).  Its semantics `Cmd.exec` is a total Lean function and
`Cmd.cost` an upper bound for the bit cost of the compiled RAM code.  `RamSim.lean`
compiles a `Cmd` to a `RAM.Program` and proves the simulation (`toProgram_spec`).

FROZEN INTERFACE: every other part is written against these definitions.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- Primitive commands on user registers.  `aload d x i` reads array `x` (the value of
register `x`) at index (value of register `i`): memory cell `Nat.pair x i`. -/
inductive Prim where
  | lit (d v : ℕ)
  | copy (d a : ℕ)
  | arith (op : RAM.Arithmetic) (d a b : ℕ)
  | aload (d x i : ℕ)
  | astore (x i v : ℕ)
  | read (d : ℕ)
  | emit (a : ℕ)

inductive Cmd where
  | prim (p : Prim)
  | seq (c₁ c₂ : Cmd)
  /-- `ifz a c₁ c₂`: run `c₁` if register `a` is zero, else `c₂`. -/
  | ifz (a : ℕ) (c₁ c₂ : Cmd)
  /-- `loop a c`: run `c` exactly `regs a` times (value read on entry). -/
  | loop (a : ℕ) (c : Cmd)
  | skip

/-- High-level machine state: registers, memory (arrays via `Nat.pair`), input cursor, output. -/
structure HS where
  regs : ℕ → ℕ
  mem : ℕ → ℕ
  cur : ℕ
  out : List ℕ

/-- The state at the start of a run on parameter `n`: register 0 holds `n`. -/
def HS.init (n : ℕ) : HS := ⟨fun r => if r = 0 then n else 0, fun _ => 0, 0, []⟩

/-- Array cell `i` of array `x`. -/
def HS.arr (s : HS) (x i : ℕ) : ℕ := s.mem (Nat.pair x i)

def Prim.exec (inp : ℕ → ℕ) : Prim → HS → HS
  | .lit d v, s => { s with regs := Function.update s.regs d v }
  | .copy d a, s => { s with regs := Function.update s.regs d (s.regs a) }
  | .arith op d a b, s =>
      { s with regs := Function.update s.regs d (RAM.arithmeticValue op (s.regs a) (s.regs b)) }
  | .aload d x i, s =>
      { s with regs := Function.update s.regs d (s.mem (Nat.pair (s.regs x) (s.regs i))) }
  | .astore x i v, s =>
      { s with mem := Function.update s.mem (Nat.pair (s.regs x) (s.regs i)) (s.regs v) }
  | .read d, s => { s with regs := Function.update s.regs d (inp s.cur), cur := s.cur + 1 }
  | .emit a, s => { s with out := s.out ++ [s.regs a] }

def Cmd.exec (inp : ℕ → ℕ) : Cmd → HS → HS
  | .prim p, s => p.exec inp s
  | .seq c₁ c₂, s => Cmd.exec inp c₂ (Cmd.exec inp c₁ s)
  | .ifz a c₁ c₂, s => if s.regs a = 0 then Cmd.exec inp c₁ s else Cmd.exec inp c₂ s
  | .loop a c, s => (Cmd.exec inp c)^[s.regs a] s
  | .skip, s => s

/-- The uniform charge for one primitive or one control overhead, where `B` bounds the bit
length of every program counter and register index, and `W` the bit length of the data. -/
def kappa (B W : ℕ) : ℕ := 1000 * (B + 1) + 1000 * (W + 2) ^ 2

/-- Bit length of the data a primitive touches (a sum dominates each value). -/
def Prim.wt (inp : ℕ → ℕ) : Prim → HS → ℕ
  | .lit _ v, _ => RAM.bits v
  | .copy _ a, s => RAM.bits (s.regs a)
  | .arith _ _ a b, s => RAM.bits (s.regs a + s.regs b)
  | .aload _ x i, s => RAM.bits (s.regs x + s.regs i + s.mem (Nat.pair (s.regs x) (s.regs i)))
  | .astore x i v, s => RAM.bits (s.regs x + s.regs i + s.regs v)
  | .read _, s => RAM.bits (s.cur + inp s.cur)
  | .emit a, s => RAM.bits (s.regs a + s.out.length)

/-- Cost of the iterations of a loop whose counter starts at `v`. -/
def loopCost (B : ℕ) (body : HS → HS) (bc : HS → ℕ) : ℕ → HS → ℕ
  | 0, _ => kappa B 0
  | v + 1, s => kappa B (RAM.bits (v + 1)) + bc s + loopCost B body bc v (body s)

def Cmd.cost (inp : ℕ → ℕ) (B : ℕ) : Cmd → HS → ℕ
  | .prim p, s => kappa B (p.wt inp s)
  | .seq c₁ c₂, s => Cmd.cost inp B c₁ s + Cmd.cost inp B c₂ (Cmd.exec inp c₁ s)
  | .ifz a c₁ c₂, s => kappa B (RAM.bits (s.regs a)) +
      (if s.regs a = 0 then Cmd.cost inp B c₁ s else Cmd.cost inp B c₂ s)
  | .loop a c, s => kappa B (RAM.bits (s.regs a)) +
      loopCost B (Cmd.exec inp c) (Cmd.cost inp B c) (s.regs a) s
  | .skip, _ => 0

/-! Convenience constructors. -/
def lit (d v : ℕ) : Cmd := .prim (.lit d v)
def cp (d a : ℕ) : Cmd := .prim (.copy d a)
def ar (op : RAM.Arithmetic) (d a b : ℕ) : Cmd := .prim (.arith op d a b)
def ald (d x i : ℕ) : Cmd := .prim (.aload d x i)
def ast (x i v : ℕ) : Cmd := .prim (.astore x i v)
def rd (d : ℕ) : Cmd := .prim (.read d)
def em (a : ℕ) : Cmd := .prim (.emit a)
def seqs : List Cmd → Cmd
  | [] => .skip
  | c :: cs => .seq c (seqs cs)

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamLib
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-- Register update. -/
def HS.setR (s : HS) (r v : ℕ) : HS := { s with regs := Function.update s.regs r v }

@[simp] theorem HS.setR_regs (s : HS) (r v : ℕ) : (s.setR r v).regs = Function.update s.regs r v := rfl
@[simp] theorem HS.setR_mem (s : HS) (r v : ℕ) : (s.setR r v).mem = s.mem := rfl
@[simp] theorem HS.setR_cur (s : HS) (r v : ℕ) : (s.setR r v).cur = s.cur := rfl
@[simp] theorem HS.setR_out (s : HS) (r v : ℕ) : (s.setR r v).out = s.out := rfl
@[simp] theorem HS.setR_arr (s : HS) (r v x i : ℕ) : (s.setR r v).arr x i = s.arr x i := rfl

/-- Memory update at array cell `(x, i)`. -/
def HS.store (s : HS) (x i v : ℕ) : HS := { s with mem := Function.update s.mem (Nat.pair x i) v }

@[simp] theorem HS.store_regs (s : HS) (x i v : ℕ) : (s.store x i v).regs = s.regs := rfl
@[simp] theorem HS.store_cur (s : HS) (x i v : ℕ) : (s.store x i v).cur = s.cur := rfl
@[simp] theorem HS.store_out (s : HS) (x i v : ℕ) : (s.store x i v).out = s.out := rfl
@[simp] theorem HS.store_arr (s : HS) (x i v y j : ℕ) :
    (s.store x i v).arr y j = if y = x ∧ j = i then v else s.arr y j := by
  simp only [HS.store, HS.arr, Function.update_apply]
  by_cases h : y = x ∧ j = i
  · simp [h]
  · rw [if_neg, if_neg h]
    intro he
    exact h (by have := Nat.pair_eq_pair.mp he; exact this)

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

@[simp] theorem exec_seq (c₁ c₂ : Cmd) (s : HS) :
    (Cmd.seq c₁ c₂).exec inp s = c₂.exec inp (c₁.exec inp s) := rfl
@[simp] theorem exec_skip (s : HS) : Cmd.skip.exec inp s = s := rfl
@[simp] theorem exec_ifz (a : ℕ) (c₁ c₂ : Cmd) (s : HS) :
    (Cmd.ifz a c₁ c₂).exec inp s = if s.regs a = 0 then c₁.exec inp s else c₂.exec inp s := rfl
@[simp] theorem exec_seqs_nil (s : HS) : (seqs []).exec inp s = s := rfl
@[simp] theorem exec_seqs_cons (c : Cmd) (cs : List Cmd) (s : HS) :
    (seqs (c :: cs)).exec inp s = (seqs cs).exec inp (c.exec inp s) := rfl
@[simp] theorem exec_lit (d v : ℕ) (s : HS) : (lit d v).exec inp s = s.setR d v := rfl
@[simp] theorem exec_cp (d a : ℕ) (s : HS) : (cp d a).exec inp s = s.setR d (s.regs a) := rfl
@[simp] theorem exec_ar (op : RAM.Arithmetic) (d a b : ℕ) (s : HS) :
    (ar op d a b).exec inp s = s.setR d (RAM.arithmeticValue op (s.regs a) (s.regs b)) := rfl
@[simp] theorem exec_ald (d x i : ℕ) (s : HS) :
    (ald d x i).exec inp s = s.setR d (s.arr (s.regs x) (s.regs i)) := rfl
@[simp] theorem exec_ast (x i v : ℕ) (s : HS) :
    (ast x i v).exec inp s = s.store (s.regs x) (s.regs i) (s.regs v) := rfl
@[simp] theorem exec_rd (d : ℕ) (s : HS) :
    (rd d).exec inp s = { s with regs := Function.update s.regs d (inp s.cur), cur := s.cur + 1 } := rfl
@[simp] theorem exec_em (a : ℕ) (s : HS) :
    (em a).exec inp s = { s with out := s.out ++ [s.regs a] } := rfl

@[simp] theorem cost_seq (c₁ c₂ : Cmd) (s : HS) :
    (Cmd.seq c₁ c₂).cost inp B s = c₁.cost inp B s + c₂.cost inp B (c₁.exec inp s) := rfl
@[simp] theorem cost_skip (s : HS) : Cmd.skip.cost inp B s = 0 := rfl
@[simp] theorem cost_ifz (a : ℕ) (c₁ c₂ : Cmd) (s : HS) :
    (Cmd.ifz a c₁ c₂).cost inp B s = kappa B (RAM.bits (s.regs a)) +
      (if s.regs a = 0 then c₁.cost inp B s else c₂.cost inp B s) := rfl
@[simp] theorem cost_seqs_nil (s : HS) : (seqs []).cost inp B s = 0 := rfl
@[simp] theorem cost_seqs_cons (c : Cmd) (cs : List Cmd) (s : HS) :
    (seqs (c :: cs)).cost inp B s = c.cost inp B s + (seqs cs).cost inp B (c.exec inp s) := rfl
@[simp] theorem cost_lit (d v : ℕ) (s : HS) : (lit d v).cost inp B s = kappa B (RAM.bits v) := rfl
@[simp] theorem cost_cp (d a : ℕ) (s : HS) :
    (cp d a).cost inp B s = kappa B (RAM.bits (s.regs a)) := rfl
@[simp] theorem cost_ar (op : RAM.Arithmetic) (d a b : ℕ) (s : HS) :
    (ar op d a b).cost inp B s = kappa B (RAM.bits (s.regs a + s.regs b)) := rfl
@[simp] theorem cost_ald (d x i : ℕ) (s : HS) :
    (ald d x i).cost inp B s =
      kappa B (RAM.bits (s.regs x + s.regs i + s.arr (s.regs x) (s.regs i))) := rfl
@[simp] theorem cost_ast (x i v : ℕ) (s : HS) :
    (ast x i v).cost inp B s = kappa B (RAM.bits (s.regs x + s.regs i + s.regs v)) := rfl
@[simp] theorem cost_rd (d : ℕ) (s : HS) :
    (rd d).cost inp B s = kappa B (RAM.bits (s.cur + inp s.cur)) := rfl
@[simp] theorem cost_em (a : ℕ) (s : HS) :
    (em a).cost inp B s = kappa B (RAM.bits (s.regs a + s.out.length)) := rfl

@[simp] theorem arith_add (a b : ℕ) : RAM.arithmeticValue .add a b = a + b := rfl
@[simp] theorem arith_sub (a b : ℕ) : RAM.arithmeticValue .sub a b = a - b := rfl
@[simp] theorem arith_mul (a b : ℕ) : RAM.arithmeticValue .mul a b = a * b := rfl
@[simp] theorem arith_div (a b : ℕ) : RAM.arithmeticValue .div a b = a / b := rfl
@[simp] theorem arith_mod (a b : ℕ) : RAM.arithmeticValue .mod a b = a % b := rfl
@[simp] theorem arith_lt (a b : ℕ) : RAM.arithmeticValue .lt a b = if a < b then 1 else 0 := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

@[simp] theorem bits_zero : RAM.bits 0 = 1 := rfl
@[simp] theorem bits_one : RAM.bits 1 = 1 := rfl

/-! ## Syntactic frames -/

/-- Registers a command may write. -/
def Cmd.wregs : Cmd → List ℕ
  | .prim (.lit d _) => [d]
  | .prim (.copy d _) => [d]
  | .prim (.arith _ d _ _) => [d]
  | .prim (.aload d _ _) => [d]
  | .prim (.astore _ _ _) => []
  | .prim (.read d) => [d]
  | .prim (.emit _) => []
  | .seq c₁ c₂ => c₁.wregs ++ c₂.wregs
  | .ifz _ c₁ c₂ => c₁.wregs ++ c₂.wregs
  | .loop _ c => c.wregs
  | .skip => []

/-- Whether a command contains a `read`. -/
def Cmd.reads : Cmd → Bool
  | .prim (.read _) => true
  | .prim _ => false
  | .seq c₁ c₂ => c₁.reads || c₂.reads
  | .ifz _ c₁ c₂ => c₁.reads || c₂.reads
  | .loop _ c => c.reads
  | .skip => false

/-- Whether a command contains an `emit`. -/
def Cmd.emits : Cmd → Bool
  | .prim (.emit _) => true
  | .prim _ => false
  | .seq c₁ c₂ => c₁.emits || c₂.emits
  | .ifz _ c₁ c₂ => c₁.emits || c₂.emits
  | .loop _ c => c.emits
  | .skip => false

/-- Whether a command contains a `store`. -/
def Cmd.stores : Cmd → Bool
  | .prim (.astore _ _ _) => true
  | .prim _ => false
  | .seq c₁ c₂ => c₁.stores || c₂.stores
  | .ifz _ c₁ c₂ => c₁.stores || c₂.stores
  | .loop _ c => c.stores
  | .skip => false

/-! ## Loops -/

section Loops
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Counted for-loop: `i := 0; repeat (value of n) times { body; one := 1; i := i + one }`. -/
def forLoop (i n one : ℕ) (body : Cmd) : Cmd :=
  .seq (lit i 0) (.loop n (.seq body (.seq (lit one 1) (ar .add i i one))))

@[simp] theorem forLoop_reads (i n one : ℕ) (body : Cmd) :
    (forLoop i n one body).reads = body.reads := by
  simp [forLoop, Cmd.reads, lit, ar]
@[simp] theorem forLoop_emits (i n one : ℕ) (body : Cmd) :
    (forLoop i n one body).emits = body.emits := by
  simp [forLoop, Cmd.emits, lit, ar]
@[simp] theorem forLoop_stores (i n one : ℕ) (body : Cmd) :
    (forLoop i n one body).stores = body.stores := by
  simp [forLoop, Cmd.stores, lit, ar]

end Loops

/-! ## Words stored in arrays -/

/-- `w` is stored in array `x` from offset `off` (one cell per symbol, its value). -/
def WordAt {q : ℕ} (s : HS) (x off : ℕ) (w : Word q) : Prop :=
  ∀ i (h : i < w.length), s.arr x (off + i) = (w[i]).val

/-! ## Copying a block of cells -/

section Copy
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Copy `regs n` cells: `arr D (dO + j) := arr S (so + j)` for `j < regs n` (registers `S`,
`D` hold array ids, `so`, `dO` offsets).  Scratch registers: `j t u one`. -/
def copyW (S so D dO n j t u one : ℕ) : Cmd :=
  forLoop j n one (seqs [ar .add t so j, ald u S t, ar .add t dO j, ast D t u])

@[simp] theorem copyW_reads (S so D dO n j t u one : ℕ) :
    (copyW S so D dO n j t u one).reads = false := rfl
@[simp] theorem copyW_emits (S so D dO n j t u one : ℕ) :
    (copyW S so D dO n j t u one).emits = false := rfl

end Copy

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

/-- The words visited by the scripts of depth `s` from `x`, in order (with multiplicity). -/
def visits {q : ℕ} (s : ℕ) (x : Word q) : List (Word q) := (scripts s x).map Prod.snd

def insW {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) : Word q := x.take i ++ a :: x.drop i
def delW {q : ℕ} (x : Word q) (i : ℕ) : Word q := x.take i ++ x.drop (i + 1)
def repW {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) : Word q := x.take i ++ a :: x.drop (i + 1)

/-- A `Fin q`-indexed family extended by `[]` to all naturals. -/
def finFlat {q : ℕ} {β : Type*} (F : Fin q → List β) (a : ℕ) : List β :=
  if h : a < q then F ⟨a, h⟩ else []

/-! ## Configuration -/

/-- Resources owned by an enumerator: registers `r0 ..` (16 scratch registers, then three per
level) and arrays `a0` (the visit array) and `a0 + 1 + k` (the level-`k` buffer). -/
structure EnumCfg where
  r0 : ℕ
  a0 : ℕ

namespace EnumCfg
variable (c : EnumCfg)

/-- Register receiving the length of the visited word. -/
@[simp] def VL : ℕ := c.r0
@[simp] def one : ℕ := c.r0 + 1
@[simp] def cnt : ℕ := c.r0 + 2
@[simp] def S : ℕ := c.r0 + 3
@[simp] def so : ℕ := c.r0 + 4
@[simp] def D : ℕ := c.r0 + 5
@[simp] def dO : ℕ := c.r0 + 6
@[simp] def n : ℕ := c.r0 + 7
@[simp] def j : ℕ := c.r0 + 8
@[simp] def t : ℕ := c.r0 + 9
@[simp] def u : ℕ := c.r0 + 10
@[simp] def d : ℕ := c.r0 + 11
@[simp] def e : ℕ := c.r0 + 12
/-- Level-`k` registers: position, symbol, length of the level word. -/
@[simp] def iR (k : ℕ) : ℕ := c.r0 + (16 + 3 * k)
@[simp] def aR (k : ℕ) : ℕ := c.r0 + (17 + 3 * k)
@[simp] def lenR (k : ℕ) : ℕ := c.r0 + (18 + 3 * k)
/-- The visit array. -/
@[simp] def vis : ℕ := c.a0
/-- The level-`k` buffer; the input of `enumScripts q s` lives in `buf s`, length in `lenR s`. -/
@[simp] def buf (k : ℕ) : ℕ := c.a0 + 1 + k

/-- Registers owned by the enumerator of depth `s`. -/
def ownsReg (s r : ℕ) : Prop := c.r0 ≤ r ∧ r ≤ c.r0 + (18 + 3 * s)
/-- Arrays owned by the enumerator of depth `s`. -/
def ownsArr (s x : ℕ) : Prop := c.a0 ≤ x ∧ x ≤ c.a0 + 1 + s

/-- `st'` agrees with `st` outside the resources owned by the depth-`s` enumerator. -/
def Agree (s : ℕ) (st st' : HS) : Prop :=
  (∀ r, ¬ c.ownsReg s r → st'.regs r = st.regs r) ∧
  (∀ y i, ¬ c.ownsArr s y → st'.arr y i = st.arr y i) ∧ st'.cur = st.cur ∧ st'.out = st.out

/-- The body's obligation: it keeps every owned register except `VL` and every owned array
except `vis`. -/
def BodyFrame (s : ℕ) (st st' : HS) : Prop :=
  (∀ r, c.ownsReg s r → r ≠ c.VL → st'.regs r = st.regs r) ∧
  (∀ y i, c.ownsArr s y → y ≠ c.vis → st'.arr y i = st.arr y i)

/-- Internal frame: only scratch registers, register `w` and array `Y` change. -/
def Fr (w Y : ℕ) (st st' : HS) : Prop :=
  (∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → r ≠ w → st'.regs r = st.regs r) ∧
  (∀ y i, y ≠ Y → st'.arr y i = st.arr y i) ∧ st'.cur = st.cur ∧ st'.out = st.out

/-- The levels `≥ k` (registers from `lenR k` to `lenR s`, buffers `k .. s`) are unchanged. -/
def Keep (s k : ℕ) (st st' : HS) : Prop :=
  (∀ r, c.lenR k ≤ r → r ≤ c.lenR s → st'.regs r = st.regs r) ∧
  (∀ y i, c.buf k ≤ y → y ≤ c.buf s → st'.arr y i = st.arr y i)

/-! ## Code -/

/-- Copy `regs n` cells from `(regs S, regs so)` to `(regs D, regs dO)`. -/
def cpy : Cmd := copyW c.S c.so c.D c.dO c.n c.j c.t c.u c.one

/-- Copy the level-`k` word into the visit array, its length into `VL`. -/
def visitC (k : ℕ) : Cmd :=
  .seq (seqs [lit c.S (c.buf k), lit c.so 0, lit c.D c.vis, lit c.dO 0, cp c.n (c.lenR k)])
    (.seq c.cpy (cp c.VL (c.lenR k)))

/-- Level `k` word := insert symbol `aR (k+1)` at position `iR (k+1)` of the level `k+1` word. -/
def insC (k : ℕ) : Cmd :=
  .seq (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
      cp c.n (c.iR (k + 1))])
    (.seq c.cpy
      (.seq (seqs [ast c.D (c.iR (k + 1)) (c.aR (k + 1)),
          lit c.one 1, ar .add c.dO (c.iR (k + 1)) c.one, cp c.so (c.iR (k + 1)),
          ar .sub c.n (c.lenR (k + 1)) (c.iR (k + 1))])
        (.seq c.cpy (seqs [lit c.one 1, ar .add (c.lenR k) (c.lenR (k + 1)) c.one]))))

/-- Level `k` word := delete position `iR (k+1)` of the level `k+1` word. -/
def delC (k : ℕ) : Cmd :=
  .seq (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
      cp c.n (c.iR (k + 1))])
    (.seq c.cpy
      (.seq (seqs [lit c.one 1, cp c.dO (c.iR (k + 1)), ar .add c.so (c.iR (k + 1)) c.one,
          ar .sub c.n (c.lenR (k + 1)) c.so])
        (.seq c.cpy (seqs [lit c.one 1, ar .sub (c.lenR k) (c.lenR (k + 1)) c.one]))))

/-- Level `k` word := replace position `iR (k+1)` of the level `k+1` word by `aR (k+1)`. -/
def repC (k : ℕ) : Cmd :=
  .seq (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
      cp c.n (c.lenR (k + 1))])
    (.seq c.cpy (seqs [ast c.D (c.iR (k + 1)) (c.aR (k + 1)), cp (c.lenR k) (c.lenR (k + 1))]))

/-- `d := 0` iff the level `k+1` word has symbol `aR (k+1)` at position `iR (k+1)`. -/
def neqC (k : ℕ) : Cmd :=
  seqs [lit c.S (c.buf (k + 1)), ald c.u c.S (c.iR (k + 1)), ar .sub c.d c.u (c.aR (k + 1)),
    ar .sub c.e (c.aR (k + 1)) c.u, ar .add c.d c.d c.e]

/-- The enumerator from level `k` down. -/
def lev (q : ℕ) (body : Cmd) : ℕ → Cmd
  | 0 => .seq (c.visitC 0) body
  | k + 1 => seqs [c.visitC (k + 1), body,
      lit c.one 1, ar .add c.cnt (c.lenR (k + 1)) c.one,
      forLoop (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
        (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.insC k) (lev q body k)))),
      cp c.cnt (c.lenR (k + 1)),
      forLoop (c.iR (k + 1)) c.cnt c.one (.seq (c.delC k) (lev q body k)),
      cp c.cnt (c.lenR (k + 1)),
      forLoop (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
        (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
          (.ifz c.d .skip (.seq (c.repC k) (lev q body k))))))]

end EnumCfg

/-- The scripts enumerator of depth `s` (input word in `buf s`, length in `lenR s`). -/
def enumScripts (q s : ℕ) (cfg : EnumCfg) (body : Cmd) : Cmd := cfg.lev q body s

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum2
/-!
# The scripts enumerator, part 2: the three edit phases (q379, Part L)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Membership in the visit list -/

/-! ## Positions in the visit list -/

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

/-- Uniform data bound for the enumerator of depth `s` on words of length `L`. -/
def enumM (q L s : ℕ) : ℕ := 2 * c.a0 + 4 * (L + s + q) + 8

/-- Per-visit overhead of the enumerator. -/
def enumE (q L s : ℕ) : ℕ := 100 * (q + 1) * (L + s + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s))

/-- Loop invariant inside level `k`: the fold invariant, and levels `≥ k` as at entry. -/
def LQ {α : Type*} (Inv : α → HS → Prop) (s k : ℕ) (st0 : HS) (acc : α) (st : HS) : Prop :=
  Inv acc st ∧ c.Keep s k st0 st

section Phases
variable {q : ℕ} {α : Type*} (s L : ℕ) (body : Cmd) (Inv : α → HS → Prop) (f : α → Word q → α)
  (cb : ℕ) (Ok : α → Word q → Prop)

/-- The level-`k` hypothesis (the induction hypothesis of the enumerator). -/
def IHk (k : ℕ) : Prop :=
  ∀ (z : Word q) (a : α) (st : HS), z.length + k ≤ L + s →
    (∀ j (hj : j < (visits k z).length), Ok (((visits k z).take j).foldl f a) ((visits k z)[j])) →
    Inv a st → st.regs (c.lenR k) = z.length → WordAt st (c.buf k) 0 z →
    Inv ((visits k z).foldl f a) ((c.lev q body k).exec inp st) ∧
    c.Keep s k st ((c.lev q body k).exec inp st) ∧
    (c.lev q body k).cost inp B st ≤ (visits k z).length * (cb + c.enumE B q L s)

/-- The insertion loops of level `k+1`. -/
def insLoop (q : ℕ) (body : Cmd) (k : ℕ) : Cmd :=
  forLoop (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
    (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.insC k) (c.lev q body k))))

/-- The deletion loop of level `k+1`. -/
def delLoop (q : ℕ) (body : Cmd) (k : ℕ) : Cmd :=
  forLoop (c.iR (k + 1)) c.cnt c.one (.seq (c.delC k) (c.lev q body k))

/-- The replacement loops of level `k+1`. -/
def repLoop (q : ℕ) (body : Cmd) (k : ℕ) : Cmd :=
  forLoop (c.iR (k + 1)) c.cnt c.one (.seq (lit c.cnt q)
    (forLoop (c.aR (k + 1)) c.cnt c.one (.seq (c.neqC k)
      (.ifz c.d .skip (.seq (c.repC k) (c.lev q body k))))))

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamLib2
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-- With registers `r .. r+10`: `X ox Y oy n flag j t u v one`.
`flag := 1` iff `arr X (ox + i) = arr Y (oy + i)` for all `i < regs n`, else `0`.
Writes only `r+5 .. r+10`. -/
def eqW (r : ℕ) : Cmd :=
  .seq (lit (r + 5) 1) (forLoop (r + 6) (r + 4) (r + 10) (seqs [ar .add (r + 7) (r + 1) (r + 6),
    ald (r + 8) r (r + 7), ar .add (r + 7) (r + 3) (r + 6), ald (r + 9) (r + 2) (r + 7),
    ar .sub (r + 7) (r + 8) (r + 9), ar .sub (r + 9) (r + 9) (r + 8),
    ar .add (r + 7) (r + 7) (r + 9), .ifz (r + 7) .skip (lit (r + 5) 0)]))

/-! ### Emitting a stored block -/

/-- With registers `r .. r+6`: `X off n j t u one`. Emits `arr X (off + i)` for `i < regs n`.
Writes only `r+3 .. r+6`. -/
def emitW (r : ℕ) : Cmd :=
  forLoop (r + 3) (r + 2) (r + 6)
    (seqs [ar .add (r + 4) (r + 1) (r + 3), ald (r + 5) r (r + 4), em (r + 5)])

/-! ### Reading input -/

/-- Length of the leading run of nonzero values `g c, g (c+1), …` within the first `k`. -/
def runLen (g : ℕ → ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if runLen g c k = k ∧ g (c + k) ≠ 0 then k + 1 else runLen g c k

/-- With registers `r .. r+8`: `X off n len flag j t u one`.  Reads `N = regs n` input symbols,
storing `v - 1` at `arr X (off + i)`, and sets `len` to the length of the leading non-EOF
run among them (`runLen`).  Writes only `r+3 .. r+8`. -/
def readW (r : ℕ) : Cmd :=
  seqs [lit (r + 3) 0, lit (r + 4) 1, forLoop (r + 5) (r + 2) (r + 8)
    (seqs [rd (r + 7), .ifz (r + 7) (lit (r + 4) 0) .skip, ar .add (r + 3) (r + 3) (r + 4),
      lit (r + 8) 1, ar .sub (r + 7) (r + 7) (r + 8), ar .add (r + 6) (r + 1) (r + 5),
      ast r (r + 6) (r + 7)])]

/-! ### Horner evaluation -/

/-- `horner q g k = q^(k-1) g 0 + … + g (k-1)`, computed as `V := q * V + g i`. -/
def horner (q : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => q * horner q g k + g k

/-- With registers `r .. r+8`: `X off n Q V j t u one`.  `V := horner (regs Q) (arr X (off + ·)) N`.
Writes only `r+4 .. r+8`. -/
def valueW (r : ℕ) : Cmd :=
  .seq (lit (r + 4) 0) (forLoop (r + 5) (r + 2) (r + 8) (seqs [ar .add (r + 6) (r + 1) (r + 5),
    ald (r + 7) r (r + 6), ar .mul (r + 4) (r + 3) (r + 4), ar .add (r + 4) (r + 4) (r + 7)]))

/-! ### Digits -/

/-- With registers `r .. r+9`: `V Q K D off W j t u one`.
`arr D (off + i) := (V / Q ^ i) % Q` for `i < K`.  Writes only `r+5 .. r+9` and those cells. -/
def digitsW (r : ℕ) : Cmd :=
  .seq (cp (r + 5) r) (forLoop (r + 6) (r + 2) (r + 9) (seqs [ar .add (r + 7) (r + 4) (r + 6),
    ar .mod (r + 8) (r + 5) (r + 1), ast (r + 3) (r + 7) (r + 8), ar .div (r + 5) (r + 5) (r + 1)]))

end Utils

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum3
/-!
# The scripts enumerator: main theorem, size bound, toy clients (q379, Part L)

* `enumScripts_spec` — the fold specification of `enumScripts q s cfg body`;
* `visits_length_le` — `(visits s x).length ≤ ∑ i ∈ range (s+1), (2q(|x|+s+1))^i`;
* toy clients `countProg` (count the visited words of length `|x|` other than `x`) and
  `listProg` (store them as a 2-D array, word `j` at offsets `j * S`), both proved.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Size of the visit list -/

/-! ## Toy client (a): counting -/

section Toys
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Toy client (b): the list of visited words of length `|x|` other than `x` -/

def listF {q : ℕ} (x : Word q) (l : List (Word q)) (w : Word q) : List (Word q) :=
  if w.length = x.length ∧ w ≠ x then l ++ [w] else l

end Toys

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamGF
/-!
# GF(2)[X] arithmetic on `Cmd` (q379, Part G)

* fold forms of `binaryMul` / `binaryRem` with an arbitrary (large enough) loop count;
* value bounds (`binaryMul_lt`, `binaryRem_lt`, `fieldMul_lt`);
* `gfMul`, `gfRem`, `gfField` (= `fieldMul`) on a register block, `gfSetup` (the context).

Field-context block `g .. g+15`: `p lp P2 W N2 PN X Y Z` then scratch `g+9 .. g+15`, where
`lp = log2 p`, `P2 = 2^lp`, `N2 = 2W`, `PN = 2^(2W)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Arithmetic facts -/

/-- One step of `binaryMul a b`. -/
def mulStep (b a z i : ℕ) : ℕ := if b.testBit i then Nat.xor z (a * 2 ^ i) else z

/-- One step of `binaryRem p`. -/
def remStep (p z i : ℕ) : ℕ :=
  if p ≠ 0 ∧ p.log2 ≤ i ∧ z.testBit i then Nat.xor z (p * 2 ^ (i - p.log2)) else z

/-! ## `gfMul` -/

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)

@[simp] theorem arith_xor (a b : ℕ) : RAM.arithmeticValue .xor a b = Nat.xor a b := rfl

/-- `Z := binaryMul X Y` by `W` shift-and-add iterations (needs `Y < 2^W`).
Reads `g+3 (W), g+6 (X), g+7 (Y)`; writes only `g+8 .. g+14`, result in `g+8`. -/
def gfMul (g : ℕ) : Cmd :=
  seqs [lit (g + 8) 0, cp (g + 9) (g + 6), cp (g + 10) (g + 7), lit (g + 14) 2,
    forLoop (g + 11) (g + 3) (g + 13) (seqs [ar .mod (g + 12) (g + 10) (g + 14),
       .ifz (g + 12) .skip (ar .xor (g + 8) (g + 8) (g + 9)),
       ar .add (g + 9) (g + 9) (g + 9), ar .div (g + 10) (g + 10) (g + 14)])]

/-- `Z := binaryRem p Z` by a downward scan of `N2` bits (needs `Z < 2^N2`).
Reads `g+0 (p), g+1 (lp), g+2 (P2), g+4 (N2), g+5 (2^N2)`; writes only `g+8 .. g+15`. -/
def gfRem (g : ℕ) : Cmd :=
  seqs [cp (g + 9) (g + 5), cp (g + 10) (g + 4), lit (g + 14) 2,
    forLoop (g + 11) (g + 4) (g + 13) (seqs [lit (g + 13) 1, ar .sub (g + 10) (g + 10) (g + 13),
      ar .div (g + 9) (g + 9) (g + 14), ar .lt (g + 12) (g + 10) (g + 1),
      .ifz (g + 12) (seqs [ar .div (g + 15) (g + 8) (g + 9), ar .mod (g + 15) (g + 15) (g + 14),
        .ifz (g + 15) .skip (seqs [ar .div (g + 15) (g + 9) (g + 2), ar .mul (g + 15) g (g + 15),
          ar .xor (g + 8) (g + 8) (g + 15)])]) .skip])]


/-! ## The field context and `fieldMul` -/

/-- Registers `g .. g+5` hold `p, log2 p, 2^log2 p, W, 2W, 2^(2W)`. -/
def GFCtx (s : HS) (g p W : ℕ) : Prop :=
  s.regs g = p ∧ s.regs (g + 1) = p.log2 ∧ s.regs (g + 2) = 2 ^ p.log2 ∧ s.regs (g + 3) = W ∧
    s.regs (g + 4) = 2 * W ∧ s.regs (g + 5) = 2 ^ (2 * W)

/-- `Z := fieldMul p X Y` (block `g`; writes only `g+8 .. g+15`). -/
def gfField (g : ℕ) : Cmd := .seq (gfMul g) (gfRem g)

/-- Compute the context from `p` (register `g`) and `W` (register `g+3`). Writes only
`g+1, g+2, g+4, g+5` and scratch `g+9 .. g+15`. -/
def gfSetup (g : ℕ) : Cmd :=
  seqs [lit (g + 1) 0, lit (g + 2) 1, cp (g + 9) g, lit (g + 14) 2,
    forLoop (g + 11) (g + 3) (g + 13) (seqs [ar .div (g + 9) (g + 9) (g + 14),
      .ifz (g + 9) .skip (seqs [lit (g + 13) 1, ar .add (g + 1) (g + 1) (g + 13),
        ar .add (g + 2) (g + 2) (g + 2)])]),
    ar .add (g + 4) (g + 3) (g + 3), lit (g + 5) 1,
    forLoop (g + 11) (g + 4) (g + 13) (ar .add (g + 5) (g + 5) (g + 5))]


/-! ## `bitEval` on a digit array -/

/-- The rest of the `bitEval` loop body after the field multiplication. -/
def bevRest (g : ℕ) : List Cmd :=
  [ar .add (g + 21) (g + 17) (g + 18), lit (g + 22) 1, ar .sub (g + 21) (g + 21) (g + 22),
    ar .sub (g + 21) (g + 21) (g + 20), ald (g + 23) (g + 16) (g + 21), ar .xor (g + 19) (g + 8) (g + 23)]

def bevBody (g : ℕ) : Cmd := seqs (cp (g + 6) (g + 19) :: gfField g :: bevRest g)

/-- `E := bitEval Q p K id a`, Horner over the digit array `D` (from offset `off`).
Registers: field context `g .. g+5`, `a` in `g+7`, `D off K` in `g+16 g+17 g+18`, result `g+19`.
Writes only `g+6`, `g+8 .. g+15`, `g+19 .. g+23`. -/
def bitEvalW (g : ℕ) : Cmd := .seq (lit (g + 19) 0) (forLoop (g + 20) (g + 18) (g + 22) (bevBody g))

/-- Registers `bitEvalW` keeps. -/
def BevKeep (g r : ℕ) : Prop := r < g + 6 ∨ r = g + 7 ∨ (g + 16 ≤ r ∧ r < g + 19) ∨ g + 24 ≤ r

end Prog

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor
/-!
# `localColor` on `Cmd` (q379, Part G): setup and neighbour-list facts

Register map of `colorOf` (base `g`, all registers `g .. g+50`; the enumerator `cfg` must
start at `cfg.r0 ≥ g + 51`):
* `g .. g+15` field context and scratch (`RamGF`), `g+16 g+17 g+18 g+19` = `D off K E` of
  `bitEvalW` (`D` is the digit array, `K` is kept there throughout);
* `g+24` `Q`, `g+25` `|x|`, `g+26` `J` (number of neighbours), `g+27` `α`, `g+28` `found`,
  `g+29` `ok`, `g+30` `bitEval(x,a)`, `g+31` `a`, `g+32` `j`, `g+33 g+35` loop `one`s,
  `g+34 g+36 g+38 g+39` scratch, `g+36` the result;
* `g+40 .. g+50` the block of the word utilities.
Arrays: `XA` (a copy of `x`), `DG` (digits: row `0` is `x`, row `m+1` neighbour `m`, stride `K`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The neighbour list -/

/-- The visited words of length `|x|` other than `x`, in visit order with multiplicity. -/
def nbrList {q : ℕ} (t : ℕ) (x : Word q) : List (Word q) :=
  (visits (2 * t) x).filter (fun w => decide (w.length = x.length ∧ w ≠ x))

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

section Init
variable (inp : ℕ → ℕ) (B : ℕ)

def colorInit (q s : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) : Cmd :=
  seqs [gfSetup g,
    seqs [lit (g + 40) (cfg.buf s), lit (g + 41) 0, lit (g + 42) XA, lit (g + 43) 0,
      cp (g + 44) (cfg.lenR s), cp (g + 25) (cfg.lenR s)],
    copyW (g + 40) (g + 41) (g + 42) (g + 43) (g + 44) (g + 45) (g + 46) (g + 47) (g + 48),
    seqs [lit (g + 40) XA, lit (g + 41) 0, cp (g + 42) (g + 25), lit (g + 43) q],
    valueW (g + 40),
    seqs [cp (g + 40) (g + 44), cp (g + 41) (g + 24), cp (g + 42) (g + 18), lit (g + 43) DG,
      lit (g + 44) 0],
    digitsW (g + 40)]

end Init

/-! ## Enumeration: digits of every neighbour -/

section Enum
variable (inp : ℕ → ℕ) (B : ℕ)

def enApp (q : ℕ) (cfg : EnumCfg) (g DG : ℕ) : Cmd :=
  seqs [seqs [lit (g + 40) cfg.vis, lit (g + 41) 0, cp (g + 42) (g + 25), lit (g + 43) q],
    valueW (g + 40),
    seqs [cp (g + 40) (g + 44), cp (g + 41) (g + 24), cp (g + 42) (g + 18), lit (g + 43) DG,
      lit (g + 34) 1, ar .add (g + 34) (g + 26) (g + 34), ar .mul (g + 44) (g + 34) (g + 18)],
    digitsW (g + 40),
    seqs [lit (g + 34) 1, ar .add (g + 26) (g + 26) (g + 34)]]

def enInner (q : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) : Cmd :=
  .seq (seqs [lit (g + 40) cfg.vis, lit (g + 41) 0, lit (g + 42) XA, lit (g + 43) 0, cp (g + 44) (g + 25)])
    (.seq (eqW (g + 40)) (.ifz (g + 45) (enApp q cfg g DG) .skip))

def enBody (q : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) : Cmd :=
  .seq (seqs [ar .sub (g + 38) cfg.VL (g + 25), ar .sub (g + 39) (g + 25) cfg.VL,
      ar .add (g + 38) (g + 38) (g + 39)])
    (.ifz (g + 38) (enInner q cfg g XA DG) .skip)

/-- Invariant of the enumeration (accumulator: the neighbours found so far). -/
def EnInv {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g DG K Q : ℕ) (x : Word q) (st0 : HS)
    (l : List (Word q)) (st : HS) : Prop :=
  st.regs (g + 26) = l.length ∧ (∀ w ∈ l, w.length = x.length) ∧
  (∀ m (hm : m < l.length), ∀ i < K, st.arr DG ((m + 1) * K + i) = (value l[m] / Q ^ i) % Q) ∧
  (∀ r, r < g + 26 → st.regs r = st0.regs r) ∧
  (∀ r, g + 51 ≤ r → ¬ cfg.ownsReg s r → st.regs r = st0.regs r) ∧
  (∀ y i, y ≠ DG → ¬ cfg.ownsArr s y → st.arr y i = st0.arr y i) ∧
  (∀ i < K, st.arr DG i = st0.arr DG i) ∧ st.cur = st0.cur ∧ st.out = st0.out


def colorEnum (q s : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) : Cmd :=
  .seq (lit (g + 26) 0) (enumScripts q s cfg (enBody q cfg g XA DG))

end Enum

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor2
/-!
# `localColor` on `Cmd` (q379, Part G): the search for the first separating point

Digit array `DG`: row `m` (offset `m * K`) holds the base-`Q` digits of `ids m`, `m ≤ J`.
`okAt … a` says `bitEval` at `a` separates row `0` from every row `j + 1`, `j < J`; the search
computes `α = ((List.range Q).find? okAt).getD 0` with a `found` flag (no early exit).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- `bitEval` at `a` separates row `0` from rows `1 .. J`. -/
def okAt (Q p K : ℕ) (ids : ℕ → ℕ) (J a : ℕ) : Bool :=
  (List.range J).all (fun j => bitEval Q p K (ids 0) a != bitEval Q p K (ids (j + 1)) a)

/-- Digit rows `0 .. J` of `DG` hold the digits of `ids`. -/
def Rows (st : HS) (DG K Q J : ℕ) (ids : ℕ → ℕ) : Prop :=
  ∀ m ≤ J, ∀ i < K, st.arr DG (m * K + i) = (ids m / Q ^ i) % Q

section Search
variable (inp : ℕ → ℕ) (B : ℕ)

def nBody (g : ℕ) : Cmd :=
  seqs [seqs [lit (g + 34) 1, ar .add (g + 34) (g + 32) (g + 34), ar .mul (g + 17) (g + 34) (g + 18)],
    bitEvalW g,
    seqs [ar .sub (g + 34) (g + 30) (g + 19), ar .sub (g + 36) (g + 19) (g + 30),
      ar .add (g + 34) (g + 34) (g + 36), .ifz (g + 34) (lit (g + 29) 0) .skip]]

/-- Registers kept by the neighbour loop. -/
def KeepN (g r : ℕ) : Prop :=
  r < g + 6 ∨ r = g + 7 ∨ r = g + 16 ∨ r = g + 18 ∨ (g + 24 ≤ r ∧ r ≤ g + 28) ∨ r = g + 30 ∨
    r = g + 31 ∨ r = g + 33 ∨ g + 37 ≤ r


def sBody (g : ℕ) : Cmd :=
  seqs [seqs [cp (g + 7) (g + 31), lit (g + 17) 0], bitEvalW g, seqs [cp (g + 30) (g + 19), lit (g + 29) 1],
    forLoop (g + 32) (g + 26) (g + 35) (nBody g),
    .ifz (g + 28) (.ifz (g + 29) .skip (seqs [lit (g + 28) 1, cp (g + 27) (g + 31)])) .skip]

/-- The search for `α` over `a < Q` (register `g+24`). -/
def colorSearch (g : ℕ) : Cmd :=
  seqs [lit (g + 27) 0, lit (g + 28) 0, forLoop (g + 31) (g + 24) (g + 33) (sBody g)]

/-- Registers kept by the search. -/
def KeepS (g r : ℕ) : Prop :=
  r < g + 6 ∨ r = g + 16 ∨ r = g + 18 ∨ (g + 24 ≤ r ∧ r ≤ g + 26) ∨ g + 37 ≤ r

end Search

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor3
/-!
# `colorOf`: the program computing `localColor t P p x` (q379, Part G)

Main theorem `colorOf_spec`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- Identifiers of the digit rows: row `0` is `x`, row `m + 1` the `m`-th neighbour. -/
def rowIds {q : ℕ} (t : ℕ) (x : Word q) : ℕ → ℕ
  | 0 => value x
  | m + 1 => value ((nbrList t x).getD m [])

section Out
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `C := Q * α + bitEval(x, α)` into `g+36`. -/
def colorOut (g : ℕ) : Cmd :=
  seqs [seqs [cp (g + 7) (g + 27), lit (g + 17) 0], bitEvalW g,
    seqs [ar .mul (g + 36) (g + 24) (g + 27), ar .add (g + 36) (g + 36) (g + 19)]]

/-- The full `colorOf` program. Static parameters: alphabet `q`, `t`, the enumerator `cfg`,
the register base `g`, the arrays `XA` and `DG`. -/
def colorOf (q t : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) : Cmd :=
  seqs [colorInit q (2 * t) cfg g XA DG, colorEnum q (2 * t) cfg g XA DG, lit (g + 16) DG,
    colorSearch g, colorOut g]

end Out

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The cost bound of `colorOf_spec`. -/
def colorOfCost (B q t L K Q W Vb Ms Mb : ℕ) (cfg : EnumCfg) : ℕ :=
  (Vb + 1) * ((19 * L + 7 * K + 40) * kappa B (RAM.bits Mb) + cfg.enumE B q L (2 * t)) +
    ((Q + 1) * (Vb + 1) * (K * (36 * W + 24) + 15) + 16 * W + 3 * Q + 18) * kappa B (RAM.bits Ms)

/-- Uniform bound on the number of visited words, for words of length `L`. -/
def visBound (q t L : ℕ) : ℕ := ∑ i ∈ Finset.range (2 * t + 1), (2 * q * (L + 2 * t + 1)) ^ i

/-! ## The program -/

def cApp (q t : ℕ) (cfg1 cfg2 : EnumCfg) (g XA DG CLA : ℕ) : Cmd :=
  seqs [seqs [lit (g + 54) cfg1.vis, lit (g + 55) 0, lit (g + 56) (cfg2.buf (2 * t)), lit (g + 57) 0,
      cp (g + 58) (g + 53)],
    copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61) (g + 62),
    cp (cfg2.lenR (2 * t)) (g + 53),
    colorOf q t cfg2 g XA DG,
    seqs [lit (g + 54) CLA, ast (g + 54) (g + 52) (g + 36), lit (g + 67) 1,
      ar .add (g + 52) (g + 52) (g + 67)]]

def cInner (q t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) : Cmd :=
  .seq (seqs [lit (g + 54) cfg1.vis, lit (g + 55) 0, lit (g + 56) X2, lit (g + 57) 0, cp (g + 58) (g + 53)])
    (.seq (eqW (g + 54)) (.ifz (g + 59) (cApp q t cfg1 cfg2 g XA DG CLA) .skip))

def cBody (q t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) : Cmd :=
  .seq (seqs [ar .sub (g + 65) cfg1.VL (g + 53), ar .sub (g + 66) (g + 53) cfg1.VL,
      ar .add (g + 65) (g + 65) (g + 66)])
    (.ifz (g + 65) (cInner q t cfg1 cfg2 g X2 XA DG CLA) .skip)

/-- Invariant of the outer enumeration. -/
def CAInv {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g XA DG CLA p Q K : ℕ) (x : Word q) (st0 : HS)
    (l : List (Word q)) (st : HS) : Prop :=
  st.regs (g + 52) = l.length ∧ (∀ w ∈ l, w.length = x.length) ∧
  (∀ m (hm : m < l.length), ∀ P : Parameters, P.Q = Q → P.K = K →
    st.arr CLA m = localColor t P p l[m]) ∧
  (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ r = g + 51 ∨ r = g + 53 ∨ cfg1.r0 ≤ r) →
    ¬ cfg1.ownsReg (2 * t) r → st.regs r = st0.regs r) ∧
  (∀ y i, y ≠ XA → y ≠ DG → y ≠ CLA → ¬ cfg2.ownsArr (2 * t) y → ¬ cfg1.ownsArr (2 * t) y →
    st.arr y i = st0.arr y i) ∧
  st.cur = st0.cur ∧ st.out = st0.out


section Body
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Placement hypotheses of `colorsAll`. -/
structure CAPlace (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) : Prop where
  r2 : g + 68 ≤ cfg2.r0
  r12 : cfg2.r0 + 19 + 6 * t ≤ cfg1.r0
  a12 : cfg2.a0 + 2 + 2 * t ≤ cfg1.a0
  hX2 : X2 < cfg2.a0
  hXA : XA < cfg2.a0
  hDG : DG < cfg2.a0
  hCL : CLA < cfg2.a0
  d1 : X2 ≠ XA
  d2 : X2 ≠ DG
  d3 : X2 ≠ CLA
  d4 : XA ≠ DG
  d5 : XA ≠ CLA
  d6 : DG ≠ CLA

/-- A generic `Parameters` with the given `Q` and `K`. -/
def parQK (Q K : ℕ) : Parameters := ⟨0, K, Q, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩


/-- **`colorsAll`** (see the module doc). -/
def colorsAll (q t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) : Cmd :=
  seqs [seqs [lit (g + 54) (cfg1.buf (2 * t)), lit (g + 55) 0, lit (g + 56) X2, lit (g + 57) 0,
      cp (g + 58) (cfg1.lenR (2 * t)), cp (g + 53) (cfg1.lenR (2 * t))],
    copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61) (g + 62),
    seqs [lit (g + 56) (cfg2.buf (2 * t)), cp (cfg2.lenR (2 * t)) (g + 53)],
    copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61) (g + 62),
    colorOf q t cfg2 g XA DG,
    seqs [cp (g + 51) (g + 36), lit (g + 52) 0],
    enumScripts q (2 * t) cfg1 (cBody q t cfg1 cfg2 g X2 XA DG CLA)]

end Body

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode
/-!
# The decoder, part 1: good-index test, good-index count, writing `repr` (q379, Part D)

* `goodW r piR cxR vR CL`: `regs r := 1` iff `cx % pi ≠ CL[ℓ] % pi` for all `ℓ < V`
  (`pi = regs piR`, `cx = regs cxR`, `V = regs vR`); writes only `r .. r+7`.
* `countW r iR prR piR cxR vR CL`: `regs r := #{i' < regs iR : goodW-test with pi = PR[i']}`;
  writes only `r .. r+3`, `piR`, and the `goodW` block `r+4 .. r+11`.
* `reprOut r vR wR offR X qR`: writes `repr q w v` into array `X` at offset `off`;
  writes only `r .. r+6`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Dec1
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## The good-index test -/

/-- The predicate computed by `goodW`. -/
def goodP (cx pi : ℕ) (cl : ℕ → ℕ) (V : ℕ) : Bool :=
  (List.range V).all (fun ℓ => decide (cx % pi ≠ cl ℓ % pi))

def goodBody (r piR : ℕ) : Cmd :=
  seqs [ald (r + 5) (r + 2) (r + 3), ar .mod (r + 5) (r + 5) piR,
      ar .sub (r + 6) (r + 5) (r + 1), ar .sub (r + 7) (r + 1) (r + 5), ar .add (r + 6) (r + 6) (r + 7),
      .ifz (r + 6) (lit r 0) .skip]

def goodW (r piR cxR vR CL : ℕ) : Cmd :=
  .seq (seqs [lit r 1, ar .mod (r + 1) cxR piR, lit (r + 2) CL])
    (forLoop (r + 3) vR (r + 4) (goodBody r piR))

/-! ## Counting the good indices below `i` -/

def countGood (cx : ℕ) (pr cl : ℕ → ℕ) (V I : ℕ) : ℕ :=
  ((List.range I).filter (fun i' => goodP cx (pr i') cl V)).length

def countW (r iR prR piR cxR vR CL : ℕ) : Cmd :=
  .seq (lit r 0) (forLoop (r + 1) iR (r + 2)
    (seqs [ald piR prR (r + 1), goodW (r + 4) piR cxR vR CL, ar .add r r (r + 4)]))

/-! ## Writing `repr q w v` into an array -/

def reprBody (r qR : ℕ) : Cmd :=
  seqs [ar .sub (r + 1) (r + 1) (r + 3), ar .mod (r + 6) r qR, ast (r + 2) (r + 1) (r + 6),
    ar .div r r qR]

def reprOut (r vR wR offR X qR : ℕ) : Cmd :=
  .seq (seqs [cp r vR, ar .add (r + 1) offR wR, lit (r + 2) X, lit (r + 3) 1])
    (forLoop (r + 4) wR (r + 5) (reprBody r qR))

end Dec1

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams
/-!
# Part P (q379): logarithms and powers

Register convention: inputs in arbitrary registers below `S`; outputs at `S`, `S + 1`, …;
scratch above the outputs.  Each program's frame lemma lists the registers it may write.

* `floorLogW b N T S`: `S := Nat.log (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`
  (needs `Nat.log … ≤ regs T`, loop count `regs T`); writes `S .. S+3`.
* `ceilLogW b N T S`: `S := ceilLog (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`; `S .. S+3`.
* `powW a e S`: `S := regs a ^ regs e`; writes only `S`.
* `radW q t lR S`: `S := radiusBound q (2 t) (regs lR)`; writes `S .. S+2`.
* `rhoW q t nR hR qhR S`: `S := shortLength q t (regs hR)`; writes `S .. S+8`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

/-- One step: if `P * b ≤ N` then `P := P * b; c := c + 1`. -/
def floorLogBody (b N S : ℕ) : Cmd :=
  seqs [ar .mul (S + 2) (S + 1) b, ar .lt (S + 3) N (S + 2),
    .ifz (S + 3) (seqs [cp (S + 1) (S + 2), lit (S + 3) 1, ar .add S S (S + 3)]) .skip]

def floorLogW (b N T S : ℕ) : Cmd :=
  seqs [lit S 0, lit (S + 1) 1, .loop T (floorLogBody b N S)]

/-- Ceiling logarithm: after `floorLogW`, if `b ^ c < N` then `c := c + 1`, `P := P * b`. -/
def ceilLogW (b N T S : ℕ) : Cmd :=
  .seq (floorLogW b N T S) (seqs [ar .lt (S + 3) (S + 1) N,
    .ifz (S + 3) .skip (seqs [ar .mul (S + 1) (S + 1) b, lit (S + 3) 1, ar .add S S (S + 3)])])

/-- `S := regs a ^ regs e` by `regs e` multiplications. -/
def powW (a e S : ℕ) : Cmd := .seq (lit S 1) (.loop e (ar .mul S S a))

/-- `S := radiusBound q (2 t) (regs lR)`; writes only `S, S+1, S+2`. -/
def radW (q t lR S : ℕ) : Cmd :=
  .seq (seqs [lit S (2 * t + 1), ar .add S lR S, lit (S + 1) (2 * q), ar .mul S S (S + 1),
    lit (S + 1) (2 * t)]) (.seq (powW S (S + 1) (S + 2)) (seqs [lit (S + 1) (2 * t + 1),
    ar .mul S (S + 2) (S + 1)]))

/-! ### The short length `ρ = shortLength q t h` -/

/-- The defining condition of `shortLength q t h`. -/
def rhoCond (q t h l : ℕ) : Prop := h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l

/-- The test of one candidate: if `flag = 0` (register `S+1`), `¬ (S+2) < (S+6)` and
`¬ (S+4) < h`, then `S := (S+4)`, `flag := 1`. -/
def rhoTest (hR S : ℕ) : Cmd :=
  .ifz (S + 1) (seqs [ar .lt (S + 7) (S + 2) (S + 6), .ifz (S + 7) (seqs [ar .lt (S + 8) (S + 4) hR,
    .ifz (S + 8) (seqs [cp S (S + 4), lit (S + 1) 1]) .skip]) .skip]) .skip

def rhoBody (q t hR qhR S : ℕ) : Cmd :=
  .seq (radW q t (S + 4) (S + 6)) (seqs [ar .mul (S + 6) qhR (S + 6), rhoTest hR S,
    lit (S + 7) q, ar .mul (S + 2) (S + 2) (S + 7)])

/-- `S := shortLength q t (regs hR)` (needs `regs qhR = q ^ regs hR` and a witness `≤ regs nR`),
searching `l = 0 … n` with a found flag (`S+1`) and `S+2 = q ^ l`.  Writes only `S .. S+8`. -/
def rhoW (q t nR hR qhR S : ℕ) : Cmd :=
  .seq (seqs [lit S 0, lit (S + 1) 0, lit (S + 2) 1, lit (S + 3) 1, ar .add (S + 3) nR (S + 3)])
    (forLoop (S + 4) (S + 3) (S + 5) (rhoBody q t hR qhR S))

end Logs

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams2
/-!
# Part P (q379): the prime table

`primesW PR Mc S`: for every `m < regs Mc` (trial division), store the primes in increasing
order into array `regs PR`: afterwards `arr PR i = Nat.nth Nat.Prime i` for all
`i < Nat.count Nat.Prime (regs Mc)`, and register `S` holds that count.
With `regs Mc > (L + 2) * (2 * (Nat.log 2 (L + 2) + 3))` this covers every `i ≤ L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### A Chebyshev bound on the `N`-th prime (copied from the q373 record,
`Solutions/EditMulticoloring/EncoderRedundancyAux1.lean`, `nth_prime_le`). -/

section Primes
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Inner loop body: if `1 < d` and `m % d = 0` then `flag := 0`
(`m` in `S+2`, flag `S+3`, `1` in `S+4`, `d` in `S+5`). -/
def ptBody (S : ℕ) : Cmd :=
  seqs [ar .lt (S + 7) (S + 4) (S + 5),
    .ifz (S + 7) .skip (seqs [ar .mod (S + 8) (S + 2) (S + 5), .ifz (S + 8) (lit (S + 3) 0) .skip])]

/-- `S+3 := if Nat.Prime (regs (S+2)) then 1 else 0`; writes only `S+3 .. S+8`. -/
def primeTest (S : ℕ) : Cmd :=
  .seq (seqs [lit (S + 4) 1, ar .lt (S + 3) (S + 4) (S + 2)])
    (forLoop (S + 5) (S + 2) (S + 6) (ptBody S))

/-- Outer body: test `m` (index `S+2`); if prime, `PR[count] := m; count := count + 1`. -/
def primesBody (PR S : ℕ) : Cmd :=
  .seq (primeTest S) (.ifz (S + 3) .skip (seqs [ast PR S (S + 2), lit (S + 9) 1, ar .add S S (S + 9)]))

/-- The prime table: `S := Nat.count Nat.Prime (regs Mc)` and `arr PR i = Nat.nth Nat.Prime i`
for `i < S`.  Writes only registers `S .. S+9` and those cells. -/
def primesW (PR Mc S : ℕ) : Cmd :=
  .seq (lit S 0) (forLoop (S + 2) Mc (S + 1) (primesBody PR S))

end Primes

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams3
/-!
# Part P (q379): the modulus search

`modTest b p`: no binary polynomial `d` with `2 ≤ d < 2^b` (degree `1 .. b-1`) divides `p`.
`modSearch b`: the first `p ∈ [2^b, 2^(b+1))` passing `modTest b`, else `0`.

`modulusW bR S` computes `S := modSearch (regs bR)` by two nested loops of `2^b` iterations
around `gfSetup` / `gfRem` (block `g = S + 10`).  Writes only registers `S .. S+25`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

def modTest (b p : ℕ) : Bool := (List.range (2^b)).all (fun d => d < 2 || binaryRem d p != 0)

def modSearch (b : ℕ) : ℕ := ((List.range (2^b)).map (· + 2^b)).find? (modTest b) |>.getD 0

section Modulus
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Inner body (`d` in `S+7`, `p` in `S+3`, flag `S+4`, `W` in `S+13 = g+3`):
if `1 < d` and `binaryRem d p = 0` then `flag := 0`. -/
def mtBody (S : ℕ) : Cmd :=
  seqs [lit (S + 9) 1, ar .lt (S + 9) (S + 9) (S + 7),
    .ifz (S + 9) .skip (seqs [cp (S + 10) (S + 7), gfSetup (S + 10), cp (S + 18) (S + 3),
      gfRem (S + 10), .ifz (S + 18) (lit (S + 4) 0) .skip])]

/-- `S+4 := if modTest b p then 1 else 0` (`2^b` in `S+2`, `p` in `S+3`, `b+1` in `S+13`). -/
def mtInner (S : ℕ) : Cmd := .seq (lit (S + 4) 1) (forLoop (S + 7) (S + 2) (S + 8) (mtBody S))

/-- The outer body (candidate index `i` in `S+5`): `p := i + 2^b`; test; record the first. -/
def moBody (S : ℕ) : Cmd :=
  seqs [ar .add (S + 3) (S + 5) (S + 2), mtInner S,
    .ifz (S + 1) (.ifz (S + 4) .skip (seqs [cp S (S + 3), lit (S + 1) 1])) .skip]

/-- `S := modSearch (regs bR)`.  Writes only registers `S .. S+25`. -/
def modulusW (bR S : ℕ) : Cmd :=
  .seq (seqs [lit S 0, lit (S + 1) 0, lit (S + 9) 2, powW (S + 9) bR (S + 2), lit (S + 9) 1,
    ar .add (S + 13) bR (S + 9)]) (forLoop (S + 5) (S + 2) (S + 6) (moBody S))

/-- The first `i` candidates of `modSearch`. -/
def modFind (b i : ℕ) : Option ℕ := ((List.range i).map (· + 2 ^ b)).find? (modTest b)

end Modulus

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams4
/-!
# Part P (q379): the parameters, part A (`r, K, b, Q, B, L, W`) and part F (`f, J, h₁`)

Output block `O`: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1,
O+7 f = floorLog q (L / 2), O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ,
O+15 m, O+16 k`; temporaries `O+17 .. O+22`; subroutine scratch from `O+23` (to `O+48`).
Here `b = ceilLog 2 (r * K + 1)` (so `Q = 2 ^ b`, `B = 2 b`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The (explicit) data bound needed by part A. -/
noncomputable def pABound (q t n : ℕ) : ℕ :=
  radiusBound q (2 * t) n + 2 * q * (n + 2 * t + 1) + 2 * q + 2 * t + n + ceilLog 2 q +
    (parameters q t n).K + 5 * ((parameters q t n).r * (parameters q t n).K + 3) +
    (parameters q t n).L + (parameters q t n).Q + 10

section PartA
variable (inp : ℕ → ℕ) (B : ℕ)

def pA (q t nR O : ℕ) : Cmd :=
  .seq (radW q t nR (O + 23)) (.seq (seqs [cp O (O + 23), lit (O + 17) (ceilLog 2 q),
    ar .mul (O + 1) nR (O + 17), ar .mul (O + 18) O (O + 1), lit (O + 17) 1,
    ar .add (O + 18) (O + 18) (O + 17), lit (O + 17) 2])
   (.seq (ceilLogW (O + 17) (O + 18) (O + 18) (O + 23)) (.seq (seqs [cp (O + 2) (O + 23), cp (O + 3) (O + 24), ar .add (O + 4) (O + 2) (O + 2),
    lit (O + 17) 1, ar .add (O + 6) (O + 2) (O + 17)])
    (seqs [ar .add (O + 18) O (O + 17), ar .add (O + 19) (O + 4) (O + 17),
    ar .mul (O + 18) (O + 18) (O + 19), lit (O + 17) 4, ar .mul (O + 5) (O + 17) (O + 18)]))))

end PartA

section PartF
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Part F: `O+7 := Nat.log q (L / 2)`, `O+8 := q ^ (O+7)` (`= J`), `O+9 := ceilLog q L`
(`L` in `O+5`). -/
def pF (q O : ℕ) : Cmd :=
  .seq (seqs [lit (O + 17) q, lit (O + 19) 2, ar .div (O + 18) (O + 5) (O + 19)])
  (.seq (floorLogW (O + 17) (O + 18) (O + 18) (O + 23))
  (.seq (seqs [cp (O + 7) (O + 23), cp (O + 8) (O + 24)])
  (.seq (ceilLogW (O + 17) (O + 5) (O + 5) (O + 23)) (cp (O + 9) (O + 23)))))

end PartF

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams5
/-!
# Part P (q379): the parameters, part P (prime table, `h₂`, `h`) and part R (`q^h, ρ, q^ρ, m, k`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The number of trial-division candidates for the prime table of length `L + 1`. -/
def primeBound (L : ℕ) : ℕ := (L + 2) * (2 * (Nat.log 2 (L + 2) + 3)) + 1

section PartP
variable (inp : ℕ → ℕ) (B : ℕ)

def pPrime (q PR O : ℕ) : Cmd :=
  .seq (seqs [lit (O + 17) 2, lit (O + 19) 2, ar .add (O + 18) (O + 5) (O + 19)])
  (.seq (floorLogW (O + 17) (O + 18) (O + 18) (O + 23))
  (.seq (seqs [lit (O + 19) 3, ar .add (O + 19) (O + 23) (O + 19), ar .add (O + 19) (O + 19) (O + 19),
     ar .mul (O + 18) (O + 18) (O + 19), lit (O + 19) 1, ar .add (O + 18) (O + 18) (O + 19)])
  (.seq (primesW PR (O + 18) (O + 23))
  (.seq (seqs [lit (O + 19) 1, ar .sub (O + 18) (O + 5) (O + 19), ald (O + 18) PR (O + 18),
     lit (O + 17) q])
  (.seq (ceilLogW (O + 17) (O + 18) (O + 18) (O + 23))
   (seqs [cp (O + 10) (O + 23), ar .add (O + 11) (O + 9) (O + 10)]))))))

end PartP

/-- The data bound needed by part R. -/
def pRBound (q t n hv fv : ℕ) : ℕ :=
  q ^ (n + 1) + 2 * (q ^ hv * radiusBound q (2 * t) n) + 2 * q * (n + 2 * t + 1) + 2 * q + 2 * t +
    hv + n + 4 + q ^ hv + fv

section PartR
variable (inp : ℕ → ℕ) (B : ℕ)

/-- Part R: `O+12 := q ^ h`, `O+13 := ρ`, `O+14 := q ^ ρ`, `O+15 := n - ρ`, `O+16 := (O+15) + f`
(`h` in `O+11`, `f` in `O+7`, `n` in `nR`). -/
def pR (q t nR O : ℕ) : Cmd :=
  .seq (lit (O + 17) q)
  (.seq (powW (O + 17) (O + 11) (O + 23))
  (.seq (cp (O + 12) (O + 23))
  (.seq (rhoW q t nR (O + 11) (O + 12) (O + 23))
  (.seq (cp (O + 13) (O + 23))
  (.seq (powW (O + 17) (O + 13) (O + 23))
  (seqs [cp (O + 14) (O + 23), ar .sub (O + 15) nR (O + 13), ar .add (O + 16) (O + 15) (O + 7)]))))))

end PartR

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams6
/-!
# Part P (q379): `paramsW`, all fields of `parameters q t n`

`paramsW q t nR PR O` (with `nR, PR < O`, `n = regs nR`, `regs PR` an array id) leaves
`ParamsAt s' O q t n` (layout below), fills the prime table `arr (regs PR) i = primeAt i` for
`i ≤ L`, and writes only registers in `[O, O + 49)`.

Layout: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1, O+7 f = Nat.log q (L / 2),
O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ, O+15 m, O+16 k`,
where `b = ceilLog 2 (r * K + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The registers `O .. O+16` hold the parameters (see the module docstring). -/
structure ParamsAt (s : HS) (O q t n : ℕ) : Prop where
  hr : s.regs O = (parameters q t n).r
  hK : s.regs (O + 1) = (parameters q t n).K
  hb : s.regs (O + 2) = ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)
  hQ : s.regs (O + 3) = (parameters q t n).Q
  hB : s.regs (O + 4) = (parameters q t n).B
  hL : s.regs (O + 5) = (parameters q t n).L
  hW : s.regs (O + 6) = ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1
  hf : s.regs (O + 7) = Nat.log q ((parameters q t n).L / 2)
  hJ : s.regs (O + 8) = (parameters q t n).J
  hh₁ : s.regs (O + 9) = (parameters q t n).h₁
  hh₂ : s.regs (O + 10) = (parameters q t n).h₂
  hh : s.regs (O + 11) = (parameters q t n).h
  hqh : s.regs (O + 12) = q ^ (parameters q t n).h
  hρ : s.regs (O + 13) = (parameters q t n).ρ
  hqρ : s.regs (O + 14) = q ^ (parameters q t n).ρ
  hm : s.regs (O + 15) = (parameters q t n).m
  hk : s.regs (O + 16) = (parameters q t n).k

/-- The data bound for `paramsW` (`x` = the prime-table array id). -/
noncomputable def paramsBound (q t n x : ℕ) : ℕ :=
  pABound q t n + (((parameters q t n).L + 2) * (q + 1) + (parameters q t n).L) +
    ((primeBound (parameters q t n).L + 2) * (q + 1) + x + 3 * primeBound (parameters q t n).L +
      (parameters q t n).h₁ + 10) +
    pRBound q t n (parameters q t n).h (Nat.log q ((parameters q t n).L / 2))

/-- The cost factor of `paramsW` (to be multiplied by `kappa B (RAM.bits M)`). -/
noncomputable def paramsCost (q t n : ℕ) : ℕ :=
  (7 * ((parameters q t n).r * (parameters q t n).K + 1) + 4 * t + 40) +
    (11 * (parameters q t n).L + 19) +
    ((8 * primeBound (parameters q t n).L + 13) * (primeBound (parameters q t n).L + 1) +
      14 * primeBound (parameters q t n).L + 40) +
    ((4 * t + 24) * (n + 1) + 2 * (parameters q t n).h + 2 * n + 20)

/-! ### Size bounds of the outputs -/

section Params
variable (inp : ℕ → ℕ) (B : ℕ)

def paramsW (q t nR PR O : ℕ) : Cmd :=
  .seq (pA q t nR O) (.seq (pF q O) (.seq (pPrime q PR O) (pR q t nR O)))

end Params

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode2
/-!
# The decoder, part 2: semantics, layout, frames, and the last levels of the candidate test
(q379, Part D)

Layout of the decoder (constant registers / arrays; `t`-dependent ones are functions of `t`):
* registers `0` = n, `1` = 1 (the prime-table array id), `2` = done flag (`decFlag`),
  `3` = q^h₂, `4` = q, `100 .. 116` the parameters (`ParamsAt _ 100`), `200 .. 299` scratch of
  the candidate test, `400 ..` the `colorsAll` block (`g = 400`: `400` = p, `403` = W, `418` = K,
  `424` = Q), enumerators `dC2c` (`r0 = 470`), `dC1 t` (`r0 = 490 + 6t`), `dC0 t` (`r0 = 510 + 12t`);
* arrays `1` the prime table, `2` the result, `3 4 5 6` = `X2 XA DG CLA` of `colorsAll`, `10 ..`
  enumerator arrays, `dINV t = 18 + 5t` the inverse table of the short code.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Semantics of `validate` and `decode` -/

noncomputable def vTail {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) (i η : ℕ) :
    Option (Word q) :=
  if !(localGood t P p x i) ∨ η ≠ localColor t P p x % primeAt i then none else
    if ((List.range i).filter (localGood t P p x)).length ≥ P.J then none
    else some (x ++ Code.repr q (P.k - P.m) ((List.range i).filter (localGood t P p x)).length)

noncomputable def vMid {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) (i η : ℕ) :
    Option (Word q) :=
  if i ≥ P.L ∨ η ≥ primeAt i then none else vTail t P p x i η

/-! ## Layout -/

def dC0 (t : ℕ) : EnumCfg := ⟨510 + 12 * t, 14 + 4 * t⟩
def dC1 (t : ℕ) : EnumCfg := ⟨490 + 6 * t, 12 + 2 * t⟩
def dC2c : EnumCfg := ⟨470, 10⟩
def dINV (t : ℕ) : ℕ := 18 + 5 * t

/-- Registers the candidate test never changes. -/
def KeptR (t r : ℕ) : Prop :=
  (r < 200 ∧ r ≠ 2) ∨ r = 400 ∨ r = 403 ∨ r = 418 ∨ r = 424 ∨ 510 + 12 * t ≤ r

/-- Arrays the candidate test never changes. -/
def KeptA (t y : ℕ) : Prop := y = 1 ∨ 14 + 4 * t ≤ y

def SFr (t : ℕ) (st st' : HS) : Prop :=
  (∀ r, KeptR t r → st'.regs r = st.regs r) ∧ (∀ y i, KeptA t y → st'.arr y i = st.arr y i) ∧
  st'.cur = st.cur ∧ st'.out = st.out

/-- The outcome of a candidate test: the frame, and the done flag / result array. -/
def DOut {q : ℕ} (t : ℕ) (st st' : HS) (res : Option (Word q)) : Prop :=
  SFr t st st' ∧ (res = none → st'.regs 2 = st.regs 2) ∧
  (∀ r, res = some r → st'.regs 2 = 1 ∧ WordAt st' 2 0 r)

/-- The context the candidate test relies on (all in kept registers / arrays). -/
structure DCtx (q t n p : ℕ) (st : HS) : Prop where
  n0 : st.regs 0 = n
  pr1 : st.regs 1 = 1
  qh2 : st.regs 3 = q ^ (parameters q t n).h₂
  q4 : st.regs 4 = q
  par : ParamsAt st 100 q t n
  g0 : st.regs 400 = p
  g3 : st.regs 403 = ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1
  g18 : st.regs 418 = (parameters q t n).K
  g24 : st.regs 424 = (parameters q t n).Q
  prt : ∀ i ≤ (parameters q t n).L, st.arr 1 i = primeAt i
  inv : ∀ z : Word q, z.length = (parameters q t n).ρ →
    shortInverse t (parameters q t n).h z =
      if st.arr (dINV t) (value z) ≠ 0 ∧ st.arr (dINV t) (value z) - 1 < q ^ (parameters q t n).h
      then some (Code.repr q (parameters q t n).h (st.arr (dINV t) (value z) - 1)) else none
  invb : ∀ u < q ^ (parameters q t n).ρ, st.arr (dINV t) u ≤ q ^ (parameters q t n).ρ

/-! ## Size bounds -/

/-- The bound for the number of visits around `x` (length `m`). -/
noncomputable def dVb (q t n : ℕ) : ℕ := visBound q t (parameters q t n).m

noncomputable def dW (q t n : ℕ) : ℕ :=
  ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1

noncomputable def dTW (q t n : ℕ) : ℕ := 2 ^ dW q t n

/-- The data bound of the candidate test. -/
noncomputable def DM (q t n : ℕ) : ℕ :=
  4 * q ^ n + 2 * q ^ (parameters q t n).h + 2 * ((parameters q t n).Q * (parameters q t n).Q) +
    2 * dTW q t n + primeBound (parameters q t n).L + dVb q t n + (parameters q t n).L + 4 * n +
    (parameters q t n).k + 2 * q + 100 * t + 1000

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Level 8: store the result `x ++ repr q (k - m) j` and set the done flag -/

def pC8 (t : ℕ) : Cmd :=
  seqs [seqs [lit 220 (dC0 t).a0, lit 221 0, lit 222 2, lit 223 0, cp 224 115],
    copyW 220 221 222 223 224 225 226 227 228, ar .sub 253 116 115, reprOut 255 240 253 115 2 4,
    lit 2 1]

/-! ## Level 7: count the good indices below `i`, compare with `J`, store -/

def pC7 (t : ℕ) : Cmd :=
  seqs [countW 240 213 1 252 451 452 6, ar .lt 212 240 108, .ifz 212 .skip (pC8 t)]

/-! ## Level 6: compare `η` with the colour of `x` modulo `primeAt i` -/

def pC6 (t : ℕ) : Cmd :=
  .seq (seqs [ar .mod 216 451 215, ar .sub 217 216 214, ar .sub 218 214 216, ar .add 217 217 218])
    (.ifz 217 (pC7 t) .skip)

/-- The result of levels 7-8. -/
noncomputable def r7 {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) (i : ℕ) : Option (Word q) :=
  if ((List.range i).filter (localGood t P p x)).length ≥ P.J then none
  else some (x ++ Code.repr q (P.k - P.m) ((List.range i).filter (localGood t P p x)).length)

/-! ## Level 5: the colours (`colorsAll`), the test `localGood x i` -/

noncomputable def dMs (q t n : ℕ) : ℕ :=
  dTW q t n * 2 ^ (2 * dW q t n) + 6 * 2 ^ (2 * dW q t n) + 5 + (dVb q t n + 2) * (parameters q t n).K +
    dVb q t n

noncomputable def dMb (q t n : ℕ) : ℕ :=
  q ^ (parameters q t n).m + 2 * q + 2 * (12 + 2 * t) + 2 * t + 3 + 4 + 5 + 6 +
    2 * (parameters q t n).m + (parameters q t n).Q + (dVb q t n + 1) * (parameters q t n).K +
    dVb q t n + 2 * 2 ^ (2 * dW q t n) + 2

/-- The cost bound of `colorsAll` in the decoder. -/
noncomputable def caCost (q t n B : ℕ) : ℕ :=
  (dVb q t n + 1) * (colorOfCost B q t (parameters q t n).m (parameters q t n).K (parameters q t n).Q
      (dW q t n) (dVb q t n) (dMs q t n) (dMb q t n) dC2c +
    (19 * (parameters q t n).m + 40) * kappa B (RAM.bits (dMb q t n)) +
    (dC1 t).enumE B q (parameters q t n).m (2 * t))

def pC5 (q t : ℕ) : Cmd :=
  seqs [seqs [lit 220 (dC0 t).a0, lit 221 0, lit 222 (13 + 4 * t), lit 223 0, cp 224 115],
    copyW 220 221 222 223 224 225 226 227 228, cp (508 + 12 * t) 115,
    colorsAll q t (dC1 t) dC2c 400 3 4 5 6, goodW 230 215 451 452 6, .ifz 230 .skip (pC6 t)]

/-! ## Level 4: `pi := PR[i]`, test `η < pi` -/

def pC4 (q t : ℕ) : Cmd :=
  .seq (seqs [ald 215 1 213, ar .lt 212 214 215]) (.ifz 212 .skip (pC5 q t))

/-- The hypotheses shared by the levels 2-5. -/
structure DHyp (q t n p : ℕ) : Prop where
  hq : 2 ≤ q
  H3 : (parameters q t n).m + (parameters q t n).ρ = n
  hcol : ∀ y : Word q, localColor t (parameters q t n) p y <
    (parameters q t n).Q * (parameters q t n).Q + dTW q t n
  hp : p ≠ 0
  hpW : p < dTW q t n
  hQ0 : 0 < (parameters q t n).Q
  hQW : (parameters q t n).Q ≤ dTW q t n

/-! ## Level 3: `i := idx / q^h₂`, `η := idx % q^h₂`, test `i < L` -/

def pC3 (q t : ℕ) : Cmd :=
  .seq (seqs [ar .div 213 211 3, ar .mod 214 211 3, ar .lt 212 213 105]) (.ifz 212 .skip (pC4 q t))

/-! ## Level 2: `idx := INV - 1`, test `idx < q^h` -/

def pC2 (q t : ℕ) : Cmd :=
  .seq (seqs [lit 217 1, ar .sub 211 210 217, ar .lt 212 211 112]) (.ifz 212 .skip (pC3 q t))

/-! ## The candidate test: value of the tail, `INV` lookup -/

def pCand (q t : ℕ) : Cmd :=
  .seq (seqs [seqs [lit 200 (14 + 4 * t), cp 201 115, cp 202 113, cp 203 4], valueW 200,
      seqs [lit 216 (dINV t), ald 210 216 204]]) (.ifz 210 .skip (pC2 q t))

/-- The split of a short-code index into the palette pair. -/
def SplitOK (q t n : ℕ) : Prop :=
  ∀ idx < q ^ (parameters q t n).h,
    value ((Code.repr q (parameters q t n).h idx).take (parameters q t n).h₁) =
        idx / q ^ (parameters q t n).h₂ ∧
      value ((Code.repr q (parameters q t n).h idx).drop (parameters q t n).h₁) =
        idx % q ^ (parameters q t n).h₂

end Levels

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode3
/-!
# The decoder, part 3: the enumeration body and the enumeration (q379, Part D)

`pBody q t` is the body run by the scripts enumerator `dC0 t` (depth `t`) on every visited word
`w`: if the done flag (register `2`) is clear and `|w| = n`, it runs the candidate test, which
stores `validate t n p w` (when it is `some`) in array `2` and sets the flag.
`decEnum_spec`: after the enumeration, the flag / array `2` hold
`((scripts t z).map Prod.snd).findSome? (validate t n p)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The invariant of the enumeration. -/
def DInv (q t n p : ℕ) (a : Option (Word q)) (st : HS) : Prop :=
  DCtx q t n p st ∧ st.out = [] ∧
  ((a = none ∧ st.regs 2 = 0) ∨
    (∃ r, a = some r ∧ st.regs 2 = 1 ∧ WordAt st 2 0 r ∧ r.length = (parameters q t n).k))

section Body
variable (inp : ℕ → ℕ) (B : ℕ)

def pIn (q t : ℕ) : Cmd :=
  .seq (seqs [ar .sub 262 (510 + 12 * t) 0, ar .sub 263 0 (510 + 12 * t), ar .add 262 262 263])
    (.ifz 262 (pCand q t) .skip)

def pBody (q t : ℕ) : Cmd := .ifz 2 (pIn q t) .skip

/-- The per-candidate cost bound. -/
noncomputable def dBodyCost (q t n B : ℕ) : ℕ :=
  ((11 * dVb q t n + 11) * (parameters q t n).L + 21 * n + 7 * (parameters q t n).k +
    11 * dVb q t n + 110) * kappa B (RAM.bits (DM q t n)) + caCost q t n B

end Body

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncodeS1
/-! Verbatim copy of `RamShort.lean` (q379, Part S) in namespace `EditMulticoloring.Dev.Ram.EncS`:
the original clashes with `RamColor` on the names `value_lt` and `visBound`, so the two chains
cannot be imported together; the encoder uses this copy. -/

/-!
# Short table, part 1: words, values, representations, greedy (q379, Part S)

* `value_cons`, `value_lt`, `value_inj` — `value` is a bijection from words of length `l`
  onto `[0, q^l)`;
* `repr_length`, `repr_getElem`, `value_repr`, `repr_value` — `Code.repr q l` is its inverse;
* `words_eq` — `words q l = (List.range (q^l)).map (Code.repr q l)`;
* `greedy` facts: sublist of the input, no duplicates, lengths;
* the RAM routine `reprW` writing the digits of a number (`repr`) into an array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## `value` -/

/-! ## `repr` -/

/-! ## `words` -/

/-! ## `greedy` -/

/-- One step of `greedy`. -/
def greedyStep {q : ℕ} (t : ℕ) (chosen : List (Word q)) (x : Word q) : List (Word q) :=
  if chosen.any (fun z => decide (x ∈ ball (2 * t) z)) then chosen else chosen ++ [x]

/-! ## Writing the digits of a number -/

section Repr
variable (inp : ℕ → ℕ) (B : ℕ)

/-- With registers `r .. r+7`: `X V P n Q j d one`, where `P = Q ^ n` on entry.
`arr X i := (V / Q ^ (n - 1 - i)) % Q` for `i < n` (the digits of `repr`).
Writes only `r+2, r+5, r+6, r+7` and the cells `arr X i`, `i < n`. -/
def reprW (r : ℕ) : Cmd :=
  forLoop (r + 5) (r + 3) (r + 7) (seqs [ar .div (r + 2) (r + 2) (r + 4),
    ar .div (r + 6) (r + 1) (r + 2), ar .mod (r + 6) (r + 6) (r + 4), ast r (r + 5) (r + 6)])

end Repr

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS2
/-!
# Short table, part 2: marking a ball (q379, Part S)

`markBody q r a` is the enumerator body: if the visited word has length `ρ` (register `r`),
set `MARK[value w] := 1` (array id in register `r + 7`, equal to `a + 1`).
`markEnum_spec`: running the enumerator of depth `2t` with this body on a word `x` of length `ρ`
turns the mark predicate "in a ball around `chosen`" into "in a ball around `chosen ++ [x]`".

Layout (relative to `r`, `a`): registers `r` = ρ, `r+5`, `r+9` scratch, `r+7` = `a+1`,
`r+20 .. r+28` the `valueW` block, `r+30 ..` the enumerator (`shortCfg r a = ⟨r+30, a+3⟩`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-- The enumerator configuration of the short-table program. -/
def shortCfg (r a : ℕ) : EnumCfg := ⟨r + 30, a + 3⟩

/-- The uniform data bound of the short-table program. -/
def shortM (q t ρ a : ℕ) : ℕ := 2 * a + 4 * (ρ + 2 * t + q) + 4 * q ^ ρ + 20

/-- The enumerator body: mark the visited word if it has length `ρ`. -/
def markBody (q r a : ℕ) : Cmd :=
  .seq (seqs [ar .sub (r + 5) (r + 30) r, ar .sub (r + 9) r (r + 30), ar .add (r + 5) (r + 5) (r + 9)])
    (.ifz (r + 5) (.seq (seqs [lit (r + 20) (a + 3), lit (r + 21) 0, cp (r + 22) r, lit (r + 23) q])
      (.seq (valueW (r + 20)) (seqs [lit (r + 9) 1, ast (r + 7) (r + 24) (r + 9)]))) .skip)

/-- The marking invariant during one enumeration: marks are the balls around `chosen` and the
words visited so far (`l`); the rest of the client state is as in `st0`. -/
def MInv {q : ℕ} (t r a ρ : ℕ) (chosen : List (Word q)) (st0 : HS) (l : List (Word q)) (st : HS) :
    Prop :=
  (∀ u < q ^ ρ, st.arr (a + 1) u =
    if (∃ z ∈ chosen, Code.repr q ρ u ∈ ball (2 * t) z) ∨ Code.repr q ρ u ∈ l then 1 else 0) ∧
  (∀ r', r' < r + 20 → r' ≠ r + 5 → r' ≠ r + 9 → st.regs r' = st0.regs r') ∧
  (∀ r', r + 49 + 6 * t ≤ r' → st.regs r' = st0.regs r') ∧
  (∀ y i, y ≠ a + 1 → (y < a + 3 ∨ a + 5 + 2 * t ≤ y) → st.arr y i = st0.arr y i) ∧
  st.cur = st0.cur ∧ st.out = st0.out

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS3
/-!
# Short table, part 3: one step of the greedy scan (q379, Part S)

`mainBody q t r a` processes the word `x = repr q ρ v` (`v` in register `r + 3`): if
`MARK[v] = 0` it appends `v` to the table (`T[cnt] := v`, `INV[v] := cnt + 1`, `cnt += 1`),
writes `x` into the enumerator's input buffer and marks the ball of radius `2t` around `x`.
`mainBody_spec`: the invariant `SInv` follows one step of `greedy` (`greedyStep`).

Registers (relative to `r`): `r` = ρ, `r+1` = q^ρ, `r+2` = cnt, `r+3` = v, `r+4` loop scratch,
`r+5`, `r+9` scratch, `r+6 r+7 r+8` = the array ids `a` (T), `a+1` (MARK), `a+2` (INV),
`r+10 .. r+17` the `reprW` block, `r+20 .. r+28` the `valueW` block, `r+30 .. r+48+6t` the
enumerator; arrays `a+3 .. a+4+2t` belong to the enumerator.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-- Table updates and the set-up of `reprW`. -/
def chooseA (q t r a : ℕ) : Cmd :=
  seqs [ast (r + 6) (r + 2) (r + 3), lit (r + 9) 1, ar .add (r + 5) (r + 2) (r + 9),
    ast (r + 8) (r + 3) (r + 5), cp (r + 2) (r + 5), lit (r + 10) ((shortCfg r a).buf (2 * t)),
    cp (r + 11) (r + 3), cp (r + 12) (r + 1), cp (r + 13) r, lit (r + 14) q]

/-- Choose the current word: update the tables, write the word, mark its ball. -/
def chooseC (q t r a : ℕ) : Cmd :=
  .seq (chooseA q t r a) (.seq (reprW (r + 10))
    (.seq (cp ((shortCfg r a).lenR (2 * t)) r) (enumScripts q (2 * t) (shortCfg r a) (markBody q r a))))

/-- One iteration of the greedy scan. -/
def mainBody (q t r a : ℕ) : Cmd :=
  .seq (ald (r + 5) (r + 7) (r + 3)) (.ifz (r + 5) (chooseC q t r a) .skip)

/-- The scan invariant for the chosen list `chosen`. -/
def SInv {q : ℕ} (t r a ρ : ℕ) (st0 : HS) (chosen : List (Word q)) (st : HS) : Prop :=
  st.regs r = ρ ∧ st.regs (r + 1) = q ^ ρ ∧ st.regs (r + 2) = chosen.length ∧
  st.regs (r + 6) = a ∧ st.regs (r + 7) = a + 1 ∧ st.regs (r + 8) = a + 2 ∧
  (∀ i (h : i < chosen.length), st.arr a i = value chosen[i]) ∧
  (∀ u < q ^ ρ, st.arr (a + 1) u = if ∃ z ∈ chosen, Code.repr q ρ u ∈ ball (2 * t) z then 1 else 0) ∧
  (∀ u < q ^ ρ, st.arr (a + 2) u =
    if Code.repr q ρ u ∈ chosen then chosen.idxOf (Code.repr q ρ u) + 1 else 0) ∧
  (∀ r', (r' < r ∨ r + 49 + 6 * t ≤ r') → st.regs r' = st0.regs r') ∧
  (∀ y i, (y < a ∨ a + 5 + 2 * t ≤ y) → st.arr y i = st0.arr y i) ∧
  st.cur = st0.cur ∧ st.out = st0.out

/-- The number of visits of a word of length `ρ` (bound). -/
def visBound (q t ρ : ℕ) : ℕ := ∑ i ∈ Finset.range (2 * t + 1), (2 * q * (ρ + 2 * t + 1)) ^ i

/-- Per-iteration cost bound of the scan. -/
def mainD (B q t ρ a : ℕ) : ℕ :=
  (7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) +
    visBound q t ρ * ((7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) +
      (shortCfg 0 a).enumE B q ρ (2 * t))

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS4
/-!
# Short table, part 4: the program `shortW` and its specification (q379, Part S)

`shortW q t r a` (static `q`, `t`; register base `r`, array base `a`), inputs `regs r = ρ`,
`regs (r + 1) = q ^ ρ`:
1. `MARK[u] := 0`, `INV[u] := 0` for `u < q^ρ` (arrays `a + 1`, `a + 2`), `cnt := 0`;
2. for `v = 0 .. q^ρ - 1`: if `MARK[v] = 0` then `T[cnt] := v` (array `a`), `INV[v] := cnt + 1`,
   `cnt += 1`, and mark every length-`ρ` word of `ball (2t) (repr q ρ v)`.

`shortW_spec`: the final state satisfies `SInv` for `greedy t (words q ρ)`, with the cost bound
`shortCost`.  `shortW_table`: the corollaries for `shortTable q t h` (`ρ = shortLength q t h`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-- Clear `MARK[v]` and `INV[v]` (register `r + 5` holds `0`). -/
def initBody (r : ℕ) : Cmd := seqs [ast (r + 7) (r + 3) (r + 5), ast (r + 8) (r + 3) (r + 5)]

/-- **The short-table program.** -/
def shortW (q t r a : ℕ) : Cmd :=
  .seq (seqs [lit (r + 6) a, lit (r + 7) (a + 1), lit (r + 8) (a + 2), lit (r + 5) 0, lit (r + 2) 0])
    (.seq (forLoop (r + 3) (r + 1) (r + 4) (initBody r)) (forLoop (r + 3) (r + 1) (r + 4) (mainBody q t r a)))

/-- The cost bound of `shortW`. -/
def shortCost (B q t ρ a : ℕ) : ℕ :=
  (q ^ ρ + 1) * (1 + visBound q t ρ) * (200 * (q + 1) * (ρ + 2 * t + 2) ^ 2) *
    kappa B (RAM.bits (shortM q t ρ a))

/-! ## Corollaries for `shortTable` -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamDecode4
/-!
# The decoder, part 4: the program `decProg` and its specification (q379, Part D)

The short-table routine is taken from `RamEncodeS4` (namespace `EncS`, a verbatim copy of
`RamShort*`), because `RamShort` and `RamColor` cannot be imported together (name clashes
`value_lt`, `visBound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The split of a short-code index -/

/-! ## Monotone bounds -/

/-! ## The program -/

def dSetA (q : ℕ) : Cmd := seqs [cp 400 200, cp 403 106, cp 418 101, cp 424 103, lit 4 q]
def dSetS (t : ℕ) : Cmd := seqs [cp (530 + 15 * t) 113, cp (531 + 15 * t) 114]
def dSetR (t : ℕ) : Cmd := seqs [lit 7 (t + 1), ar .add 5 0 7, lit 270 (15 + 5 * t), lit 271 0, cp 272 5]
def dCheck (t : ℕ) : Cmd := seqs [cp (528 + 15 * t) 273, lit 2 0, lit 8 t, ar .add 9 0 8,
  ar .lt 10 9 273, ar .add 11 273 8, ar .lt 12 11 0, ar .add 10 10 12]

/-- The set-up: parameters, modulus, `q^h₂`, short table, reading `z`, the length test. -/
def decPre (q t : ℕ) : Cmd :=
  seqs [lit 1 1, paramsW q t 0 1 100, modulusW 102 200, dSetA q, powW 4 110 3, dSetS t,
    EncS.shortW q t (530 + 15 * t) (16 + 5 * t), dSetR t, readW 270, dCheck t]

def dEmit : Cmd := seqs [lit 280 2, lit 281 0, cp 282 116, emitW 280]

/-- **The decoder program** (run from `HS.init n`); the flag register is `decFlag`. -/
def decProg (q t : ℕ) : Cmd :=
  seqs [decPre q t, .ifz 10 (enumScripts q t (dC0 t) (pBody q t)) .skip, .ifz 2 .skip dEmit]

def decFlag : ℕ := 2

/-- The modulus `p = modSearch b`, `b = ceilLog 2 (r K + 1)`. -/
noncomputable def decB (q t n : ℕ) : ℕ := ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)

/-- The cost bound of the set-up. -/
noncomputable def preCost (q t n B : ℕ) : ℕ :=
  paramsCost q t n * kappa B (RAM.bits (paramsBound q t n 1)) +
  (2 ^ decB q t n + 1) ^ 2 * (44 * decB q t n + 90) *
    kappa B (RAM.bits ((2 ^ decB q t n + 4) * 2 ^ (2 * (decB q t n + 1)))) +
  EncS.shortCost B q t (parameters q t n).ρ (16 + 5 * t) +
  (11 * n + 2 * (parameters q t n).h₂ + 11 * t + 60) * kappa B (RAM.bits (DM q t n))

/-- **The cost bound of the decoder**, explicit in `n`, `q`, `t`, `B` and the parameter fields. -/
noncomputable def decCost (q t n B : ℕ) : ℕ :=
  preCost q t n B +
  (∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i) *
    (dBodyCost q t n B + (dC0 t).enumE B q (n + t) t) +
  (6 * (parameters q t n).k + 20) * kappa B (RAM.bits (DM q t n))

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode
/-!
# The encoder program (q379, Part E), part 1: the program and its first phases

`encProg q t` (run from `HS.init n`, input `toWord u`):

* A: `paramsW` (registers `100 ..`, prime table in array `1`), `modulusW` (`p` in register `150`);
* B: read the `k` input symbols into array `2` (`readW`), copy `x = u.take m` into the input buffer
  of `colorsAll` (`copyW`), `j := value (u.drop m)` (`valueW`, register `2`);
* C: `colorsAll` (`Cx` in register `3`, `V` in register `4`, neighbour colours in array `6`);
* D: the good-index loop (`sel` in register `6`);
* E: `idx := (sel % q^h₁) * q^h₂ + (Cx % PR[sel]) % q^h₂` (register `22`);
* F: `shortW` (base register `310 + 12 t`, table array `14 + 4 t`);
* G: emit `x`, then the table word `T[idx]` (if `idx` is below the table length), flag `30 := 1`.

The short-table routines come from the namespace copy `RamEncodeS*` of `RamShort*` (the originals
clash with `RamColor` on two names).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Layout and program -/

/-- The enumerator of the neighbour colours (inner, `colorOf`). -/
def encCfg2 : EnumCfg := ⟨270, 10⟩
/-- The enumerator of the neighbourhood of `x` (outer). -/
def encCfg1 (t : ℕ) : EnumCfg := ⟨289 + 6 * t, 12 + 2 * t⟩

/-- Phase A: parameters, prime table, modulus. -/
def encA (q t : ℕ) : Cmd := seqs [lit 1 1, paramsW q t 0 1 100, modulusW 102 150]

/-- Phase B: read `u`, copy `x`, compute `j`. -/
def encB (t : ℕ) (q : ℕ) : Cmd :=
  seqs [seqs [lit 40 2, lit 41 0, cp 42 116], readW 40,
    seqs [lit 50 2, lit 51 0, lit 52 (13 + 4 * t), lit 53 0, cp 54 115],
    copyW 50 51 52 53 54 55 56 57 58, cp (307 + 12 * t) 115,
    seqs [lit 60 2, cp 61 115, ar .sub 62 116 115, lit 63 q], valueW 60, cp 2 64]

/-- Phase C: the colours. -/
def encC (q t : ℕ) : Cmd :=
  seqs [seqs [cp 200 150, cp 203 106, cp 218 101, cp 224 103],
    colorsAll q t (encCfg1 t) encCfg2 200 3 4 5 6, seqs [cp 3 251, cp 4 252]]

/-- Inner loop body: `good := 0` if `CL[ℓ] % pr = Cx % pr`. -/
def encInner : Cmd :=
  seqs [ald 14 17 10, ar .mod 14 14 12, ar .sub 15 14 13, ar .sub 16 13 14, ar .add 15 15 16,
    .ifz 15 (lit 7 0) .skip]

/-- Selection step: if `good ∧ c = j` then `sel := i`; `c := c + good`. -/
def encStep : Cmd :=
  seqs [seqs [ar .sub 15 5 2, ar .sub 16 2 5, ar .add 15 15 16, lit 16 1, ar .sub 16 16 7,
    ar .add 15 15 16], .ifz 15 (cp 6 8) .skip, ar .add 5 5 7]

/-- Outer loop body (index `i` in register `8`). -/
def encBody : Cmd :=
  seqs [seqs [ald 12 1 8, ar .mod 13 3 12, lit 7 1], forLoop 10 4 11 encInner, encStep]

/-- Phase D: the good-index loop. -/
def encD : Cmd := seqs [seqs [lit 5 0, cp 6 105, lit 17 6], forLoop 8 105 9 encBody]

/-- Phase E: `idx`. -/
def encE (q : ℕ) : Cmd :=
  seqs [seqs [ald 12 1 6, ar .mod 18 3 12, lit 19 q], powW 19 109 20, powW 19 110 21,
    seqs [ar .mod 22 6 20, ar .mul 22 22 21, ar .mod 23 18 21, ar .add 22 22 23]]

/-- Phase F: the short table. -/
def encF (q t : ℕ) : Cmd :=
  seqs [seqs [cp (310 + 12 * t) 113, cp (311 + 12 * t) 114], EncS.shortW q t (310 + 12 * t) (14 + 4 * t)]

/-- Emitting the table word `T[idx]`. -/
def encWord (q t : ℕ) : Cmd :=
  seqs [seqs [lit 26 (14 + 4 * t), ald 81 26 22, lit 80 7, cp 82 114, cp 83 113, lit 84 q], EncS.reprW 80,
    seqs [lit 90 7, lit 91 0, cp 92 113], emitW 90]

/-- Phase G: the output. -/
def encG (q t : ℕ) : Cmd :=
  seqs [seqs [lit 70 2, lit 71 0, cp 72 115], emitW 70,
    seqs [ar .lt 24 22 112, ar .lt 25 22 (312 + 12 * t), ar .mul 24 24 25],
    .ifz 24 .skip (encWord q t), lit 30 1]

/-- **The encoder program.** -/
def encProg (q t : ℕ) : Cmd :=
  seqs [encA q t, encB t q, encC q t, encD, encE q, encF q t, encG q t]

/-- The flag register of the encoder. -/
def encFlag : ℕ := 30

/-! ## Invariant kept from phase A on -/

/-- Parameters at `100`, `p` at `150`, the prime-table array id `1` in register `1`, the table. -/
structure EBase (q t n p : ℕ) (s : HS) : Prop where
  par : ParamsAt s 100 q t n
  r1 : s.regs 1 = 1
  rp : s.regs 150 = p
  pr : ∀ i ≤ (parameters q t n).L, s.arr 1 i = primeAt i

/-! ## Phase A -/

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

/-- The modulus-search data bound. -/
def modM (b : ℕ) : ℕ := (2 ^ b + 4) * 2 ^ (2 * (b + 1))

/-- The cost bound of phase A. -/
noncomputable def costA (B q t n : ℕ) : ℕ :=
  kappa B (RAM.bits 1) + paramsCost q t n * kappa B (RAM.bits (paramsBound q t n 1)) +
    (2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) ^ 2 *
      (44 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 90) *
      kappa B (RAM.bits (modM (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))))

/-! ## Phase B -/

/-- `2 ^ (2 W)` with `W = b + 1` (kept opaque for `omega`). -/
noncomputable def encPW (q t n : ℕ) : ℕ := 2 ^ (2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1))

/-- The data bound for the encoder's own instructions. -/
noncomputable def encM (q t n : ℕ) : ℕ :=
  4 * (q ^ (parameters q t n).k + q ^ (parameters q t n).h + q ^ (parameters q t n).ρ +
    (parameters q t n).Q ^ 2 +
    encPW q t n + primeBound (parameters q t n).L + visBound q t (parameters q t n).m + (parameters q t n).h +
    (parameters q t n).k + (parameters q t n).L + (parameters q t n).K + n + q + t + 400)

/-! ## Phase C -/

/-- The visit bound used for `colorsAll`. -/
noncomputable def encVb (q t n : ℕ) : ℕ := visBound q t (parameters q t n).m

/-- The `Ms` data bound of `colorsAll`. -/
noncomputable def encMs (q t n : ℕ) : ℕ :=
  (2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) + 6) * encPW q t n + 5 +
    (encVb q t n + 2) * (parameters q t n).K + encVb q t n

/-- The `Mb` data bound of `colorsAll`. -/
noncomputable def encMb (q t n : ℕ) : ℕ :=
  q ^ (parameters q t n).m + 2 * q + 6 * t + 44 + 2 * (parameters q t n).m + (parameters q t n).Q +
    (encVb q t n + 1) * (parameters q t n).K + encVb q t n + 2 * encPW q t n + 2

/-- The cost bound of phase C. -/
noncomputable def costC (B q t n : ℕ) : ℕ :=
  (encVb q t n + 1) * (colorOfCost B q t (parameters q t n).m (parameters q t n).K (parameters q t n).Q
      (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) (encVb q t n) (encMs q t n)
      (encMb q t n) encCfg2 +
    (19 * (parameters q t n).m + 40) * kappa B (RAM.bits (encMb q t n)) +
    (encCfg1 t).enumE B q (parameters q t n).m (2 * t)) + 6 * kappa B (RAM.bits (encM q t n))

end Phases

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode2
/-!
# The encoder program (q379, Part E), part 2: the good-index loop (phase D)

`encD` scans `i < L`; for each `i` it computes `good_i := ∀ ℓ < V, CL[ℓ] % PR[i] ≠ Cx % PR[i]`
(inner loop), and sets `sel := i` when `good_i` and the number `c` of good indices before `i`
equals `j`.  Result: `sel = ((range L).filter good)[j]?.getD L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section PhaseD
variable (inp : ℕ → ℕ) (B : ℕ)

/-- The good-index test computed by the inner loop. -/
noncomputable def goodTest (Cx V : ℕ) (cl : ℕ → ℕ) (i : ℕ) : Bool :=
  (List.range V).all (fun l => decide (Cx % primeAt i ≠ cl l % primeAt i))

end PhaseD

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode4
/-!
# The encoder program (q379, Part E), part 4: the main theorem

`encProg_spec`: for `2 ≤ q`, every `n` and `u : FixedWord q (parameters q t n).k`, with
`p = modSearch b` (`b = ceilLog 2 (r K + 1)`), under (H1) `∃ l ≤ n, rhoCond q t h l` and
(H2) `2^b ≤ p < 2^(b+1)`, the run of `encProg q t` from `HS.init n` on input `toWord u`
outputs `(encode t n p (toWord u)).map Fin.val`, leaves `1` in `encFlag`, and costs at most
`encCost q t n B`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- **The cost bound of the encoder**: the sum of the phase bounds (A: parameters and modulus,
B: reading, C: `colorsAll`, D: the good-index loop, E: `idx`, F: `shortW`, G: output). -/
noncomputable def encCost (q t n B : ℕ) : ℕ :=
  costA B q t n +
  (11 * (parameters q t n).k + 7 * (parameters q t n).m +
      7 * ((parameters q t n).k - (parameters q t n).m) + 40) * kappa B (RAM.bits (encM q t n)) +
  costC B q t n +
  (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * encVb q t n + 16) + 3) *
    kappa B (RAM.bits (8 * encM q t n + 8)) +
  (2 * (parameters q t n).h + 13) * kappa B (RAM.bits (encM q t n)) +
  (2 * kappa B (RAM.bits (encM q t n)) + EncS.shortCost B q t (parameters q t n).ρ (14 + 4 * t)) +
  (6 * (parameters q t n).m + 13 * (parameters q t n).ρ + 30) * kappa B (RAM.bits (encM q t n))

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamModulus
/-! Part M (q379): the modulus found by `modSearch` is valid. -/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

namespace Modulus

open Polynomial

/-! ## Bit polynomials -/

def mbit (a i : ℕ) : ZMod 2 := if a.testBit i then 1 else 0

/-! ## The remainder -/

/-! ## The test -/

/-! ## Existence of an irreducible polynomial of degree `b` -/

end Modulus

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamSim
/-!
# Compiling `Cmd` to `RAM.Program` (q379, Part F)

Design:
* user register `r` ↦ RAM register `2 * r` (so user register 0 holds `n` initially);
  RAM register `1` holds the constant 1, register `3` is the scratch register for
  computing `Nat.pair`, and register `2 * k + 7` is the loop counter at nesting depth `k`;
* `compile (c : Cmd) (k base : ℕ) : List RAM.Instruction` with absolute jump targets;
* the program is a prologue (set the hidden constant 1), the compiled body, then
  `jumpZero (2*flag) → reject`, `accept`, `reject`;
* `B := RAM.bits M` where `M` bounds every pc and every instruction field of the program;
* the simulation lemma `sim` by induction on `c` (fuel additivity of `RAM.run`), with the RAM
  cost increase bounded by `Cmd.cost`.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

namespace Sim

open RAM

/-! ### Bit-length facts -/

/-! ### Running -/

/-- One instruction executed on a running state (the body of `RAM.step`). -/
def stepI {q : ℕ} (input : Word q) (ins : Instruction) (s : State) : State :=
  let fetchCost := bits s.pc + 1
  let base := { s with pc := s.pc + 1, cost := s.cost + fetchCost }
  match ins with
  | .literal d a =>
      { base with registers := setReg s d a, cost := base.cost + bits d + bits a }
  | .copy d a =>
      { base with registers := setReg s d (s.registers a), cost := base.cost + bits d + bits a + bits (s.registers a) }
  | .arithmetic op d a b =>
      { base with registers := setReg s d (arithmeticValue op (s.registers a) (s.registers b)), cost := base.cost + bits d + bits a + bits b + arithmeticCost op (s.registers a) (s.registers b) }
  | .load d a =>
      let address := s.registers a
      let v := s.memory address
      { base with registers := setReg s d v, cost := base.cost + bits d + bits a + bits address + bits v }
  | .store a r =>
      let address := s.registers a
      let v := s.registers r
      { base with memory := fun i => if i = address then v else s.memory i, cost := base.cost + bits a + bits r + bits address + bits v }
  | .read d =>
      let v := inputAt input s.cursor
      { base with registers := setReg s d v, cursor := s.cursor + 1, cost := base.cost + bits d + bits s.cursor + bits v }
  | .emit a =>
      let v := s.registers a
      { base with output := s.output ++ [v], cost := base.cost + bits a + bits s.output.length + bits v }
  | .jump pc => { base with pc := pc, cost := base.cost + bits pc }
  | .jumpZero a pc =>
      { base with pc := if s.registers a = 0 then pc else s.pc + 1, cost := base.cost + bits a + bits pc + bits (s.registers a) }
  | .accept => { base with status := some true }
  | .reject => { base with status := some false }

variable {q : ℕ} {P : Program} {input : Word q}

/-! ### Program embedding and field bounds -/

/-- `L` sits in `P` at position `base`. -/
def Emb (P : Program) (base : ℕ) (L : List Instruction) : Prop :=
  ∀ i, i < L.length → P[base + i]? = L[i]?

/-- Sum of the numeric fields of an instruction. -/
def fsum : Instruction → ℕ
  | .literal d a => d + a
  | .copy d a => d + a
  | .arithmetic _ d a b => d + a + b
  | .load d a => d + a
  | .store a r => a + r
  | .read d => d
  | .emit a => a
  | .jump pc => pc
  | .jumpZero a pc => a + pc
  | .accept => 0
  | .reject => 0

/-- `M` bounds the length and every instruction field of `P`. -/
def Good (P : Program) (M : ℕ) : Prop := P.length ≤ M ∧ ∀ ins ∈ P, fsum ins ≤ M

/-! ### The state relation -/

structure Rel (s : HS) (t : State) : Prop where
  reg : ∀ r, t.registers (2 * r) = s.regs r
  one : t.registers 1 = 1
  mem : t.memory = s.mem
  cur : t.cursor = s.cur
  out : t.output = s.out
  st : t.status = none


/-! ### The compiler -/

/-- `RAM[3] := Nat.pair RAM[2x] RAM[2i]` (code at `base`, 8 instructions, 5 executed). -/
def pairCode (x i base : ℕ) : List Instruction :=
  [.arithmetic .lt 3 (2 * x) (2 * i), .jumpZero 3 (base + 5),
   .arithmetic .mul 3 (2 * i) (2 * i), .arithmetic .add 3 3 (2 * x), .jump (base + 8),
   .arithmetic .mul 3 (2 * x) (2 * x), .arithmetic .add 3 3 (2 * x), .arithmetic .add 3 3 (2 * i)]

def primCode (base : ℕ) : Prim → List Instruction
  | .lit d v => [.literal (2 * d) v]
  | .copy d a => [.copy (2 * d) (2 * a)]
  | .arith op d a b => [.arithmetic op (2 * d) (2 * a) (2 * b)]
  | .aload d x i => pairCode x i base ++ [.load (2 * d) 3]
  | .astore x i v => pairCode x i base ++ [.store 3 (2 * v)]
  | .read d => [.read (2 * d)]
  | .emit a => [.emit (2 * a)]

def primLen : Prim → ℕ
  | .aload _ _ _ => 9
  | .astore _ _ _ => 9
  | _ => 1

def len : Cmd → ℕ
  | .prim p => primLen p
  | .seq c₁ c₂ => len c₁ + len c₂
  | .ifz _ c₁ c₂ => len c₁ + len c₂ + 2
  | .loop _ c => len c + 4
  | .skip => 0

/-- Code for `c` at loop depth `k`, placed at `base`. -/
def compile : Cmd → ℕ → ℕ → List Instruction
  | .prim p, _, base => primCode base p
  | .seq c₁ c₂, k, base => compile c₁ k base ++ compile c₂ k (base + len c₁)
  | .ifz a c₁ c₂, k, base =>
      [.jumpZero (2 * a) (base + len c₂ + 2)] ++ compile c₂ k (base + 1) ++
        [.jump (base + len c₂ + 2 + len c₁)] ++ compile c₁ k (base + len c₂ + 2)
  | .loop a c, k, base =>
      [.copy (2 * k + 7) (2 * a), .jumpZero (2 * k + 7) (base + len c + 4)] ++
        compile c (k + 1) (base + 2) ++ [.arithmetic .sub (2 * k + 7) (2 * k + 7) 1, .jump (base + 1)]
  | .skip, _, _ => []

/-- The whole program. -/
def toProg (c : Cmd) (flag : ℕ) : Program :=
  [.literal 1 1] ++ compile c 0 1 ++ [.jumpZero (2 * flag) (len c + 3), .accept, .reject]

/-! ### Reachability with cost -/

/-- From `t`, some number of steps reaches a state related to `s'` at `pc`, within cost `cst`,
leaving the loop counters of depths `< k` untouched. -/
def Reach (P : Program) (input : Word q) (t : State) (s' : HS) (pc cst k : ℕ) : Prop :=
  ∃ fuel, Rel s' (run P input fuel t) ∧ (run P input fuel t).pc = pc ∧
    (run P input fuel t).cost ≤ t.cost + cst ∧
    ∀ j < k, (run P input fuel t).registers (2 * j + 7) = t.registers (2 * j + 7)

/-! ### Register-update facts -/


/-! ### Primitives -/

/-! ### Structured commands -/

/-- The simulation statement for one command. -/
def SimSpec (P : Program) (input : Word q) (M : ℕ) (c : Cmd) : Prop :=
  ∀ (k base : ℕ) (s : HS) (t : State), Emb P base (compile c k base) → Rel s t → t.pc = base →
    Reach P input t (c.exec (inputAt input) s) (base + len c) (c.cost (inputAt input) (bits M) s) k

variable {M : ℕ}

/-- The bound `M` used for `toProg`. -/
def progBound (P : Program) : ℕ := P.length + (P.map fsum).sum

end Sim

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamTop1
/-!
# Part A (q379), file 1: an asymptotic toolkit and size bounds for the parameters

`Big f a d` says `f n ≤ C * n ^ a * (bits n) ^ d` for all large `n` (with some constant `C`).
It is closed under sums, products, powers, `bits` (polynomial arguments give `Big _ 0 1`,
`q ^ e` gives the exponents of `e`) and `kappa`.  The size bounds of the fields of
`parameters q t n` are proved in this form.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

/-! ## Bit lengths -/

/-! ## The `Big` predicate -/

/-- `f n ≤ C * n ^ a * (bits n) ^ d` for all `n ≥ N`, for some `C` and `N`. -/
def Big (f : ℕ → ℕ) (a d : ℕ) : Prop :=
  ∃ C N : ℕ, ∀ n, N ≤ n → f n ≤ C * n ^ a * RAM.bits n ^ d

/-! ## The parameters -/

end EditMulticoloring.Dev.Ram.Top
end


