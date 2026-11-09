-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_WordRAM
-- name    : LinearSetReconciliation327_Main_WordRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:01.640777+00:00
-- url     : https://prove2.me/theorems/dc86c413-2b7c-45b0-a51e-e1b1561b61c2
-- title:
--   §2.1 — word-RAM with public tables, toggles, explicit sparse output
-- statement:
--   A concrete word-RAM: sixteen registers, memory addressed by words, a fixed instruction set of arithmetic, bit, compare, load, store and branch instructions, each costing one step with results reduced modulo $2^W$. Public query instructions read a uniform permutation, its inverse, a uniform coefficient table, or one deterministic preprocessed table. A `TableSpec` lists the random tables and its `Seed` is the finite type of their values. A payload of $M$ bits is packed into $W$-bit words from address 0. `TogglesWithin` says the toggle program XORs the actual column $He_i$ into any stored payload within a time bound. A decoder starts with payload and hint in memory; `OutputsSupport` says it halts with an explicit duplicate-free list of exactly the support. `WidthOK` says coordinates fit in a word and the width is at most a constant times a logarithm.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §2.1, PDF p.9 (printed p.8)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! The computational model of §2.1 (PDF p.9): a word-RAM with `W`-bit words and unit-cost access to
public random permutations and their inverses, random coefficients, and one deterministic
preprocessed table (holding the expander adjacency of the CR sketch and any other parameter
computed in preprocessing). Table storage is not sketch length; preprocessing is not charged. -/

/-- A fixed finite instruction set on sixteen registers. Every operand is a `W`-bit word. -/
inductive Instr where
  | imm (d : Fin 16) (v : ℕ)
  | add (d a b : Fin 16) | sub (d a b : Fin 16) | mul (d a b : Fin 16)
  | div (d a b : Fin 16) | mod (d a b : Fin 16)
  | band (d a b : Fin 16) | bor (d a b : Fin 16) | bxor (d a b : Fin 16)
  | shl (d a b : Fin 16) | shr (d a b : Fin 16) | lt (d a b : Fin 16)
  | load (d a : Fin 16) | store (a s : Fin 16)
  | jz (r : Fin 16) (target : ℕ) | jmp (target : ℕ)
  | qDet (d a : Fin 16)
  | qPerm (d k a : Fin 16) | qPermInv (d k a : Fin 16) | qCoeff (d k a : Fin 16)
  | halt

/-- A program is a fixed finite list of instructions, chosen before every parameter. -/
abbrev Program := List Instr

/-- Machine state: program counter, registers, memory. -/
structure RAMState where
  pc : ℕ
  regs : Fin 16 → ℕ
  mem : ℕ → ℕ

/-- The word width and the query answers available to a program. -/
structure RAMEnv where
  W : ℕ
  det : ℕ → ℕ
  perm : ℕ → ℕ → ℕ
  permInv : ℕ → ℕ → ℕ
  coeff : ℕ → ℕ → ℕ

/-- One instruction, costing one time step. All results are reduced modulo `2^W`. A state with an
invalid program counter or at `halt` does not move. -/
def step (P : Program) (E : RAMEnv) (s : RAMState) : RAMState :=
  let wr (d : Fin 16) (v : ℕ) : RAMState :=
    { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) }
  let r := s.regs
  match P[s.pc]? with
  | none => s
  | some .halt => s
  | some (.imm d v) => wr d v
  | some (.add d a b) => wr d (r a + r b)
  | some (.sub d a b) => wr d (r a + 2 ^ E.W - r b)
  | some (.mul d a b) => wr d (r a * r b)
  | some (.div d a b) => wr d (r a / r b)
  | some (.mod d a b) => wr d (r a % r b)
  | some (.band d a b) => wr d (r a &&& r b)
  | some (.bor d a b) => wr d (r a ||| r b)
  | some (.bxor d a b) => wr d (r a ^^^ r b)
  | some (.shl d a b) => wr d (r a * 2 ^ r b)
  | some (.shr d a b) => wr d (r a / 2 ^ r b)
  | some (.lt d a b) => wr d (if r a < r b then 1 else 0)
  | some (.load d a) => wr d (s.mem (r a))
  | some (.store a v) =>
      { s with pc := s.pc + 1, mem := Function.update s.mem (r a) (r v) }
  | some (.jz c t) => { s with pc := if r c = 0 then t else s.pc + 1 }
  | some (.jmp t) => { s with pc := t }
  | some (.qDet d a) => wr d (E.det (r a))
  | some (.qPerm d k a) => wr d (E.perm (r k) (r a))
  | some (.qPermInv d k a) => wr d (E.permInv (r k) (r a))
  | some (.qCoeff d k a) => wr d (E.coeff (r k) (r a))

/-- The machine is stopped at a `halt` instruction. -/
def Halted (P : Program) (s : RAMState) : Prop :=
  match P[s.pc]? with
  | some .halt => True
  | _ => False

/-- From `s` the machine reaches the halted state `s'` in at most `T` steps. -/
def HaltsWithin (P : Program) (E : RAMEnv) (T : ℝ) (s s' : RAMState) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧ Halted P s'

/-- The public random tables of a sketch: uniform permutations of the listed sizes, and tables of
uniform coefficients given as (table length, number of values). -/
structure TableSpec where
  permSizes : List ℕ
  coeffShapes : List (ℕ × ℕ)
  coeff_pos : ∀ p ∈ coeffShapes, 0 < p.2

/-- A public seed: one permutation and one coefficient table per entry of the specification. -/
def TableSpec.Seed (spec : TableSpec) : Type :=
  (∀ k : Fin spec.permSizes.length, Equiv.Perm (Fin (spec.permSizes.get k))) ×
    (∀ k : Fin spec.coeffShapes.length,
      Fin (spec.coeffShapes.get k).1 → Fin (spec.coeffShapes.get k).2)

instance (spec : TableSpec) : Fintype spec.Seed := by unfold TableSpec.Seed; infer_instance

instance (spec : TableSpec) : Nonempty spec.Seed := by
  unfold TableSpec.Seed
  refine ⟨⟨fun _ => 1, fun k _ => ⟨0, spec.coeff_pos _ (List.get_mem _ _)⟩⟩⟩

/-- All table sizes and table values fit in a `W`-bit word. -/
def TableSpec.Fits (spec : TableSpec) (W : ℕ) : Prop :=
  spec.permSizes.length ≤ 2 ^ W ∧ spec.coeffShapes.length ≤ 2 ^ W ∧
    (∀ a ∈ spec.permSizes, a ≤ 2 ^ W) ∧ ∀ p ∈ spec.coeffShapes, p.1 ≤ 2 ^ W ∧ p.2 ≤ 2 ^ W

/-- The query answers under a public seed `r` and a deterministic table `det`. Out-of-range queries
return `0`; deterministic table values are reduced by `step`. -/
def TableSpec.env (spec : TableSpec) (W : ℕ) (det : ℕ → ℕ) (r : spec.Seed) : RAMEnv where
  W := W
  det := det
  perm := fun k a =>
    if h : k < spec.permSizes.length then
      if h' : a < spec.permSizes.get ⟨k, h⟩ then (r.1 ⟨k, h⟩ ⟨a, h'⟩).val else 0
    else 0
  permInv := fun k a =>
    if h : k < spec.permSizes.length then
      if h' : a < spec.permSizes.get ⟨k, h⟩ then ((r.1 ⟨k, h⟩).symm ⟨a, h'⟩).val else 0
    else 0
  coeff := fun k a =>
    if h : k < spec.coeffShapes.length then
      if h' : a < (spec.coeffShapes.get ⟨k, h⟩).1 then (r.2 ⟨k, h⟩ ⟨a, h'⟩).val else 0
    else 0

/-- A machine with no random table (for the deterministic sketches of §2.2). -/
def detEnv (W : ℕ) (det : ℕ → ℕ) : RAMEnv :=
  { W := W, det := det, perm := fun _ _ => 0, permInv := fun _ _ => 0, coeff := fun _ _ => 0 }

/-- Number of `W`-bit words holding `M` bits. -/
def wordsOf (W M : ℕ) : ℕ := (M + W - 1) / W

/-- The stored payload packed in memory: bit `p` is bit `p % W` of word `p / W`, starting at
address `0`. All other memory is zero. -/
def packMem (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (addr : ℕ) : ℕ :=
  ∑ p : Fin M, if p.val / W = addr ∧ y p = 1 then 2 ^ (p.val % W) else 0

/-- Initial state: zero program counter, the given memory, three argument registers, all else `0`. -/
def initState (mem : ℕ → ℕ) (r0 r1 r2 : ℕ) : RAMState where
  pc := 0
  regs := fun i => if i = 0 then r0 else if i = 1 then r1 else if i = 2 then r2 else 0
  mem := mem

/-- The toggle program, started with any stored payload `y` and any coordinate `i` in register 0,
halts within `T` steps with the payload `y + H e_i` packed in the payload's words. The update is
thus an actual XOR of column `H e_i` into the stored state. -/
def TogglesWithin (P : Program) (E : RAMEnv) {n M : ℕ}
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (T : ℝ) : Prop :=
  ∀ (y : Fin M → ZMod 2) (i : Fin n), ∃ s' : RAMState,
    HaltsWithin P E T (initState (packMem E.W y) i.val 0 0) s' ∧
      ∀ addr < wordsOf E.W M, s'.mem addr = packMem E.W (y + H (Pi.single i 1)) addr

/-- Maximum column weight at most `b`: `max_i ‖H e_i‖₀ ≤ b`. -/
def ColumnWeightLE {n M : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (b : ℝ) : Prop :=
  ∀ i : Fin n, ((univ.filter (fun p : Fin M => H (Pi.single i 1) p = 1)).card : ℝ) ≤ b

/-- The explicit sparse output of a halted decoder: register 1 words starting at the address in
register 0. -/
def outList (s : RAMState) : List ℕ :=
  (List.range (s.regs 1)).map (fun i => s.mem (s.regs 0 + i))

/-- The output is an explicit duplicate-free list of exactly the support of `x`. -/
def OutputsSupport {n : ℕ} (s : RAMState) (x : Fin n → ZMod 2) : Prop :=
  (outList s).Nodup ∧ ∀ v : ℕ, v ∈ outList s ↔ ∃ i : Fin n, i.val = v ∧ x i = 1

/-- Memory of a hinted decoder: the packed syndrome, then the hint coordinates one per word
following the syndrome's words. -/
def hintMem (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) (addr : ℕ) : ℕ :=
  if addr < wordsOf W M then packMem W y addr else (J.getD (addr - wordsOf W M) 0)

/-- Decoder start state, with payload `y` and hint `J`: register 1 holds the address where the hint
begins, register 2 its length. An unhinted decoder has `J = []`. -/
def decoderStart (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) : RAMState :=
  initState (hintMem W y J) 0 (wordsOf W M) J.length

/-- Word width `W` is admissible for universe `U` when coordinates fit in a word and `W` is at most
`cW` times the logarithm `b`: this is the paper's `Θ(log n)`. -/
def WidthOK (W U : ℕ) (cW b : ℝ) : Prop :=
  1 ≤ W ∧ Nat.clog 2 U ≤ W ∧ (W : ℝ) ≤ cW * b

end LinearSetReconciliation327.Main


