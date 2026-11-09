-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Machine
-- name    : HardCoreLocalSampling_Local_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:48.592947+00:00
-- url     : https://prove2.me/theorems/79808135-37c1-45f5-a7ff-baae18807def
-- title:
--   Fair-bit local oracle machine with word and bit accounts
-- statement:
--   This is the computational model of §2 as an executable language, so that output law and cost are derived from a single run.
--
--   A *program* is a finite list of instructions over three separate register files and zero-initialized memories: **labels**, opaque values that can only come from the input or the adjacency oracle and can only be copied, stored and compared; **addresses**, changed by increment, decrement and copy, or converted from a number at that number's bit cost, which index memory; and **numbers**, on which all remaining arithmetic is done. The primitives are fair-bit flip, adjacency-list random access, tri-state pin query, and a read from an external sign source used only for the root lemma. There are no real registers, no biased-coin or exact-real instructions, and no marginal oracle.
--
--   Each step adds to two accounts of the same run: the **word** account, or intrinsic work, charges an oracle query or a label/address operation one unit and every other operation its operand bit lengths (schoolbook for multiplication and division); the **bit** account additionally charges label and address operands and oracle answers at their bit length, excluding only the oracle's internal work.
--
--   The fair-bit measure on $\{0,1\}^{\mathbb N}$ is the product of independent uniform bits. Total work is the supremum over time of the accumulated charge. Every non-halted step charges at least one unit, so a nonterminating run has infinite work: a default output cannot hide work on a nonterminating tape.
--
--   **Formalization Note** A program counter outside the code is stuck and charged per step. Truncated subtraction and division by zero follow Lean's conventions; they are machine instructions with defined results and defined cost, not source objects. Unknown opcodes decode to `halt false`, so that every natural-number code is a program.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §2, printed p.2 (PDF p.3); Appendix A, printed pp.13–14 (PDF pp.14–15)

import Mathlib

namespace HardCoreLocalSampling.Local

/-! The computational model of §2 (printed p.2 / PDF p.3) as an executable program language.
A program is finite code. It has three separate register files and memories:
* *labels*: opaque vertex labels; they can only be read from an oracle or the input, copied,
  stored and compared;
* *addresses*: built by increment, decrement and copy, or converted from a number at that
  number's bit cost; they index memory;
* *numbers*: arbitrary naturals, on which all remaining arithmetic is done at bit cost.
Randomness is a stream of fair bits. There is no real-valued register, no exact-real or
biased-coin primitive, and no marginal oracle. Memory is zero until written, so nothing of the
size of the graph is ever initialized. `ext` reads a fresh sign from an external source; it is
used only to state Lemma 13, whose residual-factory calls are black boxes, and returns `false`
in every other statement. -/

/-- One instruction. Every operand is a register index, except `nconst`'s literal `v`, jump
targets `tgt` and `halt`'s output bit. -/
inductive Instr where
  /-- `L[d] := L[s]` -/
  | lcopy (d s : ℕ)
  /-- `L[d] := Lm[A[a]]` -/
  | lload (d a : ℕ)
  /-- `Lm[A[a]] := L[s]` -/
  | lstore (a s : ℕ)
  /-- jump if `L[x] = L[y]` -/
  | ljeq (x y tgt : ℕ)
  /-- jump if `L[x] < L[y]`: the fixed order of vertex labels -/
  | ljlt (x y tgt : ℕ)
  /-- `A[d] := 0` -/
  | azero (d : ℕ)
  /-- `A[d] := A[d] + 1` -/
  | ainc (d : ℕ)
  /-- `A[d] := A[d] - 1` (truncated) -/
  | adec (d : ℕ)
  /-- `A[d] := A[s]` -/
  | acopy (d s : ℕ)
  /-- `A[d] := Am[A[a]]` -/
  | aload (d a : ℕ)
  /-- `Am[A[a]] := A[s]` -/
  | astore (a s : ℕ)
  /-- jump if `A[x] = 0` -/
  | ajz (x tgt : ℕ)
  /-- jump if `A[x] = A[y]` -/
  | ajeq (x y tgt : ℕ)
  /-- jump if `A[x] < A[y]` -/
  | ajlt (x y tgt : ℕ)
  /-- `N[d] := A[s]`, at the value's bit cost -/
  | a2n (d s : ℕ)
  /-- `A[d] := N[s]`, at the value's bit cost -/
  | n2a (d s : ℕ)
  /-- `N[d] := v` -/
  | nconst (d v : ℕ)
  /-- `N[d] := N[s]` -/
  | ncopy (d s : ℕ)
  /-- `N[d] := Nm[A[a]]` -/
  | nload (d a : ℕ)
  /-- `Nm[A[a]] := N[s]` -/
  | nstore (a s : ℕ)
  /-- `N[d] := N[x] + N[y]` -/
  | add (d x y : ℕ)
  /-- `N[d] := N[x] - N[y]` (truncated) -/
  | sub (d x y : ℕ)
  /-- `N[d] := N[x] * N[y]`, at schoolbook cost -/
  | mul (d x y : ℕ)
  /-- `N[d] := N[x] / N[y]` (`0` if `N[y] = 0`), at schoolbook cost -/
  | div (d x y : ℕ)
  /-- `N[d] := N[x] % N[y]`, at schoolbook cost -/
  | mod (d x y : ℕ)
  /-- jump if `N[x] = 0` -/
  | njz (x tgt : ℕ)
  /-- jump if `N[x] < N[y]` -/
  | njlt (x y tgt : ℕ)
  /-- `N[d] :=` the next fair bit -/
  | flip (d : ℕ)
  /-- `L[d] :=` the `A[i]`-th adjacency-list entry of `L[x]`; jump if there is none -/
  | neighbor (d x i tgt : ℕ)
  /-- `N[d] :=` the pin of `L[x]`: `0` unoccupied, `1` occupied, `2` unpinned -/
  | pinq (d x : ℕ)
  /-- `N[d] :=` the next external sign of source `A[i]` (`1` is `+1`, `0` is `-1`) -/
  | ext (d i : ℕ)
  /-- unconditional jump -/
  | jmp (tgt : ℕ)
  /-- stop and output the bit `b` -/
  | halt (b : Bool)

/-- A program is finite code. -/
abbrev Program := List Instr

/-- Finite code of an instruction: an opcode and four operands. -/
abbrev InstrCode := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Decode one instruction; an unknown opcode is `halt false`. -/
def Instr.ofCode : InstrCode → Instr
  | (0, a, b, _, _) => .lcopy a b
  | (1, a, b, _, _) => .lload a b
  | (2, a, b, _, _) => .lstore a b
  | (3, a, b, c, _) => .ljeq a b c
  | (4, a, b, c, _) => .ljlt a b c
  | (5, a, _, _, _) => .azero a
  | (6, a, _, _, _) => .ainc a
  | (7, a, _, _, _) => .adec a
  | (8, a, b, _, _) => .acopy a b
  | (9, a, b, _, _) => .aload a b
  | (10, a, b, _, _) => .astore a b
  | (11, a, b, _, _) => .ajz a b
  | (12, a, b, c, _) => .ajeq a b c
  | (13, a, b, c, _) => .ajlt a b c
  | (14, a, b, _, _) => .a2n a b
  | (15, a, b, _, _) => .n2a a b
  | (16, a, b, _, _) => .nconst a b
  | (17, a, b, _, _) => .ncopy a b
  | (18, a, b, _, _) => .nload a b
  | (19, a, b, _, _) => .nstore a b
  | (20, a, b, c, _) => .add a b c
  | (21, a, b, c, _) => .sub a b c
  | (22, a, b, c, _) => .mul a b c
  | (23, a, b, c, _) => .div a b c
  | (24, a, b, c, _) => .mod a b c
  | (25, a, b, _, _) => .njz a b
  | (26, a, b, c, _) => .njlt a b c
  | (27, a, _, _, _) => .flip a
  | (28, a, b, c, e) => .neighbor a b c e
  | (29, a, b, _, _) => .pinq a b
  | (30, a, b, _, _) => .ext a b
  | (31, a, _, _, _) => .jmp a
  | (32, _, _, _, _) => .halt true
  | _ => .halt false

/-- Decode a whole program. -/
def decodeProgram (code : List InstrCode) : Program := code.map Instr.ofCode

/-- The graph-dependent black boxes: adjacency-list random access and the tri-state pin. -/
structure Oracle where
  /-- `neighbor x i` is the `i`-th adjacency-list entry of label `x`, if any. -/
  neighbor : ℕ → ℕ → Option ℕ
  /-- `pin x` is `0` unoccupied, `1` occupied, `2` unpinned. -/
  pin : ℕ → ℕ

/-- A machine configuration, including the three cost accounts of the run so far.
`word` is intrinsic work: oracle queries and label/address operations at unit cost, all
remaining arithmetic at bit cost. `bit` charges label and address operations at their bit
length as well, and charges an oracle query for its operand and answer lengths only.
`query` counts graph and pin queries, `extCalls` the `ext` instructions. -/
structure Config where
  pc : ℕ := 0
  result : Option Bool := none
  L : ℕ → ℕ := fun _ => 0
  A : ℕ → ℕ := fun _ => 0
  N : ℕ → ℕ := fun _ => 0
  Lm : ℕ → ℕ := fun _ => 0
  Am : ℕ → ℕ := fun _ => 0
  Nm : ℕ → ℕ := fun _ => 0
  flips : ℕ := 0
  extCount : ℕ → ℕ := fun _ => 0
  word : ℕ := 0
  bit : ℕ := 0
  query : ℕ := 0
  extCalls : ℕ := 0

/-- Bit length. -/
abbrev sz (n : ℕ) : ℕ := Nat.size n

namespace Config

/-- Add to the word and bit accounts. -/
def charge (c : Config) (w b : ℕ) : Config := { c with word := c.word + w, bit := c.bit + b }

/-- Move to the next instruction. -/
def next (c : Config) : Config := { c with pc := c.pc + 1 }

/-- Go to `tgt` if the condition holds, else to the next instruction. -/
def branch (c : Config) (cond : Prop) [Decidable cond] (tgt : ℕ) : Config :=
  if cond then { c with pc := tgt } else c.next

end Config

open Function in
/-- The effect and cost of one instruction, reading fair bits from `ω` and external signs
from `ξ`. -/
def exec (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool) (c : Config) : Instr → Config
  | .lcopy d s => ({ c with L := update c.L d (c.L s) }).next.charge 1 (1 + sz (c.L s))
  | .lload d a =>
      ({ c with L := update c.L d (c.Lm (c.A a)) }).next.charge 1
        (1 + sz (c.A a) + sz (c.Lm (c.A a)))
  | .lstore a s =>
      ({ c with Lm := update c.Lm (c.A a) (c.L s) }).next.charge 1
        (1 + sz (c.A a) + sz (c.L s))
  | .ljeq x y tgt => (c.branch (c.L x = c.L y) tgt).charge 1 (1 + sz (c.L x) + sz (c.L y))
  | .ljlt x y tgt => (c.branch (c.L x < c.L y) tgt).charge 1 (1 + sz (c.L x) + sz (c.L y))
  | .azero d => ({ c with A := update c.A d 0 }).next.charge 1 1
  | .ainc d => ({ c with A := update c.A d (c.A d + 1) }).next.charge 1 (1 + sz (c.A d))
  | .adec d => ({ c with A := update c.A d (c.A d - 1) }).next.charge 1 (1 + sz (c.A d))
  | .acopy d s => ({ c with A := update c.A d (c.A s) }).next.charge 1 (1 + sz (c.A s))
  | .aload d a =>
      ({ c with A := update c.A d (c.Am (c.A a)) }).next.charge 1
        (1 + sz (c.A a) + sz (c.Am (c.A a)))
  | .astore a s =>
      ({ c with Am := update c.Am (c.A a) (c.A s) }).next.charge 1
        (1 + sz (c.A a) + sz (c.A s))
  | .ajz x tgt => (c.branch (c.A x = 0) tgt).charge 1 (1 + sz (c.A x))
  | .ajeq x y tgt => (c.branch (c.A x = c.A y) tgt).charge 1 (1 + sz (c.A x) + sz (c.A y))
  | .ajlt x y tgt => (c.branch (c.A x < c.A y) tgt).charge 1 (1 + sz (c.A x) + sz (c.A y))
  | .a2n d s =>
      ({ c with N := update c.N d (c.A s) }).next.charge (1 + sz (c.A s)) (1 + sz (c.A s))
  | .n2a d s =>
      ({ c with A := update c.A d (c.N s) }).next.charge (1 + sz (c.N s)) (1 + sz (c.N s))
  | .nconst d v => ({ c with N := update c.N d v }).next.charge (1 + sz v) (1 + sz v)
  | .ncopy d s =>
      ({ c with N := update c.N d (c.N s) }).next.charge (1 + sz (c.N s)) (1 + sz (c.N s))
  | .nload d a =>
      ({ c with N := update c.N d (c.Nm (c.A a)) }).next.charge (1 + sz (c.Nm (c.A a)))
        (1 + sz (c.A a) + sz (c.Nm (c.A a)))
  | .nstore a s =>
      ({ c with Nm := update c.Nm (c.A a) (c.N s) }).next.charge (1 + sz (c.N s))
        (1 + sz (c.A a) + sz (c.N s))
  | .add d x y =>
      let v := c.N x + c.N y
      let k := 1 + sz (c.N x) + sz (c.N y) + sz v
      ({ c with N := update c.N d v }).next.charge k k
  | .sub d x y =>
      let v := c.N x - c.N y
      let k := 1 + sz (c.N x) + sz (c.N y) + sz v
      ({ c with N := update c.N d v }).next.charge k k
  | .mul d x y =>
      let k := 1 + (sz (c.N x) + 1) * (sz (c.N y) + 1)
      ({ c with N := update c.N d (c.N x * c.N y) }).next.charge k k
  | .div d x y =>
      let k := 1 + (sz (c.N x) + 1) * (sz (c.N y) + 1)
      ({ c with N := update c.N d (c.N x / c.N y) }).next.charge k k
  | .mod d x y =>
      let k := 1 + (sz (c.N x) + 1) * (sz (c.N y) + 1)
      ({ c with N := update c.N d (c.N x % c.N y) }).next.charge k k
  | .njz x tgt => (c.branch (c.N x = 0) tgt).charge (1 + sz (c.N x)) (1 + sz (c.N x))
  | .njlt x y tgt =>
      let k := 1 + sz (c.N x) + sz (c.N y)
      (c.branch (c.N x < c.N y) tgt).charge k k
  | .flip d =>
      ({ c with N := update c.N d (if ω c.flips then 1 else 0), flips := c.flips + 1 }).next.charge 1 1
  | .neighbor d x i tgt =>
      match O.neighbor (c.L x) (c.A i) with
      | some u =>
          ({ c with L := update c.L d u, query := c.query + 1 }).next.charge 1
            (1 + sz (c.L x) + sz (c.A i) + sz u)
      | none =>
          ({ c with pc := tgt, query := c.query + 1 }).charge 1 (1 + sz (c.L x) + sz (c.A i))
  | .pinq d x =>
      ({ c with N := update c.N d (O.pin (c.L x)), query := c.query + 1 }).next.charge 1
        (1 + sz (c.L x) + sz (O.pin (c.L x)))
  | .ext d i =>
      ({ c with
          N := update c.N d (if ξ (c.A i) (c.extCount (c.A i)) then 1 else 0)
          extCount := update c.extCount (c.A i) (c.extCount (c.A i) + 1)
          extCalls := c.extCalls + 1 }).next.charge 1 (1 + sz (c.A i))
  | .jmp tgt => ({ c with pc := tgt }).charge 1 1
  | .halt b => ({ c with result := some b }).charge 1 1

/-- One machine step. A halted configuration is unchanged and uncharged. A program counter
outside the code is stuck and is charged one unit per step, so a run that never halts has
infinite work on every account. -/
def step (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool) (c : Config) : Config :=
  if c.result.isSome then c else
    match P[c.pc]? with
    | none => c.charge 1 1
    | some ins => exec O ω ξ c ins

/-- The configuration after `t` steps. -/
def run (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool) (init : Config) :
    ℕ → Config
  | 0 => init
  | t + 1 => step P O ω ξ (run P O ω ξ init t)

open Classical in
/-- The halted configuration of the run, if it halts. -/
noncomputable def finalConfig (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool)
    (init : Config) : Option Config :=
  if h : ∃ t, (run P O ω ξ init t).result.isSome then
    some (run P O ω ξ init (Nat.find h))
  else none

/-- The output bit of the run; `none` if it does not halt. -/
noncomputable def outcome (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool)
    (init : Config) : Option Bool :=
  (finalConfig P O ω ξ init).bind Config.result

/-- Total intrinsic work of the run, in `[0,∞]`; infinite if it does not halt. -/
noncomputable def wordWork (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool)
    (init : Config) : ENNReal :=
  ⨆ t, ((run P O ω ξ init t).word : ENNReal)

/-- Total non-oracle bit cost of the same run, in `[0,∞]`; infinite if it does not halt. -/
noncomputable def bitWork (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool)
    (init : Config) : ENNReal :=
  ⨆ t, ((run P O ω ξ init t).bit : ENNReal)

/-- Total number of `ext` instructions executed by the same run. -/
noncomputable def extCallCount (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool)
    (init : Config) : ENNReal :=
  ⨆ t, ((run P O ω ξ init t).extCalls : ENNReal)

/-- The external source of all statements except Lemma 13: always `false`. -/
def noExt : ℕ → ℕ → Bool := fun _ _ => false

/-- The oracle that answers nothing, for statements about graph-free computation. -/
def noOracle : Oracle := ⟨fun _ _ => none, fun _ => 2⟩

/-- The law of a coin of mean `p`, truncated to `[0,1]`; statements using it state that their
means lie in `[0,1]`, so the truncation never acts in the source's domain. -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => cond b (ENNReal.ofReal (min (max p 0) 1))
      (1 - ENNReal.ofReal (min (max p 0) 1)))
    (by simp)

/-- The uniform law of one fair bit. -/
noncomputable def fairBitLaw : MeasureTheory.Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : MeasureTheory.IsProbabilityMeasure fairBitLaw := by
  unfold fairBitLaw; infer_instance

/-- The law of the fair-bit stream: independent fair bits. -/
noncomputable def fairMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => fairBitLaw

/-- The law of the external signs: independent, source `i` having `P(+1) = p i`. -/
noncomputable def extMeasure (p : ℕ → ℝ) : MeasureTheory.Measure (ℕ × ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun i => (coin (p i.1)).toMeasure

/-- A number register file loaded from a list, zero elsewhere. -/
def regsOf (x : List ℕ) : ℕ → ℕ := fun i => x.getD i 0

/-- The dyadic `±Nm[a+1] / 2^{Nm[a+2]}` stored at `a` (sign `0` is `+`). -/
noncomputable def readDyadic (c : Config) (a : ℕ) : ℝ :=
  (if c.Nm a = 0 then 1 else -1) * ((c.Nm (a + 1) : ℝ) / 2 ^ (c.Nm (a + 2)))

end HardCoreLocalSampling.Local


