-- Prove2me | Definitions.Def_BlottoFPTAS_Main_BitRAM
-- name    : BlottoFPTAS_Main_BitRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:41:49.759549+00:00
-- url     : https://prove2.me/theorems/d4f2f98d-8a18-43b0-80c2-a01b7aab3f51
-- title:
--   The finite-bit model: a log-cost rational RAM with fair coins, bit cost, random bits, working bits, binary codes and the law of a sampler
-- statement:
--   The **finite-bit model** of §2.2 and App. B: binary input and output, bit operations, independent fair coins each counted as one bit operation, and each exact rational arithmetic operation, comparison, floor or gcd on operands of at most $W$ bits charged $\mathrm{Rat}(W)$ bit operations.
--
--   The machine is a **log-cost rational RAM**: finitely supported rational registers and memory; instructions `const`, `add`, `sub`, `mul`, `div` (division by $0$ gives $0$), `floor`, `gcd`, indexed `load`/`store` at the address $\lfloor r_a\rfloor$, the jump `jle` ($r_i\le0$), `coin` (next fair-coin bit), `inBit` (next input bit, $2$ past the end), `inBitAt` (the input bit at position $\lfloor r_a\rfloor$, $2$ outside the input; random access, so a sampler can read one entry of its stored description without reading the rest), `outBit` (append a bit to the output) and `halt`. An arithmetic, floor, gcd or comparison instruction costs $1+$ the total binary length of its operands, i.e. $\mathrm{Rat}(W)=W+1$ (any $\mathrm{Rat}(W)=\tilde O(W)$ gives the same $\tilde O$ bounds); a literal costs $1+$ its length; a memory access costs $1+$ the lengths of the address and the moved value; `inBitAt` costs $1+$ the length of the address; `coin`, `inBit`, `outBit`, `halt` cost $1$. **Random bits** are the executed `coin` instructions; the **working bits** of a run are the maximum over its states of the total binary length of all nonzero registers and memory cells plus the output written so far. The fair-coin tape is the product of uniform laws on $\{0,1\}$.
--
--   Numbers are written in a self-delimiting code (each binary digit preceded by a $1$, a $0$ ends the number; integers carry a sign bit; a rational is its reduced numerator and denominator). A sampler's output string is decoded as the unique list of $n$ rationals it encodes; the **law** of a sampler $S$ on a description $d$ is the pushforward of the coin tape under the decoded output. `bitCostE` and `randomBitsE` take the value $\infty$ on a run that never halts, for expectations.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 6, §2.2 (finite-bit model); p. 27; p. 49, App. B

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Sizes

open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# The finite-bit model (§2.2, p. 6; p. 27; App. B, p. 49)

"The input is given in binary, and computation uses bit operations. Algorithms obtain their
randomness from independent fair coin flips, each counted as one bit operation." Each exact
rational arithmetic operation, comparison, integer floor or gcd on operands of at most `W` bits is
charged `Rat(W) = Õ(W)` bit operations (p. 27, p. 49). Bit bounds include reading the input,
writing the output and generating random bits.

The machine is a **log-cost rational RAM**:
* registers `r : ℕ →₀ ℚ` and memory `M : ℤ →₀ ℚ` (finitely many nonzero cells);
* `const d q`, `add`, `sub`, `mul`, `div` (exact; division by `0` gives `0`), `floor`, `gcd` (of
  the floors of two registers), indexed `load`/`store` at address `⌊r[a]⌋`, the jump
  `jle i target` (if `r[i] ≤ 0`), `coin d` (`r[d] :=` the next fair-coin bit, `0` or `1`),
  `inBit d` (`r[d] :=` the next input bit, `0` or `1`, or `2` past the end of the input),
  `inBitAt d a` (`r[d] :=` the input bit at position `⌊r[a]⌋`, or `2` outside the input: random
  access to the input, so a sampler can look up one entry of its stored description without
  reading the rest, as the per-draw costs of App. F.6 assume), `outBit s` (append the bit `r[s] ≠ 0` to the output string) and `halt`;
* **charging**: an arithmetic, floor, gcd or comparison instruction costs `1 +` the total
  `ratSize` of its operands (`Rat(W) = W + 1`); `const d q` costs `1 + ratSize q`; a memory access
  costs `1 +` the size of the address register `+` the size of the value moved; `inBitAt d a` costs
  `1 +` the size of the address register; `coin`, `inBit`, `outBit`, `halt` cost `1`, and an instruction counter outside the program is stuck at cost `1`
  per step (it never halts);
* **random bits** = number of executed `coin` instructions;
* **working bits** of a state = total `ratSize` of all nonzero registers and memory cells plus the
  length of the output written so far (the description being written is included); the
  working bits of a run are the maximum over its states.

Bit strings are `List Bool`. Naturals, integers and rationals are written in a fixed
self-delimiting binary code (`encNat`, `encInt`, `encRat`): every bit of the binary expansion is
preceded by a `1`, and a `0` ends the number. A sampler's output string is decoded as the list of
`n` rationals whose encoding it is (`decodeAlloc`).
-/

namespace BitRAM

/-- An instruction of the log-cost rational RAM. -/
inductive Instr where
  /-- `r[dst] := q`. -/
  | const (dst : ℕ) (q : ℚ)
  /-- `r[dst] := r[a] + r[b]`. -/
  | add (dst a b : ℕ)
  /-- `r[dst] := r[a] - r[b]`. -/
  | sub (dst a b : ℕ)
  /-- `r[dst] := r[a] * r[b]`. -/
  | mul (dst a b : ℕ)
  /-- `r[dst] := r[a] / r[b]` (`0` if `r[b] = 0`). -/
  | div (dst a b : ℕ)
  /-- `r[dst] := ⌊r[a]⌋`. -/
  | floor (dst a : ℕ)
  /-- `r[dst] := gcd(⌊r[a]⌋, ⌊r[b]⌋)`. -/
  | gcd (dst a b : ℕ)
  /-- `r[dst] := M[⌊r[a]⌋]`. -/
  | load (dst a : ℕ)
  /-- `M[⌊r[a]⌋] := r[src]`. -/
  | store (a src : ℕ)
  /-- If `r[i] ≤ 0` jump to `target`, else fall through. -/
  | jle (i target : ℕ)
  /-- `r[dst] :=` the next fair-coin bit (`1` for heads, `0` for tails). -/
  | coin (dst : ℕ)
  /-- `r[dst] :=` the next input bit (`2` past the end). -/
  | inBit (dst : ℕ)
  /-- `r[dst] :=` the input bit at position `⌊r[a]⌋` (`2` if the position is negative or past
  the end): random access to the input. -/
  | inBitAt (dst a : ℕ)
  /-- Append the bit `r[src] ≠ 0` to the output. -/
  | outBit (src : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The program is deterministic: it contains no `coin` instruction. -/
def Deterministic (P : Program) : Prop :=
  ∀ op ∈ P, ∀ d : ℕ, op ≠ .coin d

/-- A machine state. -/
structure State where
  /-- Program counter. -/
  pc : ℕ
  /-- Rational registers. -/
  regs : ℕ →₀ ℚ
  /-- Rational memory. -/
  mem : ℤ →₀ ℚ
  /-- Position of the next unread input bit. -/
  inPos : ℕ
  /-- Output written so far. -/
  out : List Bool
  /-- Number of coins used (position of the next unread coin). -/
  coins : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Bit operations charged so far. -/
  cost : ℕ

/-- `1` for `true`, `0` for `false`. -/
def bitVal (b : Bool) : ℚ := if b then 1 else 0

/-- One step of `P` on input bits `inp` with coin tape `ω`. A halted state does not change. -/
noncomputable def step (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) : State :=
  if s.halted then s else
    let r := s.regs
    let sz : ℕ → ℕ := fun i => ratSize (r i)
    let nx : State := { s with pc := s.pc + 1 }
    match P[s.pc]? with
    | none => { s with cost := s.cost + 1 }
    | some (.const d q) =>
        { nx with regs := r.update d q, cost := s.cost + 1 + ratSize q }
    | some (.add d a b) =>
        { nx with regs := r.update d (r a + r b), cost := s.cost + 1 + sz a + sz b }
    | some (.sub d a b) =>
        { nx with regs := r.update d (r a - r b), cost := s.cost + 1 + sz a + sz b }
    | some (.mul d a b) =>
        { nx with regs := r.update d (r a * r b), cost := s.cost + 1 + sz a + sz b }
    | some (.div d a b) =>
        { nx with regs := r.update d (r a / r b), cost := s.cost + 1 + sz a + sz b }
    | some (.floor d a) =>
        { nx with regs := r.update d (⌊r a⌋ : ℚ), cost := s.cost + 1 + sz a }
    | some (.gcd d a b) =>
        { nx with regs := r.update d ((Int.gcd ⌊r a⌋ ⌊r b⌋ : ℕ) : ℚ),
                  cost := s.cost + 1 + sz a + sz b }
    | some (.load d a) =>
        { nx with regs := r.update d (s.mem ⌊r a⌋),
                  cost := s.cost + 1 + sz a + ratSize (s.mem ⌊r a⌋) }
    | some (.store a src) =>
        { nx with mem := s.mem.update ⌊r a⌋ (r src), cost := s.cost + 1 + sz a + sz src }
    | some (.jle i target) =>
        { s with pc := if r i ≤ 0 then target else s.pc + 1, cost := s.cost + 1 + sz i }
    | some (.coin d) =>
        { nx with regs := r.update d (bitVal (ω s.coins)), coins := s.coins + 1,
                  cost := s.cost + 1 }
    | some (.inBit d) =>
        { nx with regs := r.update d (match inp[s.inPos]? with
                    | some bit => bitVal bit
                    | none => 2),
                  inPos := s.inPos + 1, cost := s.cost + 1 }
    | some (.inBitAt d a) =>
        { nx with regs := r.update d (match (if 0 ≤ ⌊r a⌋ then inp[(⌊r a⌋).toNat]? else none) with
                    | some bit => bitVal bit
                    | none => 2),
                  cost := s.cost + 1 + sz a }
    | some (.outBit src) =>
        { nx with out := s.out ++ [decide (r src ≠ 0)], cost := s.cost + 1 }
    | some .halt => { nx with halted := true, cost := s.cost + 1 }

/-- The initial state: everything zero, no output. -/
def initState : State :=
  ⟨0, 0, 0, 0, [], 0, false, 0⟩

/-- The state after `k` steps on input `inp` and coin tape `ω`. -/
noncomputable def run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) : State :=
  (step P inp ω)^[k] initState

/-- The working bits of a state: sizes of all nonzero registers and memory cells, plus the
output written so far. -/
noncomputable def space (s : State) : ℕ :=
  (s.regs.sum fun _ q => ratSize q) + (s.mem.sum fun _ q => ratSize q) + s.out.length

/-- The run halts. -/
def Halts (P : Program) (inp : List Bool) (ω : ℕ → Bool) : Prop :=
  ∃ k : ℕ, (run P inp ω k).halted = true

open Classical in
/-- The number of steps to the first halted state (`0` if the run never halts; only used under
`Halts`). -/
noncomputable def haltStep (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  if h : ∃ k, (run P inp ω k).halted = true then Nat.find h else 0

/-- The first halted state (meaningful under `Halts`). -/
noncomputable def finalState (P : Program) (inp : List Bool) (ω : ℕ → Bool) : State :=
  run P inp ω (haltStep P inp ω)

/-- Bit operations charged by a halting run. -/
noncomputable def bitCost (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  (finalState P inp ω).cost

/-- Random bits used by a halting run. -/
noncomputable def randomBits (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  (finalState P inp ω).coins

/-- Working bits of a halting run: the maximum of `space` over its states. -/
noncomputable def workingBits (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  (Finset.range (haltStep P inp ω + 1)).sup fun k => space (run P inp ω k)

/-- The output string of a halting run. -/
noncomputable def output (P : Program) (inp : List Bool) (ω : ℕ → Bool) : List Bool :=
  (finalState P inp ω).out

/-- Bit operations as an extended natural: `⊤` on a run that never halts. -/
noncomputable def bitCostE (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ENNReal := by
  classical
  exact if Halts P inp ω then (bitCost P inp ω : ENNReal) else ⊤

/-- Random bits as an extended natural: `⊤` on a run that never halts. -/
noncomputable def randomBitsE (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ENNReal := by
  classical
  exact if Halts P inp ω then (randomBits P inp ω : ENNReal) else ⊤

/-- The coin tape fed to a deterministic program (never read). -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The fair-coin tape: independent fair bits (each cell uniform on `Bool`). -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- Self-delimiting code of a natural number: each binary digit (least significant first) is
preceded by `true`; a final `false` ends the number. -/
def encNat (k : ℕ) : List Bool :=
  (k.bits.flatMap fun bit => [true, bit]) ++ [false]

/-- Code of an integer: a sign bit (`true` for negative), then the magnitude. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- Code of a rational in lowest terms: numerator, then denominator. -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- Code of a list of rationals: the concatenation of their codes. -/
def encRats (qs : List ℚ) : List Bool :=
  qs.flatMap encRat

open Classical in
/-- Decode a string as an allocation of `n` rationals (`none` if it is not the code of exactly `n`
rationals; the code is injective, so the decoded allocation is unique). -/
noncomputable def decodeAlloc (n : ℕ) (bits : List Bool) : Option (Fin n → ℚ) :=
  if h : ∃ x : Fin n → ℚ, encRats (List.ofFn x) = bits then some (Classical.choose h) else none

/-- The real allocation read from a sampler's output string (`0` if it does not decode). -/
noncomputable def toAlloc (n : ℕ) (bits : List Bool) : Fin n → ℝ :=
  fun i => match decodeAlloc n bits with
    | some x => (x i : ℝ)
    | none => 0

/-- The law of the allocation sampled by program `S` run on the description `d`: the pushforward
of the fair-coin tape under the decoded output (tapes on which the run never halts are mapped by
the same formula; the theorems require them to have probability zero). -/
noncomputable def law (S : Program) (d : List Bool) (n : ℕ) : Measure (Fin n → ℝ) :=
  coinTape.map fun ω => toAlloc n (output S d ω)

end BitRAM

end BlottoFPTAS.Main


