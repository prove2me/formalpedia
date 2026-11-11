-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Machine
-- name    : MixedVolFPRAS_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:29.139645+00:00
-- url     : https://prove2.me/theorems/6e5afa88-c277-4951-982a-d65c972ce0b7
-- title:
--   Randomized bit-stack machine with weak-membership queries: input encoding, oracle-call and bit-operation cost, success count
-- statement:
--   The paper's "randomized algorithm" whose "number of weak membership oracle calls and bit operations" is bounded is made precise by a fixed machine model (the shape of the published `OAI.CommonBasesFPRAS` machine, with a weak-membership query).
--
--   A **program** has finitely many lines $0,\dots,s$ and $k+3$ registers, each a stack of bits. Its instructions are: push a bit onto a register; pop a bit (branching on empty / 0 / 1); **coin** (branch on a fresh random bit); **query** (send the content of a register to the oracles and branch on the answer); **halt**. Register 0 initially holds the encoded input, the others are empty; at halt the output is the nonnegative rational $\mathrm{val}(\text{reg }1)/\mathrm{val}(\text{reg }2)$ ($/0=0$), $\mathrm{val}$ the binary value with least significant bit first.
--
--   Numbers are written in a self-delimiting binary code: a natural number as its bit length in unary, a separator, then its binary digits; a rational as a sign bit, $|$numerator$|$ and denominator; a list of rationals as its length and then its entries. A query register must hold the code of a list $[i,x_1,\dots,x_n,\varepsilon']$ with $i\in\{0,\dots,n-1\}$ and $\varepsilon'>0$; the oracle of body $i$ is then asked $(x,\varepsilon')$. Any other content is malformed and the machine halts with output $0$.
--
--   **Cost.** Push, pop and coin cost one bit operation; a query costs one oracle call and $1+$(length of the register) bit operations; halt costs $1+$ the lengths of the two output registers. Step $t$ of a run reads random bit $t$ of a bit stream; halted configurations do not change.
--
--   For an input list $I$ of rationals, $L=$ the length of its code, and
--
--   $$\mathrm{size}(n,I,\varepsilon,\delta)=1+n+L+\lceil 1/\varepsilon\rceil+\lceil\log_2\lceil 1/\delta\rceil\rceil .$$
--
--   A program **runs within budget $B$** on $I$ when, on every random bit stream, after $B$ steps it has halted with an output, using at most $B$ oracle calls and at most $B$ bit operations. The **good count** is the number of the $2^B$ bit strings of length $B$ whose run outputs a value $z$ with the required property; "probability at least $1-\delta$" means good count $\ge(1-\delta)2^B$.
--
--   The input of Theorem 1.2 is the list $[n,\varepsilon,\delta,x^{\mathrm{init}}_1,r_1,R_1,\dots,x^{\mathrm{init}}_n,r_n,R_n]$, each $x^{\mathrm{init}}_i$ as its $n$ coordinates.
--
--   **Formalization Note.** `Program k s`, `machineStep`, `execution`, `finiteBits` follow `OAI.CommonBasesFPRAS`; `decodeQuery` is the total decoder of the query format, checked by `#eval` to invert `listCode`. `RunsWithinBudget`, `goodCount`, `RelApprox ε V z` ($(1-\varepsilon)V\le z\le(1+\varepsilon)V$), `presentationInput` and `sizeParam` are the notions above. Two or more bit stacks with unit-cost push/pop simulate a Turing machine with polynomial overhead, so "polynomially many bit operations" is the usual notion.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 3, Theorem 1.2 (machine model); p. 12, Remark 2.20

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_WeakOracle

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# A randomized bit machine with weak-membership queries, its cost and its success count

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 3 (Theorem 1.2: "randomized algorithm", "number of
weak membership oracle calls and bit operations") and p. 12 (Remark 2.20). The paper names no
machine model; this is the shape of the published `OAI.CommonBasesFPRAS` machine with a
weak-membership query in place of its matroid oracle.

* A program has `s + 1` instructions and `k + 3` registers, each a stack of bits. Register 0
  holds the encoded input; at `halt` the output is the nonnegative rational
  `binaryValue(reg 1) / binaryValue(reg 2)` (`/ 0 = 0`).
* Instructions: `push` a bit, `pop` a bit (branching on empty / 0 / 1), `coin` (branch on a fresh
  random bit), `query` (send the encoded query in a register to the oracle and branch on the
  answer), `halt`.
* Cost: `push`, `pop`, `coin` cost one bit operation; a `query` costs one oracle call and
  `1 +` (length of the register read) bit operations; `halt` costs `1 +` the lengths of the two
  output registers.
* A query register holds `listCode [i, x₁, …, xₙ, ε']` with `i` a natural number `< n` and
  `ε' > 0`; the oracle is asked whether `x ∈ Kᵢ` with tolerance `ε'`. Any other register content
  is a malformed query: the machine halts with output `0`.
* Numbers are written in a self-delimiting binary code: `natCode x` is the bit length of `x` in
  unary, a `false` separator and the binary digits of `x` (least significant first); a rational
  is a sign bit, the code of `|num|` and the code of `den`; a list is its length and then its
  entries.
* `execution P O c bits t` is the configuration after `t` steps when step `t` reads the random
  bit `bits t`; halted configurations do not change.
* `RunsWithinBudget P O input B`: on every random bit stream, after `B` steps the run has
  halted and has used at most `B` oracle calls and at most `B` bit operations.
* `goodCount P O input B good`: the number of the `2^B` bit strings of length `B` on which the
  run's output `z` satisfies `good z`.
-/

/-- The value of a bit list, least significant bit first. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

/-- Self-delimiting code of a natural number: bit length in unary, separator, binary digits
(least significant first). -/
def natCode (x : ℕ) : List Bool :=
  List.replicate (Nat.bits x).length true ++ false :: Nat.bits x

/-- Code of a rational: sign bit, `|numerator|`, denominator. -/
def ratCode (q : ℚ) : List Bool :=
  decide (q < 0) :: (natCode q.num.natAbs ++ natCode q.den)

/-- Code of a list of rationals: its length, then its entries. -/
def listCode (l : List ℚ) : List Bool :=
  natCode l.length ++ l.flatMap ratCode

/-- Read one `natCode` off the front of a bit list. -/
def decodeNat (l : List Bool) : Option (ℕ × List Bool) :=
  let k := (l.takeWhile id).length
  match l.drop k with
  | false :: rest => if k ≤ rest.length then some (binaryValue (rest.take k), rest.drop k) else none
  | _ => none

/-- Read one rational (sign bit, numerator, nonzero denominator) off the front of a bit list. -/
def decodeRat : List Bool → Option (ℚ × List Bool)
  | [] => none
  | s :: rest =>
    match decodeNat rest with
    | none => none
    | some (a, r1) =>
      match decodeNat r1 with
      | none => none
      | some (b, r2) =>
        if b = 0 then none else some ((if s then -(a : ℚ) else (a : ℚ)) / (b : ℚ), r2)

/-- Read `k` rationals off the front of a bit list. -/
def decodeRats : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, l => some ([], l)
  | k + 1, l =>
    match decodeRat l with
    | none => none
    | some (q, r) =>
      match decodeRats k r with
      | none => none
      | some (qs, r') => some (q :: qs, r')

/-- Decode a whole bit list as `listCode` of a list of rationals (no bits left over). -/
def decodeList (l : List Bool) : Option (List ℚ) :=
  match decodeNat l with
  | none => none
  | some (k, r) =>
    match decodeRats k r with
    | some (qs, []) => some qs
    | _ => none

/-- Decode a query `[i, x₁, …, xₙ, ε']` to `n` bodies: `i` a natural number `< n`, `ε' > 0`. -/
def decodeQuery (n : ℕ) (l : List Bool) : Option (Fin n × (Fin n → ℚ) × ℚ) :=
  match decodeList l with
  | none => none
  | some qs =>
    let iq := qs.getD 0 0
    let eps := qs.getD (n + 1) 0
    if h : qs.length = n + 2 ∧ iq.den = 1 ∧ 0 ≤ iq.num ∧ iq.num.toNat < n ∧ 0 < eps then
      some (⟨iq.num.toNat, h.2.2.2.1⟩, fun j => qs.getD (j.val + 1) 0, eps)
    else none

/-- Instructions of a program with `s + 1` lines and `k + 3` registers. -/
inductive Instruction (k s : ℕ) where
  | push (register : Fin (k + 3)) (bit : Bool) (next : Fin (s + 1))
  | pop (register : Fin (k + 3)) (empty zero one : Fin (s + 1))
  | coin (zero one : Fin (s + 1))
  | query (register : Fin (k + 3)) (no yes : Fin (s + 1))
  | halt

/-- A program: one instruction per line. -/
def Program (k s : ℕ) := Fin (s + 1) → Instruction k s

/-- A machine configuration with its cost counters. -/
structure MachineConfig (k s : ℕ) where
  registers : Fin (k + 3) → List Bool
  control : Fin (s + 1)
  output : Option ℚ := none
  oracleCalls : ℕ := 0
  bitOperations : ℕ := 0

/-- The initial configuration: `listCode input` in register 0, the other registers empty. -/
def initialConfig (k s : ℕ) (input : List ℚ) : MachineConfig k s where
  registers := fun i => if i.val = 0 then listCode input else []
  control := 0

/-- One step of the machine, given the oracles and the random bit of this step. -/
def machineStep {k s n : ℕ} (P : Program k s) (O : MemOracle n)
    (randomBit : Bool) (c : MachineConfig k s) : MachineConfig k s :=
  if c.output.isSome then c else
  match P c.control with
  | .push i b next =>
    { c with
      registers := Function.update c.registers i (b :: c.registers i)
      control := next
      bitOperations := c.bitOperations + 1 }
  | .pop i empty zero one =>
    match c.registers i with
    | [] => { c with
      control := empty
      bitOperations := c.bitOperations + 1 }
    | b :: l =>
      { c with
      registers := Function.update c.registers i l
      control := if b then one else zero
      bitOperations := c.bitOperations + 1 }
  | .coin zero one =>
    { c with
      control := if randomBit then one else zero
      bitOperations := c.bitOperations + 1 }
  | .query i no yes =>
    match decodeQuery n (c.registers i) with
    | some (j, x, eps) =>
      { c with
      control := if O j x eps then yes else no
      oracleCalls := c.oracleCalls + 1
      bitOperations := c.bitOperations + (c.registers i).length + 1 }
    | none =>
      { c with
      output := some 0
      bitOperations := c.bitOperations + (c.registers i).length + 1 }
  | .halt =>
    { c with
      output := some ((binaryValue (c.registers ⟨1, by omega⟩) : ℚ) /
        (binaryValue (c.registers ⟨2, by omega⟩) : ℚ))
      bitOperations := c.bitOperations + (c.registers ⟨1, by omega⟩).length +
        (c.registers ⟨2, by omega⟩).length + 1 }

/-- The configuration after `t` steps; step `t` reads the random bit `bits t`. -/
def execution {k s n : ℕ} (P : Program k s) (O : MemOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) : ℕ → MachineConfig k s
  | 0 => c
  | t + 1 => machineStep P O (bits t) (execution P O c bits t)

/-- A finite bit string read as a stream (`false` past its end). -/
def finiteBits {B : ℕ} (bits : Fin B → Bool) (t : ℕ) : Bool :=
  if h : t < B then bits ⟨t, h⟩ else false

/-- On every random bit stream, after `B` steps the run on `input` has halted with an output and
has used at most `B` oracle calls and at most `B` bit operations. -/
def RunsWithinBudget {k s n : ℕ} (P : Program k s) (O : MemOracle n) (input : List ℚ)
    (B : ℕ) : Prop :=
  ∀ bits : ℕ → Bool,
    (execution P O (initialConfig k s input) bits B).output.isSome ∧
    (execution P O (initialConfig k s input) bits B).oracleCalls ≤ B ∧
    (execution P O (initialConfig k s input) bits B).bitOperations ≤ B

/-- The number of bit strings of length `B` on which the run on `input` has, after `B` steps,
an output `z` with `good z`. -/
def goodCount {k s n : ℕ} (P : Program k s) (O : MemOracle n) (input : List ℚ) (B : ℕ)
    (good : ℚ → Prop) : ℕ :=
  Nat.card {bits : Fin B → Bool //
    ∃ z, (execution P O (initialConfig k s input) (finiteBits bits) B).output = some z ∧ good z}

/-- `(1 − ε) V ≤ z ≤ (1 + ε) V`. -/
def RelApprox (ε : ℚ) (V : ℝ) (z : ℚ) : Prop :=
  (1 - (ε : ℝ)) * V ≤ (z : ℝ) ∧ (z : ℝ) ≤ (1 + (ε : ℝ)) * V

/-- The input of Theorem 1.2 as a list of rationals:
`[n, ε, δ, x₁^init, r₁, R₁, …, xₙ^init, rₙ, Rₙ]` (each `xᵢ^init` as its `n` coordinates). -/
def presentationInput (n : ℕ) (ε δ : ℚ) (xinit : Fin n → Fin n → ℚ) (r R : Fin n → ℚ) :
    List ℚ :=
  (n : ℚ) :: ε :: δ :: (List.finRange n).flatMap (fun i => List.ofFn (xinit i) ++ [r i, R i])

/-- The size parameter `1 + n + L + ⌈1/ε⌉ + ⌈log₂⌈1/δ⌉⌉`, where `L` is the length of the
encoded input. -/
def sizeParam (n : ℕ) (input : List ℚ) (ε δ : ℚ) : ℕ :=
  1 + n + (listCode input).length + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊

end MixedVolFPRAS.Main


