-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Machine
-- name    : OnlineRealSampling_Exact_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:00:16.393595+00:00
-- url     : https://prove2.me/theorems/3e721be0-5239-4186-a011-1f354c59be1d
-- title:
--   Charged word-RAM machines with fair-bit reads and oracle queries; oracle cost functions and efficiency
-- statement:
--   This file gives the computational model of Section 3 an operational meaning, so that every resource in the mission is read off an actual run.
--
--   **Big integers.** An integer $z$ has bit length $\mathrm{bitLen}(z)$ (the binary digits of $|z|$) and is stored in $\lfloor \mathrm{bitLen}(z)/w\rfloor+1$ limbs of $w$ bits. Every arithmetic operation goes through a charged primitive. Addition, subtraction and comparison cost the sum of the operand limb counts. Multiplication and floor or ceiling division cost the product of the limb counts plus their sum (schoolbook). Shifts $a\cdot 2^k$ and $\lfloor a/2^k\rfloor$ and powers $2^k$ cost the limbs of the result plus one, since consecutive limbs can be copied. The bit length costs $1$, read from the stored limb count and top limb. Each primitive counts as one big-integer arithmetic operation and records the largest bit length among its operands and result. $\lceil\lg(A/B)\rceil$ for positive $A,B$ is computed from two bit lengths and one shifted comparison.
--
--   **Machines.** A program is a step function on an explicit state together with the size of the state: the sum of the bit lengths of all its registers. At each step it halts, does charged local computation, reads one fresh fair bit (cost $1$), reads $m$ fresh bits as one integer (cost $\lfloor m/w\rfloor+1$), or queries the oracle at $(x,k)$ (cost $\mathrm{cost}(x,k)+1$, one oracle call). Each step costs at least one word operation. A run records the fresh bits read, the word-RAM time, the oracle calls, the big-integer operations, the largest operand bit length, and the peak storage. The storage of a step is that of the larger of the two states plus the largest operand of its arithmetic. A run may never halt, and its result is then undefined.
--
--   **Oracle cost functions.** $C_F(x,\nu)$, for $x\ge0$ and $\nu\ge1$, is a cost function of an oracle at word size $w$ if: $C_F(x,\nu)=C_F(x,1)$ for $\nu<1$; it is nondecreasing in $x$ and in $\nu$; it bounds the evaluation cost of every call $\phi(i',k')$ with $i'\le\lceil x\rceil$ and $k'\le\lceil\lg\nu\rceil+1$; and it is at least the cost of a basic arithmetic operation on quantities of magnitude $\lceil x\rceil$ and $\nu$. It is **accuracy efficient** (7), resp. **index efficient** (8), with polynomial $g$ if
--   $$C_F(x,\nu')\le g\Big(\frac{\log\nu'}{\log\nu}\Big)C_F(x,\nu)\quad(x\ge0,\ 1\le\nu<\nu'),\qquad C_F(x',\nu)\le g\Big(\frac{\log x'}{\log x}\Big)C_F(x,\nu)\quad(\nu\ge1,\ 0\le x<x').$$
--   It is **efficient** if both hold with the same $g$.
--
--   **Formalization Note** (7) and (8) are written multiplicatively. A cost function is at least the cost of one arithmetic operation, so it is positive, and the multiplicative form is then equivalent to the paper's quotient form. Every oracle admits a cost function, for instance the maximum of the finitely many relevant evaluation costs plus the arithmetic cost.
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), §3, PDF 7–8 / printed 6–7 (Word RAM arithmetic; oracle cost C_F; eqs. (7)–(8) and the Remark on complexity bounds)

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Oracle

namespace OnlineRealSampling.Exact

noncomputable section

/-! ## Word RAM representation of big integers (Section 3, PDF 7 / printed 6) -/

/-- Bit length of an integer: the binary digits of `|z|` (`bitLen 0 = 0`). -/
def bitLen (z : ℤ) : ℕ := Nat.size z.natAbs

/-- Number of `w`-bit limbs used to store `z` (at least one). -/
def limbs (w : ℕ) (z : ℤ) : ℕ := bitLen z / w + 1

/-! ## Charged local computation -/

/-- What a piece of local computation costs: word operations (`time`), arithmetic operations on
big integers (`ops`), and the largest bit length of an operand or result of those operations
(`maxBits`). -/
structure Ledger where
  time : ℕ
  ops : ℕ
  maxBits : ℕ

/-- The empty ledger. -/
def Ledger.zero : Ledger := ⟨0, 0, 0⟩

/-- Ledgers of consecutive computations: times and operation counts add, bit lengths take the
maximum. -/
def Ledger.add (a b : Ledger) : Ledger :=
  ⟨a.time + b.time, a.ops + b.ops, max a.maxBits b.maxBits⟩

/-- A value together with the ledger of the primitive operations that computed it. -/
structure Charged (α : Type) where
  val : α
  led : Ledger

instance : Monad Charged where
  pure a := ⟨a, Ledger.zero⟩
  bind x f := ⟨(f x.val).val, x.led.add (f x.val).led⟩

/-- Apply a function to the value, keeping the ledger. -/
def Charged.mapVal {α β : Type} (f : α → β) (x : Charged α) : Charged β := ⟨f x.val, x.led⟩

/-- One big-integer operation returning `val`, whose operands and result have the bit lengths
`bits`, charged `cost` word operations. Every primitive below is built from it with a fixed
cost formula. -/
def bigOp {α : Type} (val : α) (bits : List ℕ) (cost : ℕ) : Charged α :=
  ⟨val, ⟨cost, 1, bits.foldr max 0⟩⟩

section Primitives

variable (w : ℕ)

/-- Addition: one pass over the limbs. -/
def addZ (a b : ℤ) : Charged ℤ :=
  bigOp (a + b) [bitLen a, bitLen b, bitLen (a + b)] (limbs w a + limbs w b)

/-- Subtraction: one pass over the limbs. -/
def subZ (a b : ℤ) : Charged ℤ :=
  bigOp (a - b) [bitLen a, bitLen b, bitLen (a - b)] (limbs w a + limbs w b)

/-- Schoolbook multiplication. -/
def mulZ (a b : ℤ) : Charged ℤ :=
  bigOp (a * b) [bitLen a, bitLen b, bitLen (a * b)]
    (limbs w a * limbs w b + limbs w a + limbs w b)

/-- Floor division `⌊a / b⌋` (schoolbook). -/
def fdivZ (a b : ℤ) : Charged ℤ :=
  bigOp (Int.fdiv a b) [bitLen a, bitLen b, bitLen (Int.fdiv a b)]
    (limbs w a * limbs w b + limbs w a + limbs w b)

/-- Ceiling division `⌈a / b⌉` (schoolbook). -/
def cdivZ (a b : ℤ) : Charged ℤ :=
  bigOp (-(Int.fdiv (-a) b)) [bitLen a, bitLen b, bitLen (-(Int.fdiv (-a) b))]
    (limbs w a * limbs w b + limbs w a + limbs w b)

/-- Comparison `a ≤ b`. -/
def leZ (a b : ℤ) : Charged Bool :=
  bigOp (decide (a ≤ b)) [bitLen a, bitLen b] (limbs w a + limbs w b)

/-- Comparison `a < b`. -/
def ltZ (a b : ℤ) : Charged Bool :=
  bigOp (decide (a < b)) [bitLen a, bitLen b] (limbs w a + limbs w b)

/-- The power `2^k`, written limb by limb. -/
def pow2 (k : ℕ) : Charged ℤ :=
  bigOp ((2 : ℤ) ^ k) [bitLen ((2 : ℤ) ^ k)] (limbs w ((2 : ℤ) ^ k) + 1)

/-- Left shift `a · 2^k`: the result is written limb by limb. -/
def shlZ (a : ℤ) (k : ℕ) : Charged ℤ :=
  bigOp (a * 2 ^ k) [bitLen a, bitLen (a * 2 ^ k)] (limbs w (a * 2 ^ k) + 1)

/-- Right shift `⌊a / 2^k⌋`: the limbs of the result are copied from consecutive limbs of `a`,
so the cost is that of the result only ("any `k'` consecutive limbs can be copied in `O(k')`
time"). -/
def shrZ (a : ℤ) (k : ℕ) : Charged ℤ :=
  bigOp (Int.fdiv a (2 ^ k)) [bitLen a, bitLen (Int.fdiv a (2 ^ k))]
    (limbs w (Int.fdiv a (2 ^ k)) + 1)

/-- Bit length, read in `O(1)` from the stored limb count and the top limb. -/
def bitLengthZ (a : ℤ) : Charged ℕ :=
  bigOp (bitLen a) [bitLen a] 1

/-- `⌈lg (A / B)⌉` for positive integers `A, B`: the least integer `e` with `A ≤ B · 2^e`,
computed from the two bit lengths and one shifted comparison. -/
def ceilLog2Ratio (A B : ℤ) : Charged ℤ := do
  let a ← bitLengthZ A
  let b ← bitLengthZ B
  let e : ℤ := (a : ℤ) - b
  let ok ← if 0 ≤ e then do
      let Bs ← shlZ w B e.toNat
      leZ w A Bs
    else do
      let As ← shlZ w A (-e).toNat
      leZ w As B
  pure (if ok then e else e + 1)

end Primitives

/-- The cost charged by this model for one basic arithmetic operation on integers of magnitude
at most `N` (it dominates every primitive above on such operands). -/
def arithCost (w N : ℕ) : ℕ := (limbs w N + 1) ^ 2

/-! ## Machines: programs with fair-bit reads and oracle queries -/

/-- What a program does at a state: halt, do charged local computation, read one fresh fair
bit, read `m` fresh fair bits as one integer (most significant first), or query the oracle at
`(x, k)` and receive the numerator of `φ(x,k)`. -/
inductive Action (σ : Type) where
  | halt : Action σ
  | compute (next : Charged σ) : Action σ
  | coin (next : Bool → Charged σ) : Action σ
  | coins (m : ℕ) (next : ℕ → Charged σ) : Action σ
  | query (x k : ℕ) (next : ℤ → Charged σ) : Action σ

/-- Whether an action halts. -/
def Action.isHalt {σ : Type} : Action σ → Bool
  | .halt => true
  | _ => false

/-- Change the state space of an action (used to run a subroutine inside a larger state). -/
def Action.lift {σ τ : Type} (f : σ → τ) : Action σ → Action τ
  | .halt => .halt
  | .compute nx => .compute (nx.mapVal f)
  | .coin nx => .coin (fun b => (nx b).mapVal f)
  | .coins m nx => .coins m (fun v => (nx v).mapVal f)
  | .query x k nx => .query x k (fun a => (nx a).mapVal f)

/-- A machine: a step function and the number of bits of represented storage of each state
(the sum of the bit lengths of all its registers). -/
structure Machine (σ : Type) where
  step : σ → Action σ
  size : σ → ℕ

/-- A configuration of a run: the state, the number of fresh bits read so far, and the
accumulated resources — word-RAM time, oracle calls, big-integer operations, the largest operand
bit length, and the peak storage. -/
structure Config (σ : Type) where
  st : σ
  pos : ℕ
  time : ℕ
  calls : ℕ
  ops : ℕ
  maxBits : ℕ
  space : ℕ

/-- The initial configuration of a run started in state `s`. -/
def Config.init {σ : Type} (A : Machine σ) (s : σ) : Config σ := ⟨s, 0, 0, 0, 0, 0, A.size s⟩

/-- Perform one step whose local computation is `r`, reading `bits` fresh bits, with `extra`
word operations of input/oracle time and `newCalls` oracle calls. Every step costs at least one
word operation. The storage of a step is that of the larger of the two states plus the largest
operand of its arithmetic. -/
def Config.apply {σ : Type} (A : Machine σ) (c : Config σ) (r : Charged σ)
    (bits extra newCalls : ℕ) : Config σ :=
  { st := r.val
    pos := c.pos + bits
    time := c.time + 1 + extra + r.led.time
    calls := c.calls + newCalls
    ops := c.ops + r.led.ops
    maxBits := max c.maxBits r.led.maxBits
    space := max c.space (max (A.size c.st) (A.size r.val) + r.led.maxBits) }

/-- One step of a machine on the fair-bit stream `ω` and oracle `O`, with word size `w`. A
halted configuration is left unchanged. Reading one bit costs one word operation, reading `m`
bits costs `m / w + 1`, and a query at `(x,k)` costs the oracle's evaluation cost `O.cost x k`
plus one. -/
def Machine.advance {σ : Type} (A : Machine σ) (O : OracleAccess) (w : ℕ) (ω : ℕ → Bool)
    (c : Config σ) : Config σ :=
  match A.step c.st with
  | .halt => c
  | .compute nx => c.apply A nx 0 0 0
  | .coin nx => c.apply A (nx (ω c.pos)) 1 1 0
  | .coins m nx => c.apply A (nx (bitsValue ω c.pos m)) m (m / w + 1) 0
  | .query x k nx => c.apply A (nx (O.φ x k)) 0 (O.cost x k + 1) 1

/-- The configuration after `n` steps from state `s`. -/
def Machine.iter {σ : Type} (A : Machine σ) (O : OracleAccess) (w : ℕ) (ω : ℕ → Bool)
    (s : σ) (n : ℕ) : Config σ :=
  (A.advance O w ω)^[n] (Config.init A s)

/-- The run from `s` has halted after `n` steps. -/
def Machine.HaltsBy {σ : Type} (A : Machine σ) (O : OracleAccess) (w : ℕ) (ω : ℕ → Bool)
    (s : σ) (n : ℕ) : Prop :=
  (A.step (A.iter O w ω s n).st).isHalt = true

/-- The run from `s` halts. -/
def Machine.Halts {σ : Type} (A : Machine σ) (O : OracleAccess) (w : ℕ) (ω : ℕ → Bool)
    (s : σ) : Prop :=
  ∃ n, A.HaltsBy O w ω s n

open Classical in
/-- The final configuration of the run from `s`, or `none` if the run never halts. -/
def Machine.run {σ : Type} (A : Machine σ) (O : OracleAccess) (w : ℕ) (ω : ℕ → Bool)
    (s : σ) : Option (Config σ) :=
  if h : A.Halts O w ω s then some (A.iter O w ω s (Nat.find h)) else none

/-- Resources of a finished run (or of several consecutive runs). -/
structure Usage where
  bits : ℕ
  time : ℕ
  calls : ℕ
  ops : ℕ
  maxBits : ℕ
  space : ℕ

/-- The resources recorded in a configuration. -/
def Config.usage {σ : Type} (c : Config σ) : Usage :=
  ⟨c.pos, c.time, c.calls, c.ops, c.maxBits, c.space⟩

/-- Resources of two consecutive runs: counts add, peaks take the maximum. -/
def Usage.seq (u v : Usage) : Usage :=
  ⟨u.bits + v.bits, u.time + v.time, u.calls + v.calls, u.ops + v.ops,
    max u.maxBits v.maxBits, max u.space v.space⟩

/-! ## Oracle cost functions and efficiency (Section 3, (7)–(8), PDF 7–8) -/

/-- `C` is an oracle cost function `C_F(x, ν)` for the oracle `O` at word size `w`:
the convention `C(x,ν) = C(x,1)` for `ν < 1`; nondecreasing in both arguments; an upper bound on
the evaluation cost of every call `φ(i', k')` with `i' ≤ ⌈x⌉`, `k' ≤ ⌈lg ν⌉ + 1`; and at least the
cost of a basic arithmetic operation on quantities of magnitude `⌈x⌉` and `ν`. -/
structure CostBound (w : ℕ) (O : OracleAccess) (C : ℝ → ℝ → ℝ) : Prop where
  below_one : ∀ x ν : ℝ, ν < 1 → C x ν = C x 1
  mono_x : ∀ x x' ν : ℝ, 0 ≤ x → x ≤ x' → 1 ≤ ν → C x ν ≤ C x' ν
  mono_ν : ∀ x ν ν' : ℝ, 0 ≤ x → 1 ≤ ν → ν ≤ ν' → C x ν ≤ C x ν'
  eval_le : ∀ x ν : ℝ, 0 ≤ x → 1 ≤ ν → ∀ i k : ℕ, (i : ℤ) ≤ ⌈x⌉ → (k : ℤ) ≤ ⌈lg ν⌉ + 1 →
    (O.cost i k : ℝ) ≤ C x ν
  arith_le : ∀ x ν : ℝ, 0 ≤ x → 1 ≤ ν → (arithCost w (max ⌈x⌉₊ ⌈ν⌉₊) : ℝ) ≤ C x ν

/-- Accuracy efficiency (7) with polynomial `g`, in multiplicative form:
`C(x,ν') ≤ g(log ν' / log ν) · C(x,ν)` for `x ≥ 0`, `1 ≤ ν < ν'`. -/
def AccuracyEfficient (g : Polynomial ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ν ν' : ℝ, 0 ≤ x → 1 ≤ ν → ν < ν' → C x ν' ≤ g.eval (slog ν' / slog ν) * C x ν

/-- Index efficiency (8) with polynomial `g`, in multiplicative form:
`C(x',ν) ≤ g(log x' / log x) · C(x,ν)` for `ν ≥ 1`, `0 ≤ x < x'`. -/
def IndexEfficient (g : Polynomial ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ x x' ν : ℝ, 1 ≤ ν → 0 ≤ x → x < x' → C x' ν ≤ g.eval (slog x' / slog x) * C x ν

/-- An efficient oracle cost function: accuracy efficient and index efficient with the same
polynomial. -/
def Efficient (g : Polynomial ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  AccuracyEfficient g C ∧ IndexEfficient g C

end

end OnlineRealSampling.Exact


