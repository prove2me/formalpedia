-- Prove2me | Definitions.Def_QuantumKtSoI_PolySampler
-- name    : QuantumKtSoI_PolySampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:34:40.881985+00:00
-- url     : https://prove2.me/theorems/a2ca2ef6-7643-47d0-941e-2516dcc188cc
-- title:
--   Classical polynomial-time samplers of pairs of $n$-bit strings
-- statement:
--   A **probabilistic Turing machine** (§2.1) is a multi-tape Turing machine with cells indexed by $\mathbb Z$, an alphabet containing $0$, $1$ and a distinct blank, an input and an output tape, and two transition tables; at each step a fresh fair coin chooses the table, and the machine halts when it enters a final state. Its output is the longest binary string on cells $1,2,\dots$ of the output tape.
--
--   A **classical polynomial-time sampler** is such a machine $S$ with constants $c,k$ such that on input $1^n$ and every coin sequence of length $T(n)=c(n+2)^k$ it has halted by time $T(n)$ with an output of length $2n$. The output $XY$ is read as the pair $\langle X,Y\rangle=XY$ of two $n$-bit strings, and
--   $$\Pr_{(X,Y)\sim S(1^n)}[E(X,Y)]$$
--   is the fraction of coin sequences $\beta\in\{0,1\}^{T(n)}$ whose output satisfies $E$.
--
--   These are the samplers of Proposition 6.19 and Theorem 6.20.
--
--   **Formalization Note** The paper's p.51 classical sampler is a machine of Definition 3.1 whose only qubit operations are fair-coin draws; such machines and probabilistic Turing machines sample the same distributions in polynomial time (a coin draw is one coin step, and Proposition 9.8's coin machine simulates a probabilistic Turing machine step by step). All tapes share one finite alphabet.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §2.1, pp.13–14; p.18; p.51

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Machine

open Classical

noncomputable section

namespace QuantumKtSoI

/-- A **probabilistic Turing machine** (§2.1, pp.13–14): finitely many states with an initial
state and final states, finitely many tapes (an input tape and an output tape designated), cells
indexed by `ℤ`, a finite alphabet containing `0`, `1` and a distinct blank, and two transition
tables `δ false`, `δ true` assigning to each nonfinal state and tuple of scanned symbols a next
state, a symbol to write on each tape and a move of each head. At each step a fresh fair coin
chooses the table.

**Formalization Note** All tapes share one finite alphabet `Γ` (the union of the tape
alphabets). -/
structure PTM where
  Q : Type
  T : Type
  Γ : Type
  [instFQ : Fintype Q]
  [instDQ : DecidableEq Q]
  [instFT : Fintype T]
  [instDT : DecidableEq T]
  [instFΓ : Fintype Γ]
  [instDΓ : DecidableEq Γ]
  zero : Γ
  one : Γ
  blank : Γ
  zero_ne_one : zero ≠ one
  zero_ne_blank : zero ≠ blank
  one_ne_blank : one ≠ blank
  inT : T
  outT : T
  init : Q
  isFinal : Q → Bool
  δ : Bool → Q → (T → Γ) → Q × (T → Γ) × (T → Move)

attribute [instance] PTM.instFQ PTM.instDQ PTM.instFT PTM.instDT PTM.instFΓ PTM.instDΓ

namespace PTM

variable (S : PTM)

/-- A configuration of a probabilistic Turing machine. -/
structure Conf where
  state : S.Q
  cont : S.T → ℤ → S.Γ
  head : S.T → ℤ

/-- The initial configuration (§2.1, p.13): the initial state, every head on cell `0`, the input
on cells `1, 2, …` of the input tape, every other cell blank. -/
def initConf (x : List Bool) : S.Conf where
  state := S.init
  cont := fun t i =>
    if t = S.inT ∧ 1 ≤ i ∧ i ≤ x.length then (if x.getD (i - 1).toNat false then S.one else S.zero)
    else S.blank
  head := fun _ => 0

/-- One step with coin `b`: apply table `δ b`; a final state is absorbing (the machine halts when
it enters a final state). -/
def pstep (b : Bool) (C : S.Conf) : S.Conf :=
  if S.isFinal C.state then C
  else
    let out := S.δ b C.state fun t => C.cont t (C.head t)
    { state := out.1
      cont := fun t => Function.update (C.cont t) (C.head t) (out.2.1 t)
      head := fun t => C.head t + (out.2.2 t).toInt }

/-- The configuration reached on input `x` driven by the coin sequence `β`. -/
def run (x : List Bool) (β : List Bool) : S.Conf :=
  β.foldl (fun C b => S.pstep b C) (S.initConf x)

/-- The output: the longest binary string on cells `1, 2, …` of the output tape (§2.1). -/
def Conf.output {S : PTM} (C : S.Conf) : List Bool :=
  let len := sSup {k : ℕ | ∀ i < k,
    C.cont S.outT ((i : ℤ) + 1) = S.zero ∨ C.cont S.outT ((i : ℤ) + 1) = S.one}
  List.ofFn fun i : Fin len => decide (C.cont S.outT ((i : ℤ) + 1) = S.one)

end PTM

/-- A **classical polynomial-time sampler** (§2.1 PTM; p.51): a probabilistic Turing machine `S`
with constants `c, k` such that, on input `1ⁿ` and every coin sequence of length
`T(n) = c(n+2)^k`, it has entered a final state within `T(n)` steps, and its output then has
length `2n`. The output `XY` of length `2n` is read as the pair `⟨X, Y⟩ = XY` of two `n`-bit
strings (§2.1, p.14: the pairing of equal-length strings is their concatenation).

**Formalization Note** The paper's p.51 sampler is a machine of Definition 3.1 whose only qubit
operations are fair-coin draws; such machines and §2.1 probabilistic Turing machines sample the
same families in polynomial time (a coin draw is one coin step, and Proposition 9.8's coin machine
simulates a probabilistic Turing machine step by step). -/
structure PolySampler where
  S : PTM
  c : ℕ
  k : ℕ
  halts : ∀ n : ℕ, ∀ β : Fin (c * (n + 2) ^ k) → Bool,
    S.isFinal (S.run (ones n) (List.ofFn β)).state = true ∧
      (S.run (ones n) (List.ofFn β)).output.length = 2 * n

namespace PolySampler

variable (S : PolySampler)

/-- The all-branch deadline `T(n) = c(n+2)^k`. -/
def time (n : ℕ) : ℕ := S.c * (n + 2) ^ S.k

/-- `Pr_{(X,Y) ∼ S(1ⁿ)} [E(X, Y)]`: the fraction of coin sequences `β ∈ {0,1}^{T(n)}` whose run
on `1ⁿ` outputs `XY` with `E(X, Y)`, where `X` is the first `n` and `Y` the last `n` output bits
(p.18: probabilities over a uniformly random coin sequence). Since every run has halted by
`T(n)`, this does not depend on the choice of the all-branch deadline. -/
def prob (n : ℕ) (E : List Bool → List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun β : Fin (S.time n) → Bool =>
      E ((S.S.run (ones n) (List.ofFn β)).output.take n)
        ((S.S.run (ones n) (List.ofFn β)).output.drop n)).card : ℝ) / 2 ^ S.time n

end PolySampler

end QuantumKtSoI


