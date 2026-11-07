-- Prove2me | Definitions.Def_GuardedSSSP_Machine
-- name    : GuardedSSSP_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:14.902481+00:00
-- url     : https://prove2.me/theorems/b75f16c3-78cc-4a3f-a182-a6b59a88463d
-- title:
--   The graph-input-uniform comparison–addition RAM of §4
-- statement:
--   A **uniform program** is one finite list of instructions together with a word exponent $c\in\mathbb N$, used on every input. It acts on two banks.
--
--   1. **Integer bank:** registers and an integer-addressed memory holding integers, with the instructions integer literal, $+$, $-$, $\times$, floor division $\lfloor a/b\rfloor$ (with $\lfloor a/0\rfloor=0$), shifts $a\cdot2^b$ and $\lfloor a/2^b\rfloor$, bit length, load, store, and the conditional jump "if $a\le b$ go to $t$".
--   2. **Real bank:** registers and an integer-addressed memory holding reals, with the instructions literal $0$, $+$, copy, load, store, and a three-way jump on $<$, $=$, $>$.
--   3. **halt**.
--
--   On an input with $n$ vertices and $m$ arcs the **word bound** is $W=(m+n+2)^c$: an integer result, address or shift amount outside $[-W,W]$ makes the machine stuck forever. Every executed instruction costs one step.
--
--   **Input:** integer memory cells $0,1,2$ hold $n,m,s$; cells $3+e$ and $3+m+e$ hold the tail and head of arc $e$; real memory cell $e$ holds $w_e$; all other cells and all registers are $0$. **Output:** when the program halts, for each vertex $v$ integer cell $-1-v$ is $0$ if $v$ is unreachable and $1$ otherwise, and in the latter case real cell $-1-v$ holds $d_w(s,v)$. $\mathrm{RAM}_U(G,s,w)$ is the number of steps up to and including the halt.
--
--   This is the machine of the paper's main theorem: real weights support only addition and comparison, and discrete metadata uses words of $O(\log(m+n+2))$ bits with unit-cost arithmetic.
--
--   **Formalization Note** The paper fixes the kinds of instructions (§4.1) but not a syntax; this model is the mission's reading. It has no real literal other than $0$, no real multiplication or division, and no cast between the banks, so integer computation sees real values only through comparison outcomes. The word exponent $c$ is chosen together with the program, which is the paper's "$O(\log(m+n+2))$-bit words with fixed headroom". A halted state stutters, so the output is read at the first halt.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10), "Metadata and total time"

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-!
# The graph-input-uniform comparison–addition RAM

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §4.1 "Metadata and total time", p.9 (PDF p.10): "A uniform
solver is one finite program receiving the graph as input. … Numerical registers have unit cost.
Discrete indices use O(log(m + n + 2))-bit words … Integer addition, comparison, multiplication,
division, shifts, and bit length take unit time on these words, with fixed headroom. Integer operations
act on discrete metadata; real-weight registers support the numerical instructions above."

A program is a finite list of instructions over two banks, together with a word exponent `c`.

* **Integer bank.** Registers `ℕ → ℤ` and an indirectly addressed memory `ℤ → ℤ`. Instructions: integer
  literal, `+`, `−`, `×`, floor division `⌊a/b⌋` (with `⌊a/0⌋ = 0`), shifts `a·2^b` and `⌊a/2^b⌋`, bit
  length, load, store, and the jump "if `a ≤ b` go to `target`".
* **Real bank.** Registers `ℕ → ℝ` and a memory `ℤ → ℝ` addressed by integers. Instructions: literal
  zero, `+`, copy, load, store, and the three-way jump on `<`, `=`, `>`.
* `halt`.

**Formalization Note.**
* **Word bound.** On an input with `n` vertices and `m` arcs the word bound is `W = (m + n + 2)^c`, with
  `c = wordExp` fixed together with the program. An integer result, a memory address or a shift amount
  outside `[−W, W]` sends the machine to a stuck state, which never halts. This is the paper's
  `O(log(m + n + 2))`-bit words "with fixed headroom", with the O-constant chosen with the program.
* There is no real literal other than `0`, no real multiplication or division, and no cast between the
  banks in either direction. The integer bank never sees a real value except through the outcomes of real
  comparisons. No constructor carries a function or a real number.
* **Cost.** Every executed instruction, including `halt`, is one step. A halted state stutters, so the
  running time is the index of the first halted state. An invalid program counter is stuck.
* **Input.** Integer memory: cell `0` is `n`, cell `1` is `m`, cell `2` is `s`, cells `3 + e` are the arc
  tails, cells `3 + m + e` the arc heads, all other cells `0`. Real memory: cell `e` holds `w e` for
  `e < m`, all other cells `0`. All registers start at `0` and the program counter at `0`.
* **Output.** At halting, for each vertex `v`, integer cell `−1 − v` is `0` when `v` is unreachable (the
  infinity tag) and `1` otherwise, and in the latter case real cell `−1 − v` holds `d_w(s, v)`.
-/

namespace Machine

/-- An instruction. Register indices and jump targets are natural numbers. -/
inductive Instr : Type
  | iconst (d : ℕ) (k : ℤ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | imul (d a b : ℕ)
  | idiv (d a b : ℕ)
  | ishl (d a b : ℕ)
  | ishr (d a b : ℕ)
  | ibitlen (d a : ℕ)
  | iload (d a : ℕ)
  | istore (a b : ℕ)
  | ijle (a b target : ℕ)
  | rzero (d : ℕ)
  | radd (d a b : ℕ)
  | rcopy (d a : ℕ)
  | rload (d a : ℕ)
  | rstore (a b : ℕ)
  | rcmp (a b tlt teq tgt : ℕ)
  | halt
  deriving DecidableEq

/-- A program: a finite instruction list and the word exponent `c` of its word bound `(m + n + 2)^c`. -/
structure Program : Type where
  code : List Instr
  wordExp : ℕ

/-- A machine state. -/
structure State : Type where
  pc : ℕ
  ireg : ℕ → ℤ
  imem : ℤ → ℤ
  rreg : ℕ → ℝ
  rmem : ℤ → ℝ
  halted : Bool
  stuck : Bool

/-- The word bound `W = (m + n + 2)^c` on an input with `n` vertices and `m` arcs. -/
def wordBound (U : Program) (n m : ℕ) : ℤ := ((m + n + 2 : ℕ) : ℤ) ^ U.wordExp

/-- `z` fits in a word: `−W ≤ z ≤ W`. -/
def Fits (W z : ℤ) : Prop := -W ≤ z ∧ z ≤ W

instance (W z : ℤ) : Decidable (Fits W z) := by unfold Fits; infer_instance

/-- The stuck state reached from `σ`. -/
def State.toStuck (σ : State) : State := { σ with stuck := true }

/-- Write the integer `v` to register `d` and advance, or get stuck if `v` does not fit. -/
def setI (W : ℤ) (σ : State) (d : ℕ) (v : ℤ) : State :=
  if Fits W v then { σ with ireg := Function.update σ.ireg d v, pc := σ.pc + 1 } else σ.toStuck

/-- Write the real `v` to real register `d` and advance. -/
def setR (σ : State) (d : ℕ) (v : ℝ) : State :=
  { σ with rreg := Function.update σ.rreg d v, pc := σ.pc + 1 }

/-- Execute one instruction under word bound `W`. -/
noncomputable def exec1 (W : ℤ) (σ : State) : Instr → State
  | .iconst d k => setI W σ d k
  | .iadd d a b => setI W σ d (σ.ireg a + σ.ireg b)
  | .isub d a b => setI W σ d (σ.ireg a - σ.ireg b)
  | .imul d a b => setI W σ d (σ.ireg a * σ.ireg b)
  | .idiv d a b => setI W σ d (Int.fdiv (σ.ireg a) (σ.ireg b))
  | .ishl d a b =>
      if 0 ≤ σ.ireg b ∧ σ.ireg b ≤ W then setI W σ d (σ.ireg a * 2 ^ (σ.ireg b).toNat)
      else σ.toStuck
  | .ishr d a b =>
      if 0 ≤ σ.ireg b ∧ σ.ireg b ≤ W then setI W σ d (Int.fdiv (σ.ireg a) (2 ^ (σ.ireg b).toNat))
      else σ.toStuck
  | .ibitlen d a => setI W σ d (Nat.size (σ.ireg a).natAbs)
  | .iload d a => if Fits W (σ.ireg a) then setI W σ d (σ.imem (σ.ireg a)) else σ.toStuck
  | .istore a b =>
      if Fits W (σ.ireg a) then
        { σ with imem := Function.update σ.imem (σ.ireg a) (σ.ireg b), pc := σ.pc + 1 }
      else σ.toStuck
  | .ijle a b target =>
      if σ.ireg a ≤ σ.ireg b then { σ with pc := target } else { σ with pc := σ.pc + 1 }
  | .rzero d => setR σ d 0
  | .radd d a b => setR σ d (σ.rreg a + σ.rreg b)
  | .rcopy d a => setR σ d (σ.rreg a)
  | .rload d a => if Fits W (σ.ireg a) then setR σ d (σ.rmem (σ.ireg a)) else σ.toStuck
  | .rstore a b =>
      if Fits W (σ.ireg a) then
        { σ with rmem := Function.update σ.rmem (σ.ireg a) (σ.rreg b), pc := σ.pc + 1 }
      else σ.toStuck
  | .rcmp a b tlt teq tgt =>
      { σ with pc := if σ.rreg a < σ.rreg b then tlt else if σ.rreg a = σ.rreg b then teq else tgt }
  | .halt => { σ with halted := true }

/-- One step. Halted and stuck states stutter; an invalid program counter is stuck. -/
noncomputable def step (U : Program) (W : ℤ) (σ : State) : State :=
  if σ.halted || σ.stuck then σ else
    match U.code[σ.pc]? with
    | none => σ.toStuck
    | some ins => exec1 W σ ins

/-- The integer input cells `n, m, s, tail₀, …, tail_{m−1}, head₀, …, head_{m−1}`. -/
def inputInts {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) : List ℤ :=
  [(n : ℤ), (m : ℤ), ((s : ℕ) : ℤ)] ++ List.ofFn (fun e : Fin m => (((G.tail e : ℕ)) : ℤ)) ++
    List.ofFn (fun e : Fin m => (((G.head e : ℕ)) : ℤ))

/-- The initial state on the input `(G, s, w)`. -/
def initState {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (w : Fin m → ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z => if 0 ≤ z then (inputInts G s).getD z.toNat 0 else 0
  rreg := fun _ => 0
  rmem := fun z => if 0 ≤ z then (List.ofFn w).getD z.toNat 0 else 0
  halted := false
  stuck := false

/-- The state after `t` steps of `U` on the input `(G, s, w)`. -/
noncomputable def run (U : Program) {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n)
    (w : Fin m → ℝ) (t : ℕ) : State :=
  (step U (wordBound U n m))^[t] (initState G s w)

/-- `U` has halted within `T` steps on `(G, s, w)`, i.e. `RAM_U(G, s, w) ≤ T`. -/
def HaltsWithin (U : Program) {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n)
    (w : Fin m → ℝ) (T : ℕ) : Prop :=
  (run U G s w T).halted = true

/-- The state `σ` holds the exact labeled distances: the infinity flag in integer cell `−1 − v`, and the
finite value in real cell `−1 − v`. -/
def OutputCorrect {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (w : Fin m → ℝ)
    (σ : State) : Prop :=
  ∀ v : Fin n,
    (dist G w s v = ⊤ → σ.imem (-1 - (v : ℕ)) = 0) ∧
    (dist G w s v ≠ ⊤ →
      σ.imem (-1 - (v : ℕ)) = 1 ∧ ((σ.rmem (-1 - (v : ℕ)) : ℝ) : EReal) = dist G w s v)

end Machine

end GuardedSSSP


