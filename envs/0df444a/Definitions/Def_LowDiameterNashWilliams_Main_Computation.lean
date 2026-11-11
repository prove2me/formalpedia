-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Computation
-- name    : LowDiameterNashWilliams_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:56.150392+00:00
-- url     : https://prove2.me/theorems/c58df860-c97c-4492-a8e8-23ebe4124244
-- title:
--   Graph encodings, uniform finite programs and extended execution costs
-- statement:
--   The general instruction set and execution function are reused from the published word-RAM definition. A program is a finite list containing only fixed arithmetic, bit, indirect-memory, comparison, random-word and halting instructions. Each executed instruction costs one unit; graph algorithms and mathematical functions are software, with no oracle instruction. Words have $c(\lfloor\log_2(n+e+2)\rfloor+1)$ bits, where the fixed coefficient $c$ precedes the input. Here $e=0$ except for Lemma 4.2, where $e=d$. Input is a canonical adjacency list with vertex count, edge count, degree-prefixed lists of incident edge and neighbor identifiers, followed by the specified parameters and optional input trees. The goal receives no initial trees.
--
--   Outputs are a length and literal words in memory. Sets and trees use indicator words, and an orientation lists its ordered endpoints. A random instruction consumes the next independent uniform word, equivalently a fresh block of fair bits. Let $q_t$ be the exact fraction of length-$t$ word tapes on which the program has not halted within $t$ instructions. Then
--
--   $$\operatorname{cost}(\rho)=\inf\{t:\text{execution halts within }t\},\qquad
--   \mathbb E[\operatorname{cost}]=\sum_{t\ge0}q_t.$$
--
--   The empty infimum is $+\infty$, and nontermination never receives zero cost. The randomized run specification asks for correctness on every halting tape, $\inf_t q_t=0$ (almost-sure termination), and the displayed extended expectation bound. The deterministic specification requires a halting correct output within the worst-case bound on every tape and forbids random instructions. These are conclusions to prove about a program, not fields assuming a program's correctness or time. All reads, updates, output writes and rejected attempts require actual executed instructions. The source's natural logarithms and soft-order factors are represented separately from machine arithmetic.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Sections 3.5, 4.4, 5.1 and 6, pp. 10–11, 19–20, 23–25 (PDF pp. 11–12, 20–21, 24–26)

import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_KnapsackFPRAS_Machine

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical
open scoped BigOperators

namespace LowDiameterNashWilliams.Main

/-! Operation semantics for the computational clauses (Sections 3.5, 4.4, 5.1, 6).
Only the published general instruction set, exec and uniform-tape enumeration are reused;
the knapsack input layout, output number and parameter-dependent word size are not used.
No graph algorithm, arbitrary Lean function or assigned cost is a machine instruction. -/
abbrev Program := List KnapsackFPRAS.Machine.Instr
abbrev Memory (W : ℕ) := ℕ → BitVec W

def wordSize (c n extra : ℕ) : ℕ := c * (Nat.log2 (n + extra + 2) + 1)

def initial (W : ℕ) (xs : List ℕ) : Memory W :=
  fun a => BitVec.ofNat W (xs.getD a 0)

/-- A literal output length followed by output words in memory cells 1,2,... . Writing
these words requires actual store/one/arithmetic instructions; there is no free output call. -/
def Outputs {W : ℕ} (mem : Memory W) (xs : List ℕ) : Prop :=
  (mem 0).toNat = xs.length ∧ ∀ i : Fin xs.length, (mem (i.val + 1)).toNat = xs[i]

/-- Infinite execution costs infinity: the infimum of the empty set in ENNReal is top. -/
noncomputable def executionCost (P : Program) (W : ℕ) (xs : List ℕ)
    (ρ : ℕ → BitVec W) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : (KnapsackFPRAS.Machine.exec P ρ t 0 0 (initial W xs)).isSome), (t : ℝ≥0∞)

/-- Exactly t uniform words suffice to determine whether t executed instructions halt,
even with adaptive consumption. Unread suffixes do not affect that event. -/
noncomputable def survival (P : Program) (W : ℕ) (xs : List ℕ) (t : ℕ) : ℝ≥0∞ :=
  (KnapsackFPRAS.Machine.count (fun s =>
    KnapsackFPRAS.Machine.exec P (KnapsackFPRAS.Machine.tape W s) t 0 0 (initial W xs) = none)
      (2 ^ (W * t)) : ℝ≥0∞) / (2 ^ (W * t) : ℕ)

/-- Tail-sum expectation of the charged instruction count. This includes every rejected
attempt. Positive nontermination probability makes the sum infinite. -/
noncomputable def expectedCost (P : Program) (W : ℕ) (xs : List ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ, survival P W xs t

/-- A specification to PROVE about a finite program, never a field of the machine.
Correctness is on every halted tape, termination has probability one, and cost is operational. -/
noncomputable def Runs (P : Program) (W : ℕ) (xs : List ℕ)
    (good : Memory W → Prop) (bound : ℝ) : Prop :=
  (∀ (ρ : ℕ → BitVec W) (t : ℕ) (mem : Memory W),
    KnapsackFPRAS.Machine.exec P ρ t 0 0 (initial W xs) = some mem → good mem) ∧
  (⨅ t : ℕ, survival P W xs t) = 0 ∧ expectedCost P W xs ≤ ENNReal.ofReal bound

def Deterministic (P : Program) : Prop :=
  ∀ i, KnapsackFPRAS.Machine.Instr.rand i ∉ P

/-- Worst-case deterministic bound, including halt and output writes. -/
def RunsDet (P : Program) (W : ℕ) (xs : List ℕ)
    (good : Memory W → Prop) (bound : ℝ) : Prop :=
  Deterministic P ∧ ∀ ρ : ℕ → BitVec W, ∃ t : ℕ, (t : ℝ) ≤ bound ∧
    ∃ mem, KnapsackFPRAS.Machine.exec P ρ t 0 0 (initial W xs) = some mem ∧ good mem

/-- A canonical adjacency list: n,m, then for each vertex its degree followed by pairs
(edge id, neighbor id). Incident edges occur once at each end. No initial packing is encoded. -/
noncomputable def graphWords {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) : List ℕ :=
  [n, m] ++ (List.ofFn fun v : Fin n =>
    let es := (Finset.univ.filter fun e : Fin m => v ∈ ends e).sort (· ≤ ·)
    es.length :: es.flatMap (fun e => [e.val,
      (((List.ofFn fun u : Fin n => u).find? fun u => decide (ends e = s(v, u))).map Fin.val).getD 0])).flatten

noncomputable def setWords {a : ℕ} (S : Finset (Fin a)) : List ℕ :=
  List.ofFn fun i : Fin a => if i ∈ S then 1 else 0

noncomputable def treeWords {k m : ℕ} (T : Trees k m) : List ℕ :=
  (List.ofFn fun i : Fin k => setWords (T i)).flatten

def directionWords {n m : ℕ} (D : Direction n m) : List ℕ :=
  (List.ofFn fun e : Fin m => [(D e).1.val, (D e).2.val]).flatten

noncomputable def soft (a : ℕ) (n k : ℕ) : ℝ :=
  (1 + Real.log n + Real.log (k + 1)) ^ a

end LowDiameterNashWilliams.Main


