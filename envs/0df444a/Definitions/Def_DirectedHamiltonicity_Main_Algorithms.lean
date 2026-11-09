-- Prove2me | Definitions.Def_DirectedHamiltonicity_Main_Algorithms
-- name    : DirectedHamiltonicity_Main_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:41.298278+00:00
-- url     : https://prove2.me/theorems/2e3bd9a9-1409-41b0-ad3d-fd9d8ec1e7d7
-- title:
--   Input encodings, coin strings and output probabilities of programs on the log-cost RAM
-- statement:
--   Algorithms are programs of the published log-cost random access machine `TargetedSamplers.Program`: one fixed finite list of instructions (constants, addition, truncated subtraction, indirect load and store, conditional jump, random access to the input bits and to the coin bits, output of a bit, halt) over unboundedly many cells holding natural numbers. Every executed instruction costs $1$ plus the bit lengths of all addresses and values it touches, so memory may be exponentially large and every access, arithmetic step and coin read is charged its bit cost. Runs here have no witness and no oracle.
--
--   1. A natural number $k$ is encoded by its binary digits, least significant first, each preceded by a `1` bit, then a `0`; an integer by a sign bit and the code of its absolute value.
--   2. A directed graph on $\{0,\dots,n-1\}$ with Boolean adjacency matrix is encoded as the code of $n$ followed by the $n^2$ matrix entries row by row.
--   3. A weighted parity instance $(n,m,\mathrm{tail},\mathrm{head},w,s,t,B)$ is encoded as the codes of $n$, $m$, then of the tail, head and weight of each arc, then of $s$, $t$, and last of $B$.
--   4. For a coin length $L$, the probability that a program outputs $y$ on input $x$ is the fraction of the $2^L$ coin strings of length $L$ on which its run halts with output exactly $y$. A coin read past the end of the string returns a fixed sentinel.
--
--   These definitions turn "a randomized algorithm with running time $T$" into a statement about one fixed program: halting within cost $T$ on every coin string, and output probabilities for uniform coins.
--
--   **Formalization Note** Coins are fair bits; sampling a uniform element of a $k$-element set must be programmed from them, and costs at least its bit length. No primitive computes anything about graphs, polynomials, determinants or linear systems.
--
--   For the smallest cycle inputs, `smallCycleAnswer` returns false at size zero and the diagonal bit at size one. `smallCycleProgram` supplies an ordinary finite RAM fragment for these branches; its output, halting and accumulated bit cost are checked locally.
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.2 / printed p.1 (Theorem 1) and PDF p.5 / printed p.4 (Proposition 4): the computational content of "randomized algorithm" and "running time"

import Mathlib
import Definitions.Def_TargetedSamplers_Machine

namespace DirectedHamiltonicity.Main

/-!
# Inputs, coins and output laws of randomized programs

T. Koana, S. Kumabe, STOC 2027 submission #811 (October 2026), Theorem 1 (PDF p.2 / printed p.1)
and Proposition 4 (PDF p.5 / printed p.4).

The machine is the published log-cost random access machine `TargetedSamplers.Program`
(`Definitions.Def_TargetedSamplers_Machine`): a fixed finite list of instructions over cells holding
natural numbers (constants, addition, truncated subtraction, indirect load and store, a conditional
jump, random access to the input bits and to the coin bits, output of a bit, halt). Every executed
instruction costs `1` plus the bit lengths of all addresses and values it touches, so each memory
access, arithmetic operation and coin read is charged its bit cost, and memory is unbounded
(exponential space is allowed). No instruction computes anything beyond these primitives.

Here a run has no witness and no oracle (the witness tape is empty and the oracle answers `0`). The
coins are a finite bit string; reading past its end returns the sentinel `2`. A run's *output* is the
bit list it wrote; a decision is the output `[true]` or `[false]`.
-/

/-- Self-delimiting binary code of a natural number: for each binary digit (least significant
first) the pair `true, digit`, followed by a single `false`. `0` is the code `[false]`. -/
def encNat (k : ℕ) : List Bool :=
  (k.bits.flatMap fun b => [true, b]) ++ [false]

/-- Code of an integer: a sign bit (`true` for negative) followed by `encNat |z|`. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- The input of the Hamiltonian-cycle problem: `encNat n`, then the `n × n` adjacency matrix row by
row, the entry `(i, j)` being `adj i j` (`true` iff the arc `i → j` is present). -/
def encodeDigraph (n : ℕ) (adj : Fin n → Fin n → Bool) : List Bool :=
  encNat n ++ (List.finRange n).flatMap fun i => (List.finRange n).map fun j => adj i j

/-- Direct answer for the two smallest sizes: no cycle on zero vertices, the diagonal bit on one.
Only the branch `n ≤ 1` uses this function. -/
def smallCycleAnswer (n : ℕ) (adj : Fin n → Fin n → Bool) : Bool :=
  if h : n = 1 then adj ⟨0, by omega⟩ ⟨0, by omega⟩ else false

/-- A concrete terminating RAM branch for `n = 0, 1`. The first header bit distinguishes them;
in the singleton encoding the diagonal bit is at address 3. Larger inputs use the main routine.
This fragment is not a Hamiltonicity primitive. -/
def smallCycleProgram : TargetedSamplers.Program :=
  [.const 1 0, .readInput 2 1, .jle 2 1 7,
   .const 1 3, .readInput 2 1, .output 2, .halt,
   .output 1, .halt]

/-- The input of the weighted parity problem: `encNat n`, `encNat m`, then for each arc `e < m` the
codes of its tail, head and weight, then the codes of `s` and `t`, and last the code of the integer
`B`. -/
def encodeParityInstance (n m : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ) (s t : Fin n)
    (B : ℤ) : List Bool :=
  encNat n ++ encNat m ++
    ((List.finRange m).flatMap fun e => encNat (tail e) ++ encNat (head e) ++ encNat (w e)) ++
    encNat s ++ encNat t ++ encInt B

/-- The tapes of a run on input `x` with coin string `coins`: no witness, no oracle. -/
def runTapes (x coins : List Bool) : TargetedSamplers.Tapes :=
  ⟨x, coins, [], TargetedSamplers.noOracle⟩

open Classical in
/-- `Pr[P outputs y on x]` when the coin string is uniform on `{0,1}^L`: the fraction of the `2^L`
coin strings of length `L` on which the run of `P` halts with output exactly `y`. -/
noncomputable def outputProb (P : TargetedSamplers.Program) (x : List Bool) (L : ℕ)
    (y : List Bool) : ℝ :=
  ((Finset.univ.filter fun c : Fin L → Bool =>
      P.Outputs (runTapes x (List.ofFn c)) (some y)).card : ℝ) / 2 ^ L

end DirectedHamiltonicity.Main


