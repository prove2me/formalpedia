-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_BooleanNC
-- name    : CommutativeRankNC_Approximation_BooleanNC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:59.286647+00:00
-- url     : https://prove2.me/theorems/ba647842-2cfc-4349-b634-a5d16e15625b
-- title:
--   Logspace-uniform Boolean NC circuit families
-- statement:
--   A binary-output circuit uses the published constant, NOT, binary AND and binary OR gate syntax with topological wire indices. A multiple-output circuit is a list of these circuits, one per output bit. Its size counts all gates and outputs, its depth is the longest output path, and evaluation uses the published gate-by-gate Boolean semantics. Copying shared gates per output changes size by at most a polynomial factor.
--
--   For $\ell(N)=\lfloor\log_2(N+2)\rfloor+1$, a family $F=(F_N)$ belongs to Boolean $\mathrm{NC}^a$ when a single finite deterministic transducer emits its explicit descriptions from $1^N$ using $O(\ell(N))$ work space and some constants $C,d$ satisfy
--
--   $$|F_N|\le C(N+2)^d,\qquad \operatorname{depth}(F_N)\le C\ell(N)^a.$$
--
--   Constants are uniform over all lengths. This resource predicate contains no matrix-rank guarantee.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), pp.2, 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CommutativeRankNC_Approximation_LogspaceMachine

namespace CommutativeRankNC.Approximation

open QAlgorithms.LocalHamiltonian

/-- A polynomial-output Boolean circuit represented by one ordinary circuit
per output wire. Copying a shared DAG per output costs at most a polynomial
factor and does not increase depth. All constituent gates are constants, NOT,
binary AND, binary OR; all reference indices are topological. -/
abbrev BooleanCircuit (N : ℕ) := List (KarpLiptonOM.Circuit N)

def booleanEval {N : ℕ} (C : BooleanCircuit N) (input : List Bool) : List Bool :=
  C.map (fun c => c.eval input)

def circuitSize {N : ℕ} (C : BooleanCircuit N) : ℕ :=
  (C.map (fun c => c.gates.length + 1)).sum

def gateDepth (depths : List ℕ) : KarpLiptonOM.Gate → ℕ
  | .const _ => 0
  | .not i => depths.getD i 0 + 1
  | .and i j => max (depths.getD i 0) (depths.getD j 0) + 1
  | .or i j => max (depths.getD i 0) (depths.getD j 0) + 1

/-- Longest path to an output, with depth zero for input and constant wires. -/
def circuitDepth {N : ℕ} (C : BooleanCircuit N) : ℕ :=
  (C.map fun c =>
    let ds := (c.gates.foldl (fun ds g => ds ++ [gateDepth ds g]) (List.replicate N 0)).drop N
    ds.getLastD 0).foldl max 0

def encodeGate : KarpLiptonOM.Gate → List Bool
  | .const b => [false, false, b]
  | .not i => [false, true] ++ encBin i
  | .and i j => [true, false] ++ encBin i ++ encBin j
  | .or i j => [true, true] ++ encBin i ++ encBin j

/-- Self-delimiting explicit gate descriptions, including the output count. -/
def encodeCircuit {N : ℕ} (C : BooleanCircuit N) : List Bool :=
  encBin N ++ encBin C.length ++ C.flatMap (fun c =>
    encBin c.gates.length ++ c.gates.flatMap encodeGate)

/-- An integer logarithm differing from ceiling(log₂(N+2)) by at most one. -/
def logBound (N : ℕ) : ℕ := Nat.log2 (N + 2) + 1

/-- One finite deterministic machine generates the circuit descriptions on
unary length input. No instance bits or input-specific advice are available. -/
def LogspaceUniform (F : (N : ℕ) → BooleanCircuit N) : Prop :=
  ∃ M : LogspaceMachine, ∃ C : ℕ, 0 < C ∧ ∀ N,
    GeneratesWithin M (List.replicate N true) (encodeCircuit (F N)) (C * logBound N)

/-- The resource property of a concrete circuit family, independent of any
matrix correctness specification. Constants are uniform over all input lengths. -/
def BooleanNC (exponent : ℕ) (F : (N : ℕ) → BooleanCircuit N) : Prop :=
  LogspaceUniform F ∧ ∃ C d : ℕ, 0 < C ∧ ∀ N,
    circuitSize (F N) ≤ C * (N + 2) ^ d ∧
    circuitDepth (F N) ≤ C * logBound N ^ exponent

end CommutativeRankNC.Approximation


