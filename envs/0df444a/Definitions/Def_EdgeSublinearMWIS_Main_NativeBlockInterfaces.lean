-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeBlockInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T15:20:33.702092+00:00
-- url     : https://prove2.me/theorems/113f78ba-ac5d-470f-bdf4-efd72d3db7dd
-- title:
--   Block state interfaces for native execution and recovery
-- statement:
--   These declarations expose the stored state and bounds for uniform source-RAM interpretation, exact ellipsoid search, coordinate recovery, region-cut selection and recursive collection. They consist of finite encodings, workspace predicates, matrix operations and their immediate constructor interfaces.
--
--   For a word bound $B$, command $c$ and instruction allowance $T$, the interfaces support operational contracts of the form
--   $$P(\sigma)\Longrightarrow\exists\tau,\ \operatorname{Run}_B(c,\sigma,\tau,T)\land Q(\sigma,\tau).$$
--   The bundle supplies the data and state predicates in these contracts. Their execution, halting, semantic correctness and instruction bounds remain theorem obligations. The nonnegativity lemma for replacing a distance matrix diagonal by zero is included only to construct its nonnegative-rational entries.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/BinaryOptimization.lean (definitions and structure interfaces, starting at lines 46)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidSearch.lean (definitions and structure interfaces, starting at lines 50, 98)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/PointRecovery.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPointRecoveryStep.lean (definitions and structure interfaces, starting at lines 20)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryThreshold.lean (definitions and structure interfaces, starting at lines 31, 35)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchBounds.lean (definitions and structure interfaces, starting at lines 60)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchLoop.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchStep.lean (definitions and structure interfaces, starting at lines 35)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/CutScoreHeight.lean (definitions and structure interfaces, starting at lines 9, 10)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/LargePotentialData.lean (definitions and structure interfaces, starting at lines 53)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/MetricMatrix.lean (definitions and structure interfaces, starting at lines 23, 33)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamDualDistances.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamDualDistancesInit.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamFlowData.lean (definitions and structure interfaces, starting at lines 13, 16)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamHistoryCut.lean (definitions and structure interfaces, starting at lines 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamHostBounds.lean (definitions and structure interfaces, starting at lines 8)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamLargeCut.lean (definitions and structure interfaces, starting at lines 13, 15, 16, 17, 18, 19, 20, 21)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamLargePotential.lean (definitions and structure interfaces, starting at lines 11, 13, 14, 15, 16, 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRoundingBudget.lean (definitions and structure interfaces, starting at lines 12, 13, 14, 15, 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSparseRead.lean (definitions and structure interfaces, starting at lines 10)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamVirtualCore.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamVirtualInstruction.lean (definitions and structure interfaces, starting at lines 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamVirtualState.lean (definitions and structure interfaces, starting at lines 14, 19)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamZeroCut.lean (definitions and structure interfaces, starting at lines 50, 52)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RationalDistances.lean (definitions and structure interfaces, starting at lines 14, 131)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionIterationHeight.lean (definitions and structure interfaces, starting at lines 10)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionQueryHeight.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RoundingHeight.lean (definitions and structure interfaces, starting at lines 26, 51)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/SparseRam.lean (definitions and structure interfaces, starting at lines 10, 13, 17, 26, 27, 28, 29, 30, 31, 35, 38, 66, 77, 81)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/VolumeHeight.lean (definitions and structure interfaces, starting at lines 10, 11)

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces

-- Solutions.RAM_Lax808846Proofs_Reasoning
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
The reasoning kit: how an algorithm is actually proved in this stack.

A big-step derivation is the wrong object to hand a user. It fixes the
cost *on the nose* — the constructors produce sums like
`1 + b.size + k + k'`, which no bound is definitionally equal to — and
it forces every loop to be re-proved by hand from the two `while`
constructors. This layer fixes both, and nothing else:

`Run B c σ σ' K` says that `c`, started in `σ`, terminates in `σ'` at a
cost of **at most** `K`, with every value it produces below `B`. Every
construct gets a rule, the rules compose by adding bounds, and slack can
be introduced at any point (`Run.mono`) instead of being pushed to the
end.

The judgment is built on `BigStepB`, not on `BigStep`: one derivation
carries functional correctness, cost and the value bound together, so a
user proves one thing where the alternative — a `BigStep` derivation
plus a separately established bound on the values of the same run —
would have them build the same derivation twice and then argue that the
two are the same. Where a plain-semantics fact is wanted, it is
projected out by `BigStepB.bigStep` (`Run.bigStep` here); that is how
`Run.out_eq` is proved.

The bound is not an extra hypothesis on any rule. Every rule already
asks for the value of the expression it evaluates, and it asks for it in
the bounded form `e.evalB B σ = some v`; the `simp` lemmas of the first
sections turn such a goal, on concrete syntax, into arithmetic — the
value of the expression and of each of its subexpressions is below `B` —
which is exactly the obligation the design intends and no more.

The loop rule is the only one with content. It takes an invariant `I`
and a **potential** `Φ : Env → ℕ`, and asks that one iteration —
condition test included — pay for itself out of the potential:
`1 + b.size + K + Φ σ' ≤ Φ σ`. Termination and the cost bound then come
out together, because a potential that pays for a nonzero cost is also
a variant; the loop costs at most `Φ σ + 1 + b.size`, the extra term
being the test that fails. Amortized arguments are the reason for the
potential form: a graph scan cannot bound the cost of one outer
iteration by a constant, but it can pay for it out of "queue entries
left plus adjacency slots left". `Run.while_count` is the uniform-cost
special case, an invariant and a variant, for the loops where that
suffices.
-/

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

/-! ### Reading an updated environment

Every rule below produces an environment written as a chain of updates,
and every use reads a variable back out of such a chain. These are the
lemmas that collapse the chain; they are `simp` lemmas, so the reader
of an algorithm proof sees `simp` where a proof against the raw
semantics had explicit `Env.setVar` unfolding at every step. -/



















/-! ### Arrays as functions

An IMP+ array is a list, but an invariant wants to say what is *at*
each position, not what the list is. `arrOf n f` is the array of length
`n` whose entry `i` is `f i`; an invariant then names the function, a
store updates the function at a point, and a read is a function
application. -/















/-! ### Bounded evaluation of concrete syntax

The side condition of every rule below is a bounded evaluation
`e.evalB B σ = some v`. On the concrete syntax of an actual program
these lemmas reduce such a goal to arithmetic: the value of every
subexpression is exhibited, and what is left to prove is that each of
them is below `B`. This is the whole of the value-bound obligation the
pipeline asks for, and it arrives one expression at a time, where the
values are in front of the reader, rather than as a separate pass over
the program. -/













/-! ### Introducing a bounded evaluation

The lemmas above are what `simp` needs; these are what `exact` needs.
The side condition of a rule is `e.evalB B σ = some v` with `v` already
named by the caller, and the side condition of the loop rule is the
weaker `∃ v, b.evalB B σ = some v` — a condition whose two operands
have values has one too, whichever it is. Stated as introduction rules
these are discharged by naming the value of each subexpression and its
bound, which is what a caller has in hand, instead of by first guessing
the truth value of the condition and then unfolding it again. -/





















/-! ### Counting the size of concrete syntax

An algorithm proof should never be told what a concrete expression
costs; with these the cost of a straight-line block is arithmetic on
numerals. The nine named operators get a lemma each alongside the one
for `bin`, so that a cost computation on a program written with the
abbreviations is simplified by lemmas carrying the same names. -/

















/-! ### The bounded judgment -/































/-! ### The loop rule -/





/-! ### The one frame condition that is worth having generically

A phase lemma states its own frame conditions on the variables and
arrays it touches, because those differ from phase to phase. The output
tape is the exception: almost every phase leaves it alone, and it is
syntactically evident which ones do. So it is stated once, for all
commands that contain no `write`, and no invariant has to carry it. -/

/-- The command contains no `write`. -/
def _root_.Lax808846Proofs.Imp.Com.NoWrite : Com → Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite ∧ d.NoWrite
  | .ite _ c d => c.NoWrite ∧ d.NoWrite
  | .while _ c => c.NoWrite







end Lax808846Proofs.Reasoning

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidSearch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence











def trajectory {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) :
    ℕ → Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)
  | 0 => (1, 0)
  | k + 1 => nextState A b k (trajectory A b k)









/-- A bounded scan stops immediately when its predicate succeeds. -/
def findFirst (p : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | start, count + 1 => if p start then some start else findFirst p (start + 1) count



















end Lax109476Proofs.EllipsoidSearch

end

-- Solutions.RAM_Lax109476Proofs_BinaryOptimization
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.BinaryOptimization







def steps (B : ℕ) : ℕ := 3 * B.size + 2







end Lax109476Proofs.BinaryOptimization

end

-- Solutions.RAM_Lax109476Proofs_PointRecovery
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima LexicographicBounds

def prefixVector {n : ℕ} (x : Fin n → ℚ) (k : ℕ) : Fin n → ℚ :=
  fun j => if j.val < k then x j else 0













end Lax109476Proofs.PointRecovery

end

-- Solutions.RAM_Lax109476Proofs_RamSearchStep
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState EllipsoidSearch RationalArithmeticBounds











def State {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (k : ℕ) (σ : Env) : Prop :=
  Represents "ell.shape" (RamMatrixStorage.flatten (trajectory A b k).1) σ ∧
    Represents "ell.center" (List.ofFn (trajectory A b k).2) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ MatrixRows "search.rows" (fun i j => (A i j : ℚ)) σ ∧
    Represents "search.rhs" (List.ofFn b) σ ∧ σ.vars "vec.n" = n ∧
    σ.vars "row.m" = m ∧ σ.vars "iter.k" = k

-- The iteration-loop proof will use this fixed body and a variant
-- `search.limit - iter.k`; success lowers the limit to the current index.




end Lax109476Proofs.RamSearchStep

end

-- Solutions.RAM_Lax109476Proofs_RamSearchLoop
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSearchStep EllipsoidSearch

def Invariant {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (N : ℕ) (σ : Env) : Prop :=
  ∃ k ≤ N, State A b k σ ∧
    (∀ j < k, RationalSeparation.firstViolation A b (trajectory A b j).2 ≠ none) ∧
    ((σ.vars "search.found" = 0 ∧ σ.vars "search.limit" = N) ∨
      (σ.vars "search.found" = 1 ∧ σ.vars "search.limit" = k ∧
        k < N ∧ RationalSeparation.firstViolation A b (trajectory A b k).2 = none))














end Lax109476Proofs.RamSearchLoop

end

-- Solutions.RAM_Lax109476Proofs_RamSearchBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSearchBounds

open RamTrajectoryBounds RamEllipsoidBitBounds RamEllipsoidStep
open RamDotProduct RamEllipsoidForm















open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamMatrixRows RamRationalArrays RamEllipsoidStep

def Input {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (N : ℕ) (σ : Env) : Prop :=
  MatrixRows "search.rows" (fun i j => (A i j : ℚ)) σ ∧ Represents "search.rhs" (List.ofFn b) σ ∧
    Extents "ell.center" n σ ∧ Extents "ell.shape" (n * n) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ σ.vars "vec.n" = n ∧ σ.vars "row.m" = m ∧ σ.vars "search.budget" = N



end Lax109476Proofs.RamSearchBounds

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryThreshold
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds









def sizeBound (m n M : ℕ) : ℕ :=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M : ℕ) : ℕ :=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)












end Lax109476Proofs.RamRecoveryThreshold

end

-- Solutions.RAM_Lax109476Proofs_RamPointRecoveryStep
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointRecoveryStep

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars RamRecoveryThreshold
open RationalArithmeticBounds PointRecovery





def coordinateCost (S D M m n : ℕ) : ℕ :=
  (144 * M.size + 342 + instructionBound m n (4 * M ^ 2)) * BinaryOptimization.steps D +
    12 * D.size + RamRationalReconstruction.instructionBound S + 48






end Lax109476Proofs.RamPointRecoveryStep

end

-- Solutions.RAM_Lax455465Proofs_SparseRam
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.SparseRam

open Lax808846.Ram

/-- A chronological stack of virtual memory writes, newest first. -/
abbrev Memory := List (ℕ × ℕ)

def lookup : Memory → ℕ → ℕ
  | [], _ => 0
  | (a, v) :: rest, b => if b = a then v else lookup rest b

def write (w : ℕ) (m : Memory) (a v : ℕ) : Memory := (a % 2 ^ w, v % 2 ^ w) :: m



structure SparseState where
  pc : ℕ
  memory : Memory
  input : List ℕ
  inp : List ℕ
  out : List ℕ



def assign (w : ℕ) (s : SparseState) (a v : ℕ) : SparseState :=
  { s with pc := s.pc + 1, memory := write w s.memory a v }

def effect (w : ℕ) : Instr → SparseState → Option SparseState
  | .set a n, s => some (assign w s a n)
  | .load a b, s => some (assign w s a (lookup s.memory (lookup s.memory (b % 2 ^ w) % 2 ^ w)))
  | .store a b, s => some (assign w s (lookup s.memory (a % 2 ^ w)) (lookup s.memory (b % 2 ^ w)))
  | .add a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) + lookup s.memory (c % 2 ^ w)))
  | .sub a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) - lookup s.memory (c % 2 ^ w)))
  | .mul a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) * lookup s.memory (c % 2 ^ w)))
  | .div a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) / lookup s.memory (c % 2 ^ w)))
  | .and a b c, s => some (assign w s a (Nat.land (lookup s.memory (b % 2 ^ w)) (lookup s.memory (c % 2 ^ w))))
  | .shiftl a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) * 2 ^ lookup s.memory (c % 2 ^ w)))
  | .not a b, s => some (assign w s a (2 ^ w - 1 - lookup s.memory (b % 2 ^ w)))
  | .jump l, s => some { s with pc := l }
  | .jzero a l, s => some { s with pc := if lookup s.memory (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | .jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | .inputLength a, s => some (assign w s a s.input.length)
  | .inputLoad a b, s => some (assign w s a (s.input[lookup s.memory (b % 2 ^ w) % 2 ^ w]?.getD 0))
  | .halt, _ => none
  | .read a, s => s.inp.head?.map fun v => { assign w s a v with inp := s.inp.tail }
  | .write a, s => some { s with pc := s.pc + 1, out := s.out ++ [lookup s.memory (a % 2 ^ w) % 2 ^ w] }



def step (w : ℕ) (p : Program) (s : SparseState) : Option SparseState :=
  p[s.pc]?.bind fun i => effect w i s



def run (w : ℕ) (p : Program) : ℕ → SparseState → Option SparseState
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

def init (x : List ℕ) : SparseState := ⟨0, [], x, x, []⟩



















end Lax455465Proofs.SparseRam

end

-- Solutions.RAM_Lax455465Proofs_RamSparseRead
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSparseRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSparseMemory

def Representation (records : List (ℕ × ℕ)) (σ : Env) : Prop :=
  (∀ i (hi : i < records.length), (σ.arrs "vm.addresses")[i]? = some records[i].1 ∧
    (σ.arrs "vm.values")[i]? = some records[i].2) ∧ σ.vars "vm.count" = records.length













end Lax455465Proofs.RamSparseRead

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualCore
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualCore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualProgram RamSparseRead

/-- The virtual machine owns only its reserved buffers and registers. -/
def Core (w pc : ℕ) (m : SparseRam.Memory) (σ : Env) : Prop :=
  Representation m.reverse σ ∧ σ.vars "vm.pc" = pc ∧
  σ.vars "vm.modulus" = 2 ^ w ∧ σ.vars "vm.width" = w















end Lax455465Proofs.RamVirtualCore

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualState
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualCore RamVirtualProgram



def Tapes (s : SparseRam.SparseState) (σ : Env) : Prop :=
  Prefix s.input "vm.input" σ ∧ σ.vars "vm.inputLength" = s.input.length ∧
  σ.vars "vm.cursor" ≤ s.input.length ∧ s.inp = s.input.drop (σ.vars "vm.cursor") ∧
  Prefix s.out "vm.output" σ ∧ σ.vars "vm.outputLength" = s.out.length

def Represents (w : ℕ) (s : SparseRam.SparseState) (σ : Env) : Prop :=
  Core w s.pc s.memory σ ∧ Tapes s σ









end Lax455465Proofs.RamVirtualState

end

-- Solutions.RAM_Lax455465Proofs_RamFlowData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFlowData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat




def capacities {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) : List ℚ≥0 :=
  List.ofFn fun e : Fin (n*n) => I.capacity ((edgeIndex n).symm e).1 ((edgeIndex n).symm e).2

/-- Initialized graph data and dimensions shared by all construction loops. -/
def Data {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (σ : Env) : Prop :=
  σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧ σ.vars "lp.n3" = (n*n)*n ∧
    σ.vars "lp.rows" = rows n ∧ σ.vars "lp.columns" = columns n ∧
    σ.vars "lp.matrixLength" = rows n*columns n ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
    Prefix (RamUnsignedBuffer.encode (capacities I)) "flow.capacities" σ





end Lax455465Proofs.RamFlowData

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualInstruction
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualInstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState

/-- Only the finitely many literal operands of the fixed source program
need a native bound; virtual addresses themselves may span its whole word. -/
def LiteralsFit (B : ℕ) : Lax808846.Ram.Instr → Prop
  | .set a v => a < B ∧ v < B
  | .load a b | .store a b | .not a b | .inputLoad a b => a < B ∧ b < B
  | .add a b c | .sub a b c | .mul a b c | .div a b c | .and a b c | .shiftl a b c =>
      a < B ∧ b < B ∧ c < B
  | .jzero a l => a < B ∧ l < B
  | .jump l | .jeof l => l < B
  | .inputLength a | .read a | .write a => a < B
  | .halt => True







end Lax455465Proofs.RamVirtualInstruction

end

-- Solutions.RAM_Lax455465Proofs_RamHostBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamHostBounds

/-- This sufficient host width is polynomial whenever the virtual width,
source time and input length are polynomial. Program allowance is fixed. -/
def sufficient (w time allowance inputLength : ℕ) : ℕ :=
  2 * w + time + allowance + inputLength + 8



end Lax455465Proofs.RamHostBounds

end

-- Solutions.RAM_Lax455465Proofs_RationalDistances
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! Exact min-plus shortest distances. The algorithm has n pivots, each
updating n² rational coordinates, and does not enumerate paths. -/

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances



def Nonnegative {n : ℕ} (d : Distance n) : Prop := ∀ u v, 0 ≤ d u v



































theorem nonnegative_zeroDiagonal {n : ℕ} (d : Distance n) (h : Nonnegative d) :
    Nonnegative (zeroDiagonal d) := by
  intro u v
  unfold zeroDiagonal
  split_ifs; exact le_rfl; exact h u v











end Lax455465Proofs.RationalDistances

end

-- Solutions.RAM_Lax455465Proofs_MetricMatrix
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat









def step {n : ℕ} (d : Matrix n) (p : Fin n) : Matrix n :=
  fun u v => min (d u v) (d u p+d p v)





def iterate {n : ℕ} (d : Matrix n) : List (Fin n) → Matrix n
  | [] => d
  | p :: ps => iterate (step d p) ps











end Lax455465Proofs.MetricMatrix


end

-- Solutions.RAM_Lax455465Proofs_RamDualDistancesInit
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

def matrix {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) : Matrix n :=
  fun u v => ⟨RationalDistances.zeroDiagonal (DirectedFlowDual.length y) u v,by
    apply RationalDistances.nonnegative_zeroDiagonal
    intro u v
    exact hy _⟩























end Lax455465Proofs.RamDualDistancesInit

end

-- Solutions.RAM_Lax455465Proofs_RamDualDistances
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamDualDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat



def result {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) : Matrix n :=
  iterate (RamDualDistancesInit.matrix y hy) (List.finRange n)





end Lax455465Proofs.RamDualDistances

end

-- Solutions.RAM_Lax455465Proofs_VolumeHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.VolumeHeight

open LpInputSize MetricMatrix
open scoped NNRat

def sumExponent (n w : ℕ) : ℕ := 4*w*(n*n+1)+n*n+1
def exponent (n w : ℕ) : ℕ := 3*sumExponent n w+1





end Lax455465Proofs.VolumeHeight

end

-- Solutions.RAM_Lax455465Proofs_RegionQueryHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionQueryHeight

open RegionQueryData LpInputSize
open scoped NNRat

def exponent (n w : ℕ) : ℕ := 2*VolumeHeight.exponent n w+w+1





end Lax455465Proofs.RegionQueryHeight

end

-- Solutions.RAM_Lax455465Proofs_LargePotentialData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.LargePotentialData
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat












def exponent (n w : ℕ) : ℕ := 2*w*(n+1)+n+1





end Lax455465Proofs.LargePotentialData

end

-- Solutions.RAM_Lax455465Proofs_RamLargePotential
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  distances : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  inMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tin)) "region.inMask" σ
  outMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tout)) "region.outMask" σ
















end Lax455465Proofs.RamLargePotential

end

-- Solutions.RAM_Lax455465Proofs_CutScoreHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.CutScoreHeight
open Lax455465.RationalEncoding LpInputSize CutScoreData
open scoped NNRat

def sumExponent (n w : ℕ) : ℕ := w*(n*n+1)+n*n+1
def exponent (n w : ℕ) : ℕ := 3*sumExponent n w





end Lax455465Proofs.CutScoreHeight

end

-- Solutions.RAM_Lax455465Proofs_RamLargeCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargeCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped BigOperators NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (σ : Env) : Prop where
  potential : RamLargePotential.Input I d Tin Tout σ
  n2Value : σ.vars "metric.n2"=n*n
  total : Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialRoom : RamLargePotential.Room n σ
  maskRoom : 2*n<(σ.arrs "cut.flags").length
  crossingRoom : 2*(n*n)<(σ.arrs "cut.crossing").length








end Lax455465Proofs.RamLargeCut

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext RamRegionRecord
open Lax455465.RationalEncoding
open scoped BigOperators NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (history : List (Entry n)) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  historyPosition : σ.vars "history.pos"=4*history.length
  metric : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  records : Prefix (words history) "region.history" σ
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  total : Stored "round.total" (RamRoundingInit.total I.weight) σ
  potentialRoom : 2*n < (σ.arrs "cut.potential").length
  maskRoom : 2*n < (σ.arrs "cut.flags").length
  crossingRoom : 2*(n*n) < (σ.arrs "cut.crossing").length








end Lax455465Proofs.RamHistoryCut

end

-- Solutions.RAM_Lax455465Proofs_RamZeroCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamZeroCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP
open scoped BigOperators NNRat












def prepareCost (n : ℕ) : ℕ := 98*(n*n)+66*n+38

def cost (n M : ℕ) : ℕ := prepareCost n+RamPotentialSweep.cost n M





end Lax455465Proofs.RamZeroCut

end

-- Solutions.RAM_Lax455465Proofs_RegionIterationHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionIterationHeight
open LpInputSize Lax455465.RationalEncoding
open scoped NNRat

def exponent (n w : ℕ) : ℕ := RegionQueryHeight.exponent n (2*w)



end Lax455465Proofs.RegionIterationHeight

end

-- Solutions.RAM_Lax455465Proofs_RoundingHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RoundingHeight
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat





def cutExponent (n w : ℕ) : ℕ :=
  2*w+CutScoreHeight.exponent n w+LargePotentialData.exponent n w+2*n+4



def constantExponent (w : ℕ) : ℕ := 3*w+2



end Lax455465Proofs.RoundingHeight

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingBudget
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRoundingBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionContext
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def constants (w : ℕ) : ℕ := RoundingHeight.constantExponent w
def queries (n w : ℕ) : ℕ := RegionIterationHeight.exponent n (constants w)
def cuts (n w : ℕ) : ℕ := RoundingHeight.cutExponent n (constants w)
def width (n w : ℕ) : ℕ := RamHostBounds.sufficient (constants w+queries n w+cuts n w) 0 0 (2*n*n+12*n+20)

def cost (n p w : ℕ) (total : ℚ≥0) : ℕ :=
  ((36*((2^(constants w))^2).size+200)*(n+1)+600*((2^(constants w))^2).size+2000)+
    (36*(total.den*3).size+28*n+116+RamRegionBoundedLoop.cost n p (2^(constants w)) (queries n w)+
      RamRegionCut.cost n p (2^(cuts n w))+RamZeroCut.cost n (2^(cuts n w)))









end Lax455465Proofs.RamRoundingBudget

end


