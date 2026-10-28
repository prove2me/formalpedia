-- Prove2me | Definitions.Def_CountingMatroid_Interface_Pseudocode
-- name    : CountingMatroid_Interface_Pseudocode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:42:08.284129+00:00
-- url     : https://prove2.me/theorems/b86f28c7-66c9-43f5-a975-068b273fe668
-- title:
--   Rational median with a default for the empty list
-- statement:
--   Let $a$ be a finite list of rational numbers, let $m=|a|$ be its length, and let $a^{\uparrow}$ be its insertion-sorted list in nondecreasing order. With zero-based indexing, define
--   $$\operatorname{median}(a)=\begin{cases}a^{\uparrow}_{\lfloor m/2\rfloor},&m>0,\\0,&m=0.\end{cases}$$
--   Thus an odd-length list returns its middle entry, while a nonempty even-length list returns its upper middle entry. The implementation performs an optional list lookup and uses rational zero as the default when no entry exists. This is the pure answer-level median used by the estimator’s repetition interface.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Interface/Pseudocode.lean#L138-L140

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

section


set_option autoImplicit false

/-!
# Mathematical answer side of the annealing program

Correspondence ledger (paper location → this file → charged program):
* main.tex:283–293, exact pretest → `pretest` → `Program.preprocess`.
* main.tex:1105–1150, schedule and initial multipliers → `setup`,
  `initialMultipliers` → `Program.schedule`, `Operations.initialWeights`.
* main.tex:746–751, lazy exchange → `chainStep`, `chainStepLaw` →
  `Program.chainStep`; its classification and paired rank are evaluated there.
* main.tex:1163–1176, fresh transversal and capped trace restart →
  `freshTransversal`, `traceReturn`, `restartPhase` → the identically named
  declarations in `Program`.
* main.tex:1177–1187, consecutive observations → `observePhase` →
  `Program.observePhase` (including `Program.recordObservation`).
* main.tex:1188–1201, zero-frequency abort, ratio, multiplier update →
  `finishPhase` → `Program.finishPhase`.
* main.tex:1202–1205, zero on abort and scaled product → `singleRun` →
  `Program.boundedRun`.
* main.tex:1392–1421, capped binary rejection, including `v=1` →
  `boundedDraw` → `Program.boundedUniform`.
* main.tex:1442–1448, independent runs and median → `median`, `estimate`,
  `estimateLaw` → `Program.medianRational`, `Program.estimate`,
  `Model.Run.fairBlocks` and `Model.Run.algorithmLaw`.
* main.tex:226–229 and 699–702, partition sums and transport: analysis only;
  there is no executable pseudocode or program step for them.

There are two algorithm definitions for a reason. The charged program preserves
its sequence of dictionary operations, which is the object of resource analysis;
a sealed dictionary also remembers order and update history, so equal sets can
be different program terms. Correctness compares laws of extensional sets and
therefore uses `Finset` and `PMF` here. In the present Model the charged paired
state itself is already a `Finset`, but its operations and control flow remain
inside `Charged`. The pure answer composition below removes those charges and
uses Mathlib's extensional state and probability notions. The bridge must show
that this composition has the charged program's answer law.

MODEL: `FeasibilityImplementation` is a parameter, not the cited concrete
polynomial matroid-intersection pretest (main.tex:283–289). Consequently the
algorithm is conditional on a missing implementation. The program also has no
proved RAM realization of its arithmetic or bit operations, and no proof that
`Model.Run.blockLength` covers every fair-bit read. These are program-side gaps,
not extra inputs or hypotheses added here. The full mathematical transition is
kept tape-relative; `chainStepLaw` draws from the same finite fair-bit product
used by `Model.Run`, with the same default for an exhausted block.
-/

namespace CountingMatroid.Interface.Pseudocode

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

























/-- Rational median used after the odd number of independent runs. -/
noncomputable def median (answers : List ℚ) : ℚ :=
  ((answers.insertionSort (· ≤ ·))[answers.length / 2]?).getD 0





end CountingMatroid.Interface.Pseudocode

end


