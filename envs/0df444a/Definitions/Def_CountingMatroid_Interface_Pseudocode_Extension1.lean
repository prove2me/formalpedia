-- Prove2me | Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
-- name    : CountingMatroid_Interface_Pseudocode_Extension1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:21.17605+00:00
-- url     : https://prove2.me/theorems/a53fe855-ecbc-407a-95fd-84ece10f5b87
-- title:
--   Value-level estimator and finite-block output law
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean independence-query functions on $[n]$, and let $F$ be a feasibility implementation. For rational input parameters $p=(\varepsilon,\delta)$ with $0<\varepsilon,\delta<1$, the bundle defines the returned values of preprocessing and schedule construction, the single-run output $Y(u,s)$ of a capped run from bit position zero, and their composition. A preliminary answer is returned immediately; otherwise, with $N=s.\mathrm{repetitions}$ and a supplied family of tapes $u_j:\mathbb N\to\{0,1\}$,
--   $$\operatorname{estimate}(u)=\operatorname{median}\bigl(Y(u_0,s),\ldots,Y(u_{N-1},s)\bigr).$$
--   A capped-run abort returns zero. The output probability law samples $N$ independent fair blocks of length $m=\operatorname{blockLength}(n,r,p)$, extends each by false bits, and applies this estimator:
--   $$\operatorname{estimateLaw}=\operatorname{estimate}_*\operatorname{fairBlocks}(N,m).$$
--   These are value-level definitions, with no correctness contract on the feasibility implementation or query functions and no asserted accuracy or concrete-machine cost bound.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Interface/Pseudocode.lean#L58-L61

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Interface_Pseudocode
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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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

/-- Exact empty-ground/feasibility dispatch. `none` enters annealing. -/
noncomputable def pretest (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) : Option ℚ :=
  (CountingMatroid.Program.preprocess solver n r o₁ o₂).val

/-- The paper's rational and integral schedule, evaluated by the same formulas
as the charged setup. -/
noncomputable def setup (n : ℕ) (p : InputParams) : AnnealingSchedule :=
  (CountingMatroid.Program.schedule n p).val



















/-- One capped run, with zero as the answer on every abort branch. -/
noncomputable def singleRun {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) : ℚ :=
  (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1



/-- Pure answer composition on already supplied fair-bit streams. The list
order is immaterial to the median; the charged program builds it by cons. -/
noncomputable def estimate (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) : ℚ :=
  match pretest solver n r o₁ o₂ with
  | some answer => answer
  | none =>
      let s := setup n p
      median ((List.range s.repetitions).map fun j =>
        singleRun r o₁ o₂ (tape j) s)

/-- The answer law under fresh independent fair-bit blocks, using precisely
`Model.Run`'s block length and exhausted-block convention. -/
noncomputable def estimateLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) : PMF ℚ := do
  let s := setup n p
  let blocks ← CountingMatroid.Model.Run.fairBlocks s.repetitions
    (CountingMatroid.Model.Run.blockLength n r p)
  pure (estimate solver n r o₁ o₂ p
    (CountingMatroid.Model.Run.blockTape blocks))

end CountingMatroid.Interface.Pseudocode

end


