-- Prove2me | Definitions.Def_CountingMatroid_Model_Run
-- name    : CountingMatroid_Model_Run
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:40:57.059336+00:00
-- url     : https://prove2.me/theorems/a82cf441-9712-40d8-8d70-1e6fb856d991
-- title:
--   Finite fair-bit blocks and the law of the charged estimator
-- statement:
--   The one-bit distribution `fairBitLaw` assigns each Boolean probability $1/2$. For $m\in\mathbb N$, `fairTape(m)` recursively draws $m$ independent bits and returns their list; the base case returns the empty list. For $k,\ell\in\mathbb N$, `fairBlocks(k,ℓ)` recursively draws $k$ independent lists with law `fairTape(ℓ)`.
--
--   Let $n,r\in\mathbb N$, let $p=(\varepsilon,\delta)$ consist of rational inputs in $(0,1)$, and let $s$ be the value of the charged schedule computation on $(n,p)$. Write $L=s.L$, $N=s.\mathrm{observations}$, $M=s.\mathrm{drawCalls}$, and $T=s.\mathrm{drawTrials}$. Let $b$ be the model’s binary input length: the sum of the natural binary lengths of $n,r$ and rational encoding lengths of $\varepsilon,\delta$. Natural length assigns one digit to zero; rational length is two plus the lengths of the absolute reduced numerator and positive denominator. Define
--   $$w=10^6(L+1)^4(n+1)^4(N+1)^4(b+1)^4,$$
--   $$\operatorname{blockLength}(n,r,p)=nL+M(1+Tw)+10.$$
--   For a list of bit blocks $B$ and indices $i,j\in\mathbb N$, `blockTape(B,i,j)` returns bit $j$ in block $i$, defaulting to false if either lookup is out of range.
--
--   Given a feasibility implementation $F$ and arbitrary Boolean independence-query functions $o_1,o_2$ on $[n]$, `algorithmLaw` samples $s.\mathrm{repetitions}$ independent blocks of this length and maps them through the single charged estimator execution using $F,n,r,o_1,o_2,p$ and the resulting block tape. `outputLaw` projects that same random execution $E$ to
--   $$\left(E.\mathrm{value},\ \bigl(Q(E),W(E),\operatorname{cost}_E(\mathrm{fairBit})\bigr)\right),$$
--   where $Q$ counts the two original-oracle components and $W$ counts fair-bit plus nonoracle word-operation charges. The three record fields are named `oracleCalls`, `bitOps`, and `randomBits`. This defines a joint distribution of the rational answer and its counters, including executions that encounter an abort branch; sampling the full product distribution is distributional semantics, not a charge for eagerly generating unused bits.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Model/Run.lean#L28-L81

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
# Fair-bit source and law of the charged estimator

Correspondence ledger: main.tex:102–103 and 1392–1421 give the independent
unbiased bits of `fairBitLaw`; `fairTape` and `fairBlocks` recursively generate
fresh bits for each bounded run. The chosen `blockLength` uses the very
`Program.schedule` value used by the charged estimator, so the schedule is not
restated. Its deliberately coarse polynomial width must still be proved to
cover every rational acceptance denominator before the output law can support
the paper's accuracy proof. `algorithmLaw` maps each block to one invocation of
`Program.estimate`; `outputLaw` records the value and the costs of that same
charged execution. Drawing a full product tape here is distribution semantics,
not an instruction to eagerly generate or charge unused bits.
-/

namespace CountingMatroid.Model.Run

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- One independent unbiased Boolean draw. -/
noncomputable def fairBitLaw : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => 1 / 2)
    (by simpa [Fintype.sum_bool, two_mul] using (ENNReal.add_halves (1 : ENNReal)))

/-- A finite product of fresh fair bits, by recursion so the cons case unfolds. -/
noncomputable def fairTape : (m : ℕ) → PMF (List Bool)
  | 0 => pure []
  | m + 1 => do
      let bit ← fairBitLaw
      let rest ← fairTape m
      pure (bit :: rest)

/-- A coarse finite tape block for one run. The budget depends on the actual
schedule declaration; proving sufficient rational width is outstanding. -/
noncomputable def blockLength (n r : ℕ) (p : InputParams) : ℕ :=
  let s := (CountingMatroid.Program.schedule n p).val
  let width := 1000000 * (s.L + 1) ^ 4 * (n + 1) ^ 4 *
    (s.observations + 1) ^ 4 * (binaryInputLength n r p + 1) ^ 4
  n * s.L + s.drawCalls * (1 + s.drawTrials * width) + 10

/-- Fresh, disjoint finite bit blocks for all median repetitions. -/
noncomputable def fairBlocks (m length : ℕ) : PMF (List (List Bool)) :=
  match m with
  | 0 => pure []
  | m + 1 => do
      let block ← fairTape length
      let remaining ← fairBlocks m length
      pure (block :: remaining)

/-- Out-of-range accesses read a deterministic default; the tape-coverage
proof must show the estimator never reaches one on a promised input. -/
def blockTape (blocks : List (List Bool)) (run bit : ℕ) : Bool :=
  ((blocks[run]?).getD [])[bit]?.getD false

/-- Distribution of charged executions of the one program. -/
noncomputable def algorithmLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    PMF (Arlib.Computation.Charged Op Cell ℚ) := do
  let repetitions := (CountingMatroid.Program.schedule n p).val.repetitions
  let blocks ← fairBlocks repetitions (blockLength n r p)
  pure (CountingMatroid.Program.estimate solver n r o₁ o₂ p
    (blockTape blocks))

/-- The rational answer and separate counters are projections of the same
charged execution, including all work on abort paths. -/
noncomputable def outputLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    PMF (ℚ × ExecutionCost) := do
  let run ← algorithmLaw solver n r o₁ o₂ p
  pure (run.val,
    { oracleCalls := oracleCalls run,
      bitOps := otherSteps run,
      randomBits := run.cost Op.fairBit })

end CountingMatroid.Model.Run






end


