-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
-- name    : CountingMatroid_Analysis_ScheduleOpeningCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:42:02.847496+00:00
-- url     : https://prove2.me/theorems/4e02fe91-2609-4457-be1b-8409604027f7
-- title:
--   Opening and remaining stages of the annealing schedule
-- statement:
--   Let $n\in\mathbb N$ and let the input parameters be rational numbers $0<\varepsilon,\delta<1$. An opening result is a triple $(b,\rho,m)$ consisting of two natural numbers $b,m$ and a rational $\rho$. The charged opening procedure computes $$b=\operatorname{leastHalvings}(\varepsilon/10),\qquad m=2n,\qquad \rho=1-\frac1m.$$ Here leastHalvings is the imported bounded halving search, and division is total rational division.
--
--   Given any opening result $(b,\rho,m)$, the remaining procedure constructs an annealing schedule using $$L=m(n+b),\qquad \eta=\frac{\varepsilon}{32(L+1)},\qquad \tau=20n^4\bigl(n(L+1)+2\bigr),$$ $$A=2000(L+1)^2n^2\tau,\qquad M=\max\!\left(0,\left\lceil\frac{10^{10}(L+1)n^{14}}{\eta^2}\right\rceil\right),\qquad D=3L(A+M).$$ The fields $A,M,D$ are the restart-attempt cap, observation count, and draw-call budget. The draw-trial cap is the imported bounded search $\operatorname{leastDrawTrials}(D)$; the failure-accuracy search is $b_\delta=\operatorname{leastHalvings}(\delta)$; the repetition count is $10b_\delta+1$. Every arithmetic step is sequenced through the charged primitives.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleOpeningCost.lean#L7-L61

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
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
/-- INTERNAL: Values passed from the first six charged schedule operations. -/
structure ScheduleOpeningResult where
  bε : ℕ
  rho : ℚ
  twoN : ℕ
/-- INTERNAL: The initial accuracy search and inverse-temperature setup.
TEXLINE: main.tex:1348-1351 -/
def scheduleOpening (n : ℕ) (p : InputParams) :
    Arlib.Computation.Charged Op Cell ScheduleOpeningResult := do
  let epsilonTenth ← ratDiv p.ε 10
  let bε ← CountingMatroid.Program.leastHalvings epsilonTenth
  let twoN ← natMul 2 n
  let twoNq ← ratOfNat twoN
  let inverseTwoN ← ratDiv 1 twoNq
  let rho ← ratSub 1 inverseTwoN
  pure ⟨bε, rho, twoN⟩
/-- INTERNAL: The remainder of the schedule after its first six operations.
TEXLINE: main.tex:1348-1358 -/
def scheduleRemaining (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    Arlib.Computation.Charged Op Cell AnnealingSchedule := do
  let b := head.bε
  let rho := head.rho
  let twoN := head.twoN
  let nPlusB ← natAdd n b
  let L ← natMul twoN nPlusB
  let LPlusOne ← successor L
  let etaDenNat ← natMul 32 LPlusOne
  let etaDen ← ratOfNat etaDenNat
  let eta ← ratDiv p.ε etaDen
  let nFourth ← CountingMatroid.Program.natPower n 4
  let nTimesL ← natMul n LPlusOne
  let traceInner ← natAdd nTimesL 2
  let traceScale ← natMul 20 nFourth
  let tau ← natMul traceScale traceInner
  let LSquare ← CountingMatroid.Program.natPower LPlusOne 2
  let nSquare ← CountingMatroid.Program.natPower n 2
  let restartFactor ← natMul 2000 LSquare
  let restartFactor ← natMul restartFactor nSquare
  let restartCap ← natMul restartFactor tau
  let nFourteenth ← CountingMatroid.Program.natPower n 14
  let observationFactor ← natMul 10000000000 LPlusOne
  let observationFactor ← natMul observationFactor nFourteenth
  let observationNumerator ← ratOfNat observationFactor
  let etaSquare ← ratMul eta eta
  let observationQuotient ← ratDiv observationNumerator etaSquare
  let observations ← rationalCeil observationQuotient
  let attemptsAndObservations ← natAdd restartCap observations
  let threeL ← natMul 3 L
  let drawCalls ← natMul threeL attemptsAndObservations
  let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
  let bδ ← CountingMatroid.Program.leastHalvings p.δ
  let tenBδ ← natMul 10 bδ
  let repetitions ← successor tenBδ
  pure (AnnealingSchedule.mk b rho L eta tau restartCap observations
    drawCalls drawTrials bδ repetitions)









end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end


