-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
-- name    : CountingMatroid_Analysis_ScheduleThermalSetupCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:42:41.989596+00:00
-- url     : https://prove2.me/theorems/86258b22-9a81-4bf8-85b0-0655c9a04b86
-- title:
--   Thermal schedule setup and its charged continuation
-- statement:
--   Let $n\in\mathbb N$ and let $p=(\varepsilon,\delta)$ contain rational inputs satisfying $0<\varepsilon<1$ and $0<\delta<1$. An opening record supplies natural fields $b$ and $v$ and a rational field $\rho$; its field names are `bε`, `twoN`, and `rho`. A `ThermalResult` stores such an opening record together with natural fields $L,h,D$ and a rational field $\eta$, where $h$ is named `LPlusOne`.
--
--   The charged function `thermalSetup` takes the supplied opening record and computes
--   $$L=v(n+b),\qquad h=L+1,\qquad D=32h,\qquad \eta=\frac{\varepsilon}{D},$$
--   returning all these values with that record. The supplied field $v$ is used directly; its equality with $2n$ is not imposed by the record type.
--
--   The charged continuation `thermalRest` accepts any thermal record. Using its actual fields $b,\rho,L,h,\eta$, it computes
--   $$\tau=20n^4(nh+2),\qquad R=2000h^2n^2\tau,$$
--   $$N=\max\!\left(0,\left\lceil\frac{10^{10}hn^{14}}{\eta^2}\right\rceil\right),\qquad M=3L(R+N).$$
--   It obtains $T$ from the imported bounded `leastDrawTrials` search on $M$, obtains $b_\delta$ from the imported bounded `leastHalvings` search on $\delta$, and sets $m=10b_\delta+1$. It returns the annealing schedule with fields
--   $$(b,\rho,L,\eta,\tau,R,N,M,T,b_\delta,m),$$
--   representing the accuracy exponent, cooling factor, phase count, relative tolerance, trace length, restart cap, observation count, draw-call budget, draw-trial cap, confidence exponent, and repetition count. Each arithmetic and search operation remains inside the charged computation. Rational division is total, including division by zero. This bundle splits schedule construction into a setup stage and its continuation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleThermalSetupCost.lean#L7-L59

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
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
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
/-- INTERNAL: Values passed from the thermal setup to the schedule tail. -/
structure ThermalResult where
  opening : ScheduleOpeningResult
  L : ℕ
  LPlusOne : ℕ
  D : ℕ
  eta : ℚ
/-- INTERNAL: The charged setup of phase count and annealing accuracy.
TEXLINE: main.tex:1348-1358 -/
def thermalSetup (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    Arlib.Computation.Charged Op Cell ThermalResult := do
  let nPlusB ← natAdd n head.bε
  let L ← natMul head.twoN nPlusB
  let LPlusOne ← successor L
  let D ← natMul 32 LPlusOne
  let etaDen ← ratOfNat D
  let eta ← ratDiv p.ε etaDen
  pure ⟨head, L, LPlusOne, D, eta⟩
/-- INTERNAL: The schedule tail after thermal setup.
TEXLINE: main.tex:1348-1358 -/
def thermalRest (n : ℕ) (p : InputParams) (result : ThermalResult) :
    Arlib.Computation.Charged Op Cell AnnealingSchedule := do
  let b := result.opening.bε
  let rho := result.opening.rho
  let L := result.L
  let eta := result.eta
  let LPlusOne := result.LPlusOne
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


