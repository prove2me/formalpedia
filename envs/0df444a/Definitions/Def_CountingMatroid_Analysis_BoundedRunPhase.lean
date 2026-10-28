-- Prove2me | Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
-- name    : CountingMatroid_Analysis_BoundedRunPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:41:39.224989+00:00
-- url     : https://prove2.me/theorems/30e379c4-4d87-40b9-83b7-5a52a736941c
-- title:
--   A bounded annealing phase and its size invariant
-- statement:
--   Let $n\in\mathbb N$ and let $s$ be an annealing schedule with cooling factor $\rho$, phase count $L$, trace length $\tau$, restart cap $R$, observation count $N$, and draw-trial cap $T$. Write $\ell(q)$ for the model’s rational encoding length: two plus the binary lengths of the absolute reduced numerator and positive denominator, assigning one digit to zero. Define
--   $$\operatorname{runSize}(n,s)=n+L+\tau+R+N+T+\ell(\rho)+1.$$
--
--   For $r,j\in\mathbb N$, arbitrary Boolean independence-query functions $o_1,o_2$ on $[n]$, and a tape $t:\mathbb N\to\{0,1\}$, `boundedRunPhase` transforms an optional annealing cursor by a charged computation. A missing cursor remains missing. Otherwise it computes $q=\rho^j$, performs the restart with the stored tables and current tape position, observes using $q$ and current weights, and finishes the phase. A failure in any of these calls returns a missing cursor. If finishing returns a ratio $a$ and weights $w'$, it multiplies the old product $P$ by $a$, writes $w'$ to table index $j+1$ only when $j+1<L$, and returns the updated cursor with current weights $w'$, product $Pa$, and the observation output’s tape position.
--
--   For natural numbers $S_0,j$ and an optional cursor $c$, `PhaseSizeInvariant(S₀,j,c)` means that every actual cursor carried by $c$ satisfies
--   $$\ell(w_i)\le(j+1)S_0^{10},\qquad\ell(w_i^{(a)})\le(j+1)S_0^{10},\qquad\ell(P)\le(j+1)S_0^{10}$$
--   for every distinct ordered defect index $i$ in $[n]$ and every table index $a\in\mathbb N$. Here $w_i$, $w_i^{(a)}$, and $P$ are its current multiplier, stored multiplier, and product. A missing cursor satisfies the invariant vacuously. The size parameter $S_0$ is arbitrary in this predicate; the definition does not require it to equal `runSize`. These declarations name the phase body and the operand-size condition used by subsequent induction arguments.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhase.lean#L15-L66

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
A definitional name for the body of the bounded-run phase loop and the
rational-size invariant used by its work proof. The phase code is identical
to the lambda in `Program.boundedRun`; it adds no algorithmic assumption.
-/

namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: The input size used by the bounded-run work envelope.
TEXLINE: main.tex:1348-1440 -/
def runSize (n : ℕ) (s : AnnealingSchedule) : ℕ :=
  n + s.L + s.τ + s.restartCap + s.observations +
    s.drawTrials + binaryRatLength s.ρ + 1

/-- INTERNAL: Name the exact phase-loop body so value and work induction share it.
TEXLINE: main.tex:1163-1201,1348-1440 -/
def boundedRunPhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (current : Option (AnnealingCursor n)) :
    Arlib.Computation.Charged Op Cell (Option (AnnealingCursor n)) := do
match current with
| none => pure none
| some current =>
    let q ← ratPower s.ρ j
    let started ← restartPhase r o₁ o₂ tape s current.tables j
      current.bitCursor
    match started with
    | none => pure none
    | some started =>
        let observed ← observePhase r o₁ o₂ tape s q
          current.currentWeights started
        match observed with
        | none => pure none
        | some observed =>
            let finished ← finishPhase s j current.currentWeights observed
            match finished with
            | none => pure none
            | some (ratio, nextWeights) =>
                let product ← ratMul current.product ratio
                let next ← successor j
                let update ← lessThan next s.L
                if update then
                  let tables ← learnedWeightWrite current.tables next s.L
                    nextWeights
                  pure (some ⟨tables, nextWeights, product,
                    observed.bitCursor⟩)
                else pure (some ⟨current.tables, nextWeights, product,
                  observed.bitCursor⟩)

/-- INTERNAL: All stored and current multipliers and the accumulated ratio
product have length at most a phase-linear budget. The aborted state satisfies
this vacuously. This deliberately loose budget avoids needing each table entry
to be updated only once in the nested finish-phase scan.
TEXLINE: main.tex:1356-1390 -/
def PhaseSizeInvariant {n : ℕ} (S j : ℕ)
    (acc : Option (AnnealingCursor n)) : Prop :=
  ∀ current, acc = some current →
    (∀ index, binaryRatLength (current.currentWeights index) ≤ (j + 1) * S ^ 10) ∧
    (∀ phase index, binaryRatLength (current.tables phase index) ≤ (j + 1) * S ^ 10) ∧
    binaryRatLength current.product ≤ (j + 1) * S ^ 10

end CountingMatroid.Analysis.BoundedRunPhase

end


