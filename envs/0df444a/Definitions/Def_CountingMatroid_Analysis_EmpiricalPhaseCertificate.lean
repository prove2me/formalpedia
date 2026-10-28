-- Prove2me | Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
-- name    : CountingMatroid_Analysis_EmpiricalPhaseCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:10.224075+00:00
-- url     : https://prove2.me/theorems/5e97b44a-7977-4e34-b713-51b67feebb89
-- title:
--   Raw empirical estimates and their phase-execution certificate
-- statement:
--   Fix a ground size $n\in\mathbb N$. Let $s$ be a schedule with $N$ observations and relative-error parameter $\eta$, let $w$ be a rational table indexed by ordered distinct empty/full pair indices $d$, and let an observed cursor contain transversal count $K_0$, defect counts $K_d$, and numerator sum $B$. For rational $R$ and tables $I,I^+$, the predicate $\operatorname{ObservationEstimates}$ requires witnesses $p_0\in\mathbb Q$ and $p_d\in\mathbb Q$ such that $N>0$, $p_0>0$, $R>0$, and
--   $$\begin{aligned}
--   (1-\eta)p_0&\leq K_0/N\leq(1+\eta)p_0,\\
--   (1-\eta)p_0R&\leq B/N\leq(1+\eta)p_0R.
--   \end{aligned}$$
--   For every defect index $d$, it additionally requires
--   $$w_d>0,\quad p_d>0,\quad \frac{w_dp_0}{p_d}=I_d,\quad
--   \frac{I_d}{2}\leq I_d^+\leq2I_d,\quad
--   (1-\eta)p_d\leq K_d/N\leq(1+\eta)p_d.$$
--   The means are existential witnesses; no independence of the recorded observations is assumed.
--
--   The second predicate fixes a natural rank parameter $r$, independence oracles, a Boolean tape, and a phase $j$. Write $C_a$ for the transversal partition sum at $\rho^a$ and $D_{a,d}$ for the unmultiplied operational partition sum of defect class $d$ at that parameter, and set $I_{a,d}=C_a/D_{a,d}$. It requires an annealing cursor actually reached by the phase history, a successful capped restart from its stored tables and bit cursor, and a successful observation phase at $\rho^j$ using its current weights. Every stored table at level $a\leq j$ must lie between $I_{a,d}/4$ and $4I_{a,d}$, and the current weights satisfy the analogous level-$j$ bounds. The returned observation cursor must satisfy the first predicate with
--   $$R=C_{j+1}/C_j,\qquad I=I_j,\qquad I^+=I_{j+1}.$$
--   This certificate exposes execution witnesses and arithmetic obligations; it supplies no phase-success probability.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EmpiricalPhaseCertificate.lean#L15-L34

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.EmpiricalPhaseCertificate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

/-- INTERNAL: Raw empirical mean estimates and the exact stationary type
identity needed by the deterministic finishing step. The means need not be
estimates from independent samples. The ideal-multiplier drift is retained
explicitly rather than inferred from accurate empirical ratios.
TEXLINE: main.tex:1241-1270 -/
def ObservationEstimates {n : ℕ} (s : AnnealingSchedule)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (R : ℚ) (ideal nextIdeal : Multipliers n) : Prop :=
  ∃ pZero : ℚ, ∃ pDefect : DefectIndex n → ℚ,
    0 < s.observations ∧ 0 < pZero ∧ 0 < R ∧
    RelativeEstimate s.η pZero
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ∧
    RelativeEstimate s.η (pZero * R)
      (observed.numeratorSum / (s.observations : ℚ)) ∧
    ∀ index, 0 < weights index ∧ 0 < pDefect index ∧
      weights index * pZero / pDefect index = ideal index ∧
      (ideal index / 2 ≤ nextIdeal index ∧ nextIdeal index ≤ 2 * ideal index) ∧
      RelativeEstimate s.η (pDefect index)
        ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
          (s.observations : ℚ))



/-- INTERNAL: A phase-level certificate exposing the restart endpoint and
raw empirical means before finishing. Its mean identities and drift are
mathematical obligations; no phase-success probability is assumed here.
TEXLINE: main.tex:1207-1285 -/
def RawPhaseEstimates {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  let ideal := fun a index => C a /
    FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
  ∃ current : AnnealingCursor n, ∃ start : PairedSet n × ℕ,
    ∃ observed : ObservationCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
    (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = some start ∧
    (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val =
      some observed ∧
    ObservationEstimates s current.currentWeights observed
      (C (j + 1) / C j) (ideal j) (ideal (j + 1))



end CountingMatroid.Analysis.EmpiricalPhaseCertificate

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · raw empirical mean estimates imply the actual phase
  certificate through exact finishing, ratio arithmetic, and learned-table
  preservation. Concentration and finite-tape coupling remain in the parent.
-/

end


