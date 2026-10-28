-- Prove2me | Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
-- name    : CountingMatroid_Analysis_IdealExchangeChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:10:18.426592+00:00
-- url     : https://prove2.me/theorems/e5431f78-d679-4ae0-8174-b9a97e07f6a1
-- title:
--   The ideal exchange Metropolis chain and its stationary law
-- statement:
--   Let $E=[n]\times\{0,1\}$. For labels $a,b\in E$ and a paired state $S\subseteq E$, define $\tau_{a,b}(S)$ by applying the transposition of $a,b$ to every element of $S$. The included identities state
--   $$\tau_{a,b}(\tau_{a,b}(S))=S,\qquad
--   \tau_{a,b}(S)=T\iff\tau_{a,b}(T)=S.$$
--   For $n>0$, two independent uniform labels define the symmetric proposal
--   $$Q(S,T)=\frac1{(2n)^2}\sum_{a,b\in E}\mathbf1_{\{\tau_{a,b}(S)=T\}}.$$
--   Equal labels and equal occupancy contribute holding moves; the definition applies to all paired subsets.
--
--   Fix a natural rank parameter $r$, independence oracles $o_1,o_2$, a positive rational parameter $q$, and positive rational defect multipliers $w_d$. The operational weight $W(S)$ is nonnegative: it is $q^{d(S)}$ on transversals, $w_{i,k}q^{d(S)}$ on a defect with empty pair $i$ and full pair $k$, and zero on invalid states, where $d(S)=n-\operatorname{pairedRank}(S)$ uses truncated natural subtraction. Its normalized real law and the ideal chain are
--   $$\pi(S)=\frac{W(S)}{\sum_TW(T)},\qquad P=\operatorname{Metropolis}(\pi,Q).$$
--   For distinct states, $P(S,T)=Q(S,T)\min\{1,\pi(T)/\pi(S)\}$, with remaining mass on the diagonal and total real division at zero. The bundle proves stationarity of $\pi$ for $P$. It also supplies the general detailed-balance lemma: Metropolis with any finite probability law and symmetric Markov proposal is reversible, even when the law has zero weights.
--
--   Finally, for any classifier kind $k$, the type observable is $\mathbf1_{\{\operatorname{classifyState}(S)=k\}}$. For any rational cooling factor $\rho$, the numerator observable is
--   $$G_\rho(S)=\mathbf1_{\{S\text{ transversal}\}}\rho^{d(S)},$$
--   viewed as real-valued. These are ideal finite-state constructions; a finite-tape realization is not asserted here.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IdealExchangeChain.lean#L13-L19

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.IdealExchangeChain

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: Relabel a paired state by swapping two ground labels. On an
n-element state a uniformly drawn ordered pair of labels gives the paper's
lazy exchange proposal: equal occupancy holds, and unequal occupancy exchanges.
The separate operational coupling still has to identify its transition law.
TEXLINE: main.tex:746-751 -/
def exchangeState {n : ℕ} (a b : PairedGround n) (state : PairedSet n) : PairedSet n :=
  state.image (Equiv.swap a b)

/-- INTERNAL: A label exchange is an involution on the finite state space. -/
theorem exchange_state_involutive {n : ℕ} (a b : PairedGround n)
    (state : PairedSet n) : exchangeState a b (exchangeState a b state) = state := by
  unfold exchangeState
  rw [Finset.image_image]
  simp only [Function.comp_def, Equiv.swap_apply_self, Finset.image_id']

/-- INTERNAL: Each fixed exchange has a symmetric transition indicator. -/
theorem exchange_state_eq_iff {n : ℕ} (a b : PairedGround n)
    (state next : PairedSet n) : exchangeState a b state = next ↔
      exchangeState a b next = state := by
  constructor <;> intro h
  · rw [← h, exchange_state_involutive]
  · rw [← h, exchange_state_involutive]

/-- INTERNAL: Ideal proposal obtained from two independent uniform paired
labels, including equal labels and equal occupancy. It is defined on all
paired subsets; the Metropolis target rejects zero-weight invalid states.
TEXLINE: main.tex:746-751 -/
noncomputable def exchangeProposal (n : ℕ) (hn : 0 < n) : FinChain (PairedSet n) where
  P state next := ∑ a : PairedGround n, ∑ b : PairedGround n,
    if exchangeState a b state = next then
      1 / (Fintype.card (PairedGround n) : ℝ) ^ 2 else 0
  P_nonneg state next := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    split_ifs <;> positivity
  P_sum state := by
    rw [Finset.sum_comm]
    apply Eq.trans (Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (PairedGround n) : ℝ) ≠ 0 := by
      simp only [PairedGround, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      exact_mod_cast (by omega : n * 2 ≠ 0)
    field_simp

/-- INTERNAL: The concrete ideal exchange proposal is symmetric, since
swapping a fixed pair of labels is an involution. -/
theorem exchange_proposal_symmetric (n : ℕ) (hn : 0 < n)
    (state next : PairedSet n) :
    exchangeProposal n hn state next = exchangeProposal n hn next state := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [exchange_state_eq_iff]

/-- INTERNAL: Operational weights are nonnegative at a positive parameter
with positive multipliers, including zero on rejected classifier branches. -/
theorem state_weight_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (state : PairedSet n) : 0 ≤ stateWeight r o₁ o₂ q w state := by
  classical
  cases hk : (classifyState state).val with
  | invalid => simp [stateWeight, hk, weightOfKind]
  | transversal =>
    simp only [stateWeight, hk, weightOfKind, Arlib.Computation.Charged.val_bind,
      CountingMatroid.Model.Operations.natSub,
      Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure,
      CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, Option.getD_some]
    exact (pow_pos hq _).le
  | defect i k =>
    by_cases h : i ≠ k
    · simp only [stateWeight, hk, weightOfKind, dif_pos h,
        Arlib.Computation.Charged.val_bind, CountingMatroid.Model.Operations.natSub,
        CountingMatroid.Model.Operations.multiplierRead,
        CountingMatroid.Model.Operations.ratMul,
        Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany,
        Arlib.Computation.Charged.val_pure,
        CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, Option.getD_some]
      exact (mul_pos (hw ⟨i, k, h⟩) (pow_pos hq _)).le
    · simp [stateWeight, hk, weightOfKind, h]

/-- INTERNAL: Normalize the actual rational state weights as a finite real
probability distribution for the library's Markov-chain API. -/
noncomputable def operationalLaw {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    FinDist (PairedSet n) where
  p state := (stateWeight r o₁ o₂ q w state : ℝ) / (normalizer r o₁ o₂ q w : ℝ)
  p_nonneg state := by
    apply div_nonneg
    · exact_mod_cast state_weight_nonneg r o₁ o₂ q w hq hw state
    · exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1.le
  p_sum := by
    rw [← Finset.sum_div]
    have hsum : (∑ state : PairedSet n, (stateWeight r o₁ o₂ q w state : ℝ)) =
        (normalizer r o₁ o₂ q w : ℝ) := by
      unfold normalizer
      norm_cast
    rw [hsum]
    apply div_self
    exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1.ne'

/-- INTERNAL: Metropolis detailed balance also holds for targets with zero
weights. This permits extending the valid-state law by zero to all paired
subsets without imposing an artificial full-support assumption. -/
theorem metropolis_reversible_zero_weights {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : FinDist Ω) (Q : FinChain Ω) (hsymm : ∀ x y, Q x y = Q y x) :
    Reversible μ (metropolis μ Q) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  rw [metropolis_apply_of_ne μ Q hxy, metropolis_apply_of_ne μ Q (Ne.symm hxy)]
  by_cases hx : μ x = 0
  · simp [mhRate_apply, hx]
  by_cases hy : μ y = 0
  · simp [mhRate_apply, hy]
  have hxpos : 0 < μ x := lt_of_le_of_ne (μ.coe_nonneg x) (Ne.symm hx)
  have hypos : 0 < μ y := lt_of_le_of_ne (μ.coe_nonneg y) (Ne.symm hy)
  rw [mhRate_detailed_balance Q y hxpos, mhRate_detailed_balance Q x hypos,
    hsymm x y, min_comm]

/-- INTERNAL: The fixed ideal exchange Metropolis kernel at the operational
state weights. Invalid-state targets have zero mass and are rejected; the
separate finite-tape coupling concerns draws realizing its acceptance rates.
TEXLINE: main.tex:746-757,1207-1212 -/
noncomputable def idealChain {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) : FinChain (PairedSet n) :=
  metropolis (operationalLaw r o₁ o₂ q w hq hw) (exchangeProposal n hn)

/-- INTERNAL: The normalized operational law is stationary for its concrete
ideal exchange kernel, including zero mass on invalid states.
TEXLINE: main.tex:746-757 -/
theorem ideal_chain_stationary {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) :
    Stationary (operationalLaw r o₁ o₂ q w hq hw)
      (idealChain r o₁ o₂ q w hn hq hw) :=
  (metropolis_reversible_zero_weights _ _ (exchange_proposal_symmetric n hn)).stationary

/-- INTERNAL: The real-valued type indicator used by the ideal-chain
analysis is the same classifier observation counted by the program.
TEXLINE: main.tex:1181-1187,1238-1247 -/
noncomputable def typeIndicator {n : ℕ} (kind : StateKind n) (state : PairedSet n) : ℝ :=
  if (classifyState state).val = kind then 1 else 0



/-- INTERNAL: The real-valued annealing numerator observed by the program;
it vanishes on defects and retains the cooling factor on transversals.
TEXLINE: main.tex:1181-1187,1238-1247 -/
noncomputable def numeratorObservable {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (state : PairedSet n) : ℝ :=
  if (classifyState state).val = .transversal then
    (ρ : ℝ) ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
  else 0



end CountingMatroid.Analysis.IdealExchangeChain

end


