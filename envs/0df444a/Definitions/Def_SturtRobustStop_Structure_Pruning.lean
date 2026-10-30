-- Prove2me | Definitions.Def_SturtRobustStop_Structure_Pruning
-- name    : SturtRobustStop_Structure_Pruning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:11:45.743381+00:00
-- url     : https://prove2.me/theorems/9327d20f-faf9-4253-9005-8d9a8d6685a0
-- title:
--   Finite union policy family, guaranteed stopping minima, and pruning
-- statement:
--   Given one period $\sigma^i\in\{1,\ldots,T\}$ for each sample, the assigned policy has stopping region $S_t^\sigma=\bigcup_{i:\sigma^i=t}U_t^i$. Its regions are measurable finite unions of closed boxes. The family $M$ is the image of all such assignments; different assignments may yield identical policies.
--
--   For any policy, the guaranteed stopping index for sample i is the first t with $U_t^i\subseteq S_t$, or infinity if none exists. For a terminal-feasible policy, its canonical assignment consists of these finite minima. A policy $\mu'$ is a pruned version of $\mu$ precisely when $\mu$ is terminal feasible, $S'_t\subseteq S_t$ for every period, and every guaranteed stopping minimum is preserved. No equality of individual trajectory stopping times is required.
--
--   The reachable reward set for Lemma 2 contains $g(t,x^i)$ for periods $t\le\sigma^i(\mu)$ whose stopping region intersects $U_t^i$. Empty full-box minima retain the infinity value via Option.none; canonicalAssignment uses Finset.min' only with a proved nonemptiness witness.
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, equation (2), family M, and Definition 1 (pp.14,17), printed p. 17, PDF p. 17. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_RobustProblem

open scoped ENNReal

namespace SturtRobustStop.Structure

theorem box_measurable {T N d : ℕ} (D : Model T N d) (i : Fin N) (t : Fin T) :
    MeasurableSet (box D i t) := by
  simp only [box, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro a
  exact (isClosed_le ((continuous_apply a).sub continuous_const).abs continuous_const).measurableSet

/-- Equation (2): the finite union of boxes assigned to this period. -/
def assignedPolicy {T N d : ℕ} (D : Model T N d) (σ : Fin N → Fin T) :
    Policy T (State d) where
  stop t := ⋃ i : {i : Fin N // σ i = t}, box D i.val t
  measurable_stop t := MeasurableSet.iUnion fun i => box_measurable D i.val t

/-- The image of all assignment vectors; assignments need not be injective. -/
def family {T N d : ℕ} (D : Model T N d) : Set (Policy T (State d)) :=
  Set.range (assignedPolicy D)

/-- All periods at which an entire sample box is stopped. -/
noncomputable def guaranteedTimes {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (i : Fin N) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter fun t => box D i t ⊆ μ.stop t

/-- The full-box minimum, retaining ∞ for an empty set. -/
noncomputable def guaranteedStop {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (i : Fin N) : Option (Fin T) :=
  firstIndex fun t => box D i t ⊆ μ.stop t

theorem guaranteedTimes_nonempty {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (hμ : TerminalFeasible D μ) (i : Fin N) :
    (guaranteedTimes D μ i).Nonempty := by
  classical
  obtain ⟨t, ht⟩ := hμ i
  exact ⟨t, by simp [guaranteedTimes, ht]⟩

/-- The actual minimum σⁱ(μ), used only when (RO_T) is feasible. -/
noncomputable def canonicalAssignment {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (hμ : TerminalFeasible D μ) : Fin N → Fin T :=
  fun i => (guaranteedTimes D μ i).min' (guaranteedTimes_nonempty D μ hμ i)

/-- Definition 1: feasibility of the original policy, region inclusion, and
equality of earliest full-box stopping minima. -/
def IsPruned {T N d : ℕ} (D : Model T N d)
    (μ' μ : Policy T (State d)) : Prop :=
  TerminalFeasible D μ ∧
  (∀ t, μ'.stop t ⊆ μ.stop t) ∧
  (∀ i, guaranteedStop D μ' i = guaranteedStop D μ i)

/-- Rewards of the periods admitted by Lemma 2, not rewards on perturbed paths. -/
def reachableRewards {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (hμ : TerminalFeasible D μ) (i : Fin N) : Set ℝ≥0∞ :=
  {r | ∃ t : Fin T, t ≤ canonicalAssignment D μ hμ i ∧
    (∃ z ∈ box D i t, z ∈ μ.stop t) ∧ r = (D.reward t (D.sample i) : ℝ≥0∞)}

end SturtRobustStop.Structure


