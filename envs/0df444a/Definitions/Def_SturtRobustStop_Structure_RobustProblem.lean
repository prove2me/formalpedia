-- Prove2me | Definitions.Def_SturtRobustStop_Structure_RobustProblem
-- name    : SturtRobustStop_Structure_RobustProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:10:55.421735+00:00
-- url     : https://prove2.me/theorems/fc91d8ea-dde4-4bb4-9337-2313e4d239b8
-- title:
--   Closed uncertainty boxes and the robust empirical objectives
-- statement:
--   For an instance $D$, let $U_t^i=\{z\in\mathbb R^d:|z_a-x_{ta}^i|\le\epsilon\text{ for all }a\}$ and $U^i=\prod_tU_t^i$. These closed boxes include their boundaries. Define
--   $$r_i(\mu)=\inf_{y\in U^i}g(\tau_\mu(y),x^i),\qquad J(\mu)=\frac1N\sum_i r_i(\mu).$$
--   Only the stopping input is perturbed; the reward path is the fixed original sample. The unrestricted value is the supremum of $J$ over all Borel measurable time-dependent exercise policies. Terminal feasibility means $\forall i\,\exists t\, U_t^i\subseteq S_t$, and the restricted value is the supremum over exactly those policies.
--
--   Values are encoded in ENNReal to use genuine complete-lattice extrema. The original sample lies in its uncertainty set, and a proved helper bounds each sample infimum by a finite sampled payoff. All objective values and their suprema are finite: every payoff is one of $0,g(1,x^i),\ldots,g(T,x^i)$, providing a uniform finite bound for this instance. N is positive. These are mathematical consequences, not instance assumptions.
-- source:
--   Bradley Sturt, arXiv:2103.03300v4, §2.2 (RO), printed/PDF p.7; Lemma 1 (RO_T), printed/PDF p.16. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_Model

open scoped ENNReal

namespace SturtRobustStop.Structure

/-- The closed infinity-norm box, including its boundary. -/
def box {T N d : ℕ} (D : Model T N d) (i : Fin N) (t : Fin T) : Set (State d) :=
  {z | ∀ a, |z a - D.sample i t a| ≤ D.epsilon}

/-- The full Cartesian product of the periodwise boxes. -/
def uncertainty {T N d : ℕ} (D : Model T N d) (i : Fin N) : Set (Path T d) :=
  {y | ∀ t, y t ∈ box D i t}

theorem center_mem_uncertainty {T N d : ℕ} (D : Model T N d) (i : Fin N) :
    D.sample i ∈ uncertainty D i := by
  intro t a
  simpa using D.epsilon_nonneg

/-- The adversary perturbs the stopping rule's input, never the reward's path.
Complete-lattice infima avoid conditional-real-infimum default values. -/
noncomputable def sampleReward {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (i : Fin N) : ℝ≥0∞ :=
  ⨅ y : {y // y ∈ uncertainty D i},
    (D.payoff (stoppingTime μ y.val) (D.sample i) : ℝ≥0∞)

/-- Each infimum is finite, since the sample itself belongs to its box. -/
theorem sampleReward_lt_top {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) (i : Fin N) : sampleReward D μ i < ⊤ := by
  apply lt_of_le_of_lt (iInf_le _ ⟨D.sample i, center_mem_uncertainty D i⟩)
  exact ENNReal.coe_lt_top

/-- Sample average, with the source's positive sample size. -/
noncomputable def objective {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) : ℝ≥0∞ :=
  (∑ i : Fin N, sampleReward D μ i) / (N : ℝ≥0∞)

/-- The additional constraint in (RO_T): ∀i ∃t ∀z∈Uᵢₜ, Stop. -/
def TerminalFeasible {T N d : ℕ} (D : Model T N d)
    (μ : Policy T (State d)) : Prop :=
  ∀ i, ∃ t, box D i t ⊆ μ.stop t

/-- Optimal value over every measurable Markovian policy. -/
noncomputable def optimalValue {T N d : ℕ} (D : Model T N d) : ℝ≥0∞ :=
  ⨆ μ : Policy T (State d), objective D μ

/-- Optimal value with precisely the additional (RO_T) constraint. -/
noncomputable def terminalValue {T N d : ℕ} (D : Model T N d) : ℝ≥0∞ :=
  ⨆ μ : {μ : Policy T (State d) // TerminalFeasible D μ}, objective D μ.val

end SturtRobustStop.Structure


