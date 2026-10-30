-- Prove2me | Definitions.Def_OfflineStochMatchFull_InfinitePatience_Values
-- name    : OfflineStochMatchFull_InfinitePatience_Values
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:46:51.349283+00:00
-- url     : https://prove2.me/theorems/d428fd5f-0df2-4d5e-bd48-393f4dbd2b24
-- title:
--   LP and adaptive-policy optimization values
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph, $p_e\in[0,1]$, $w_e\ge0$, and $t_v\in\mathbb N\cup\{\infty\}$. Let $\mathcal Y$ be precisely the feasible set of LP (3): $0\le y_e\le1$, $\sum_{e\in\delta(v)}p_ey_e\le1$, and $\sum_{e\in\delta(v)}y_e\le t_v$ whenever $t_v$ is finite. Let $\Pi$ be all normalized admissible adaptive randomized probing policies and $R(\pi)$ their induced execution rewards. Define
--
--   $$
--   L(y)=\sum_{e\in E}w_ep_ey_e,\qquad
--   \mathrm{LP}=\sup_{y\in\mathcal Y}L(y),\qquad
--   \mathrm{OPT}=\sup_{\pi\in\Pi}R(\pi).
--   $$
--
--   An LP maximizer is a feasible vector attaining $\mathrm{LP}$. The well-posedness predicate records that both value sets are nonempty and bounded above, both suprema are attained, and every feasible LP objective and policy reward lies between zero and $\sum_e w_e$.
--
--   These are obligations in theorem conclusions, not input assumptions or fields that prescribe the answer. The policy benchmark is computed from actual legal runs independently of the LP. Zero is feasible and the stop policy is always available, including on empty graphs.
--
--   **Formalization Note** Real suprema are used; the theorems assert their nonemptiness, boundedness and attainment on the source domain. No default optimizer is chosen.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §2, p. 7, LP (3), Lemma 1 and the optimal-LP prescription.

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Policies

namespace OfflineStochMatchFull.InfinitePatience

open OfflineStochMatch.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- LP (3)'s objective after substituting `z e = p e * y e`, p. 7. -/
noncomputable def lpObjective (p w y : E → ℝ) : ℝ := ∑ e, w e * p e * y e

/-- Objective values over exactly the source's LP-feasible vectors. -/
def lpRewards (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w : E → ℝ) : Set ℝ :=
  {r | ∃ y, LPFeasible G p t y ∧ r = lpObjective p w y}

/-- The LP value; nonemptiness, boundedness and attainment are conclusions of
Lemma 1 and the full goal, never hypotheses supplied by an optimizer structure. -/
noncomputable def lpValue (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w : E → ℝ) : ℝ := sSup (lpRewards G p t w)

/-- A maximizer of the genuine LP value, with no default feasible-vector choice. -/
def IsLPMaximizer (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w y : E → ℝ) : Prop :=
  LPFeasible G p t y ∧ lpObjective p w y = lpValue G p t w

/-- Actual attainable expected rewards of all legal randomized adaptive policies. -/
def policyRewards (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w : E → ℝ) : Set ℝ :=
  Set.range (policyReward G p t w)

/-- The policy optimum is computed from admissible execution rewards, not the LP. -/
noncomputable def OPT (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w : E → ℝ) : ℝ := sSup (policyRewards G p t w)

/-- Well-posedness obligations, asserted in theorem conclusions. Stop witnesses
nonemptiness of policy rewards and zero witnesses LP feasibility. Bounds by total
nonnegative edge weight exclude junk real suprema, also for empty graphs. -/
def OptimaAttained (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (t : V → ℕ∞) (w : E → ℝ) : Prop :=
  (lpRewards G p t w).Nonempty ∧ BddAbove (lpRewards G p t w) ∧
  (policyRewards G p t w).Nonempty ∧ BddAbove (policyRewards G p t w) ∧
  (∃ y, IsLPMaximizer G p t w y) ∧
  (∃ π : ProbingPolicy G t, policyReward G p t w π = OPT G p t w) ∧
  (∀ π : ProbingPolicy G t, 0 ≤ policyReward G p t w π ∧
    policyReward G p t w π ≤ ∑ e, w e) ∧
  (∀ y, LPFeasible G p t y → 0 ≤ lpObjective p w y ∧ lpObjective p w y ≤ ∑ e, w e)

end OfflineStochMatchFull.InfinitePatience


