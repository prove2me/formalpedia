-- Prove2me | Definitions.Def_FengLiYangMatching_General_Supplement_DynamicProgram
-- name    : FengLiYangMatching_General_Supplement_DynamicProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:21:00.739322+00:00
-- url     : https://prove2.me/theorems/935672ad-b095-400b-8842-a43b27e9c1ea
-- title:
--   Compatible labellings, recurrence and threshold policy
-- statement:
--   For a fixed graph $G$ with $m$ edges, let $H$ be the set of all labelled edges observed so far, and let $U\subseteq[n]$ be the unmatched labels. Count the compatible bijections by
--
--   $$C(H)=\#\{\pi:E(H)\subseteq E(\pi(G))\},\qquad p(e\mid H)=\frac{C(H+e)}{(m-|H|)C(H)}.$$
--
--   For $|H|=m$, set $V(H,U)=0$. Otherwise Equation (14) defines
--
--   $$V(H,U)=\sum_{e\notin H,\ C(H+e)>0}p(e\mid H)\begin{cases}\max\{V(H+e,U),1+V(H+e,U\setminus e)\},&e\subseteq U,\\ V(H+e,U),&e\not\subseteq U.\end{cases}$$
--
--   Here $U\setminus e$ removes both endpoints. The definition uses structural recursion with exactly $m-|H|$ remaining steps; each summand inserts one unseen edge. Unreachable states have zero value; probabilities are used on compatible states with positive denominator. The threshold policy reconstructs $H$ from all past arrivals and $U$ from actual accepted edges, and accepts a feasible current edge precisely when
--
--   $$1+V(H+e,U\setminus e)\ge V(H+e,U).$$
--
--   It accepts ties and ignores its private seed. These are concrete finite sums and computations; optimality and attainment are subsequent theorem obligations.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), §5.1, p. 17, Equations (13)–(14) and Lemma 5.1.

import Definitions.Def_FengLiYangMatching_General_Supplement_OnlineModel

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement
noncomputable section

/-- Section 5.1, C(H): count all compatible bijections. -/
def compatibleCount {n : ℕ} (G : SimpleGraph (Fin n)) (H : EdgeSet n) : ℕ := by
  classical
  exact (univ.filter fun labelling : Equiv.Perm (Fin n) => H ⊆ graphEdges (relabel G labelling)).card

/-- Equation (13). Used only when |H| < m and C(H)>0; extended by zero elsewhere. -/
def nextProbability {n : ℕ} (G : SimpleGraph (Fin n)) (H : EdgeSet n)
    (e : Edge n) : ℝ :=
  (compatibleCount G (insert e H) : ℝ) /
    (((graphEdges G).card - H.card : ℕ) * (compatibleCount G H : ℝ))

/-- Equation (14), by finite remaining horizon. Each summand adds one unseen edge.
At the full horizon this is exactly backward recursion on m-|H|, not an oracle. -/
def valueFuel {n : ℕ} (G : SimpleGraph (Fin n)) :
    ℕ → EdgeSet n → Finset (Fin n) → ℝ
  | 0, _, _ => 0
  | k+1, H, U => by
    classical
    exact if (graphEdges G).card ≤ H.card then 0 else
      ∑ e ∈ (univ.filter fun e : Edge n =>
        e ∉ H ∧ 0 < compatibleCount G (insert e H)),
        nextProbability G H e *
          (if ∀ v, v ∈ e → v ∈ U then
            max (valueFuel G k (insert e H) U)
              (1 + valueFuel G k (insert e H) (U \ covered {e}))
          else valueFuel G k (insert e H) U)

/-- The source's V(H,U), including its m=0 terminal case. Unreachable states
(C(H)=0 or |H|>m) have value zero and do not enter any compatible experiment. -/
def value {n : ℕ} (G : SimpleGraph (Fin n)) (H : EdgeSet n)
    (U : Finset (Fin n)) : ℝ :=
  valueFuel G ((graphEdges G).card - H.card) H U

/-- Accept ties as prescribed by Lemma 5.1. H contains all past arrivals,
whereas U removes endpoints of accepted edges only. The seed is ignored. -/
def thresholdPolicy {n : ℕ} (G : SimpleGraph (Fin n)) : OrderPolicy n := by
  classical
  exact fun past e _ =>
    let H := (past.map Prod.fst).toFinset
    let accepted := ((past.filter fun o => o.2).map Prod.fst).toFinset
    let U := univ \ covered accepted
    decide (¬ e.IsDiag ∧ (∀ v, v ∈ e → v ∈ U) ∧
      value G (insert e H) U ≤ 1 + value G (insert e H) (U \ covered {e}))

end
end FengLiYangMatching.General.Supplement


