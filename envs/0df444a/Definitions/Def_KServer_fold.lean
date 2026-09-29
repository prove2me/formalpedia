-- Prove2me | Definitions.Def_KServer_fold
-- name    : KServer_fold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T14:25:44.402764+00:00
-- url     : https://prove2.me/theorems/318aaf5b-4625-4afe-9572-e405e2e15e98
-- title:
--   Nonexpansive retractions of the chain and the theta fold
-- statement:
--   Let $X$ be a metric space with marked points $s \neq t$, $C_3(X;s,t)$ the three-copy chain, and $\Theta$ the theta gluing of two such chains sharing both endpoints (the BCR level step). Each copy $i \in \{0,1,2\}$ of the chain admits a retraction $\rho_i : C_3 \to X$ fixing copy $i$ and collapsing the earlier copies to $s$ and the later copies to $t$; each $\rho_i$ is nonexpansive, $$d(\rho_i(p), \rho_i(q)) \le d(p, q),$$ by direct inspection of the six chain distance formulas. Moreover the theta gluing folds nonexpansively onto the chain by mapping both copies identically (the cross-side theta distance dominates the chain distance by the triangle inequality through either junction). Composing gives nonexpansive projections of the level step onto each of its six embedded copies, fixing the corresponding copy embeddings. These projections are the maps along which online evaders on the level step are shadowed to evaders on $X$ in the stage constructions of the BCR lower bound.
-- source:
--   BCR randomized k-server lower bound, stage construction layer

import Mathlib
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-! ### Nonexpansive retractions of the chain and the fold of the theta step

Each copy of the three-copy chain admits a nonexpansive retraction sending
the other copies to the appropriate junction, and the theta gluing folds
nonexpansively onto the chain (both copies mapped identically).  Composing
gives the nonexpansive projections of the BCR level step onto its embedded
copies used by the stage constructions. -/

namespace Chain3

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-- Retraction onto copy 0: later copies collapse to the far junction. -/
def ret0 : Chain3Point X s t → X
  | Sum.inl (Sum.inl x) => x
  | Sum.inl (Sum.inr _) => t
  | Sum.inr _ => t

/-- Retraction onto copy 1. -/
def ret1 : Chain3Point X s t → X
  | Sum.inl (Sum.inl _) => s
  | Sum.inl (Sum.inr x) => x.1
  | Sum.inr _ => t

/-- Retraction onto copy 2. -/
def ret2 : Chain3Point X s t → X
  | Sum.inl _ => s
  | Sum.inr x => x.1

theorem ret0_emb0 (x : X) : ret0 s t (emb0 s t x) = x := rfl
theorem ret1_emb1 (x : X) (hx : x ≠ s) : ret1 s t (emb1 s t x hx) = x := rfl
theorem ret2_emb2 (x : X) (hx : x ≠ s) : ret2 s t (emb2 s t x hx) = x := rfl

theorem ret0_lipschitz (p q : Chain3Point X s t) :
    letI := chain3Metric X s t hst
    dist (ret0 s t p) (ret0 s t q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  rcases p with (x | x) | x <;> rcases q with (y | y) | y
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inl (Sum.inl y))
        = dist x y := dist_emb0_emb0 s t hst x y
    show dist x y ≤ _
    rw [h]
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inl (Sum.inr y))
        = dist x t + dist s y.1 := dist_emb0_emb1 s t hst x y.1 y.2
    show dist x t ≤ _
    rw [h]
    have := dist_nonneg (x := s) (y := y.1)
    linarith
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inr y)
        = dist x t + dist s t + dist s y.1 := dist_emb0_emb2 s t hst x y.1 y.2
    show dist x t ≤ _
    rw [h]
    have h1 := dist_nonneg (x := s) (y := t)
    have h2 := dist_nonneg (x := s) (y := y.1)
    linarith
  · have h : dist (Sum.inl (Sum.inl y) : Chain3Point X s t) (Sum.inl (Sum.inr x))
        = dist y t + dist s x.1 := dist_emb0_emb1 s t hst y x.1 x.2
    show dist t y ≤ _
    rw [dist_comm (Sum.inl (Sum.inr x) : Chain3Point X s t) (Sum.inl (Sum.inl y)),
      h, dist_comm t y]
    have := dist_nonneg (x := s) (y := x.1)
    linarith
  · show dist t t ≤ _
    rw [dist_self]
    exact dist_nonneg
  · show dist t t ≤ _
    rw [dist_self]
    exact dist_nonneg
  · have h : dist (Sum.inl (Sum.inl y) : Chain3Point X s t) (Sum.inr x)
        = dist y t + dist s t + dist s x.1 := dist_emb0_emb2 s t hst y x.1 x.2
    show dist t y ≤ _
    rw [dist_comm (Sum.inr x : Chain3Point X s t) (Sum.inl (Sum.inl y)),
      h, dist_comm t y]
    have h1 := dist_nonneg (x := s) (y := t)
    have h2 := dist_nonneg (x := s) (y := x.1)
    linarith
  · show dist t t ≤ _
    rw [dist_self]
    exact dist_nonneg
  · show dist t t ≤ _
    rw [dist_self]
    exact dist_nonneg

theorem ret1_lipschitz (p q : Chain3Point X s t) :
    letI := chain3Metric X s t hst
    dist (ret1 s t p) (ret1 s t q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  rcases p with (x | x) | x <;> rcases q with (y | y) | y
  · show dist s s ≤ _
    rw [dist_self]
    exact dist_nonneg
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inl (Sum.inr y))
        = dist x t + dist s y.1 := dist_emb0_emb1 s t hst x y.1 y.2
    show dist s y.1 ≤ _
    rw [h]
    have := dist_nonneg (x := x) (y := t)
    linarith
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inr y)
        = dist x t + dist s t + dist s y.1 := dist_emb0_emb2 s t hst x y.1 y.2
    show dist s t ≤ _
    rw [h]
    have h1 := dist_nonneg (x := x) (y := t)
    have h2 := dist_nonneg (x := s) (y := y.1)
    linarith
  · have h : dist (Sum.inl (Sum.inl y) : Chain3Point X s t) (Sum.inl (Sum.inr x))
        = dist y t + dist s x.1 := dist_emb0_emb1 s t hst y x.1 x.2
    show dist x.1 s ≤ _
    rw [dist_comm (Sum.inl (Sum.inr x) : Chain3Point X s t) (Sum.inl (Sum.inl y)),
      h, dist_comm x.1 s]
    have := dist_nonneg (x := y) (y := t)
    linarith
  · have h : dist (Sum.inl (Sum.inr x) : Chain3Point X s t) (Sum.inl (Sum.inr y))
        = dist x.1 y.1 := dist_emb1_emb1 s t hst x.1 y.1 x.2 y.2
    show dist x.1 y.1 ≤ _
    rw [h]
  · have h : dist (Sum.inl (Sum.inr x) : Chain3Point X s t) (Sum.inr y)
        = dist x.1 t + dist s y.1 := dist_emb1_emb2 s t hst x.1 y.1 x.2 y.2
    show dist x.1 t ≤ _
    rw [h]
    have := dist_nonneg (x := s) (y := y.1)
    linarith
  · have h : dist (Sum.inl (Sum.inl y) : Chain3Point X s t) (Sum.inr x)
        = dist y t + dist s t + dist s x.1 := dist_emb0_emb2 s t hst y x.1 x.2
    show dist t s ≤ _
    rw [dist_comm (Sum.inr x : Chain3Point X s t) (Sum.inl (Sum.inl y)),
      h, dist_comm t s]
    have h1 := dist_nonneg (x := y) (y := t)
    have h2 := dist_nonneg (x := s) (y := x.1)
    linarith
  · have h : dist (Sum.inl (Sum.inr y) : Chain3Point X s t) (Sum.inr x)
        = dist y.1 t + dist s x.1 := dist_emb1_emb2 s t hst y.1 x.1 y.2 x.2
    show dist t y.1 ≤ _
    rw [dist_comm (Sum.inr x : Chain3Point X s t) (Sum.inl (Sum.inr y)),
      h, dist_comm t y.1]
    have := dist_nonneg (x := s) (y := x.1)
    linarith
  · show dist t t ≤ _
    rw [dist_self]
    exact dist_nonneg

theorem ret2_lipschitz (p q : Chain3Point X s t) :
    letI := chain3Metric X s t hst
    dist (ret2 s t p) (ret2 s t q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  rcases p with (x | x) | x <;> rcases q with (y | y) | y
  · show dist s s ≤ _
    rw [dist_self]
    exact dist_nonneg
  · show dist s s ≤ _
    rw [dist_self]
    exact dist_nonneg
  · have h : dist (Sum.inl (Sum.inl x) : Chain3Point X s t) (Sum.inr y)
        = dist x t + dist s t + dist s y.1 := dist_emb0_emb2 s t hst x y.1 y.2
    show dist s y.1 ≤ _
    rw [h]
    have h1 := dist_nonneg (x := x) (y := t)
    have h2 := dist_nonneg (x := s) (y := t)
    linarith
  · show dist s s ≤ _
    rw [dist_self]
    exact dist_nonneg
  · show dist s s ≤ _
    rw [dist_self]
    exact dist_nonneg
  · have h : dist (Sum.inl (Sum.inr x) : Chain3Point X s t) (Sum.inr y)
        = dist x.1 t + dist s y.1 := dist_emb1_emb2 s t hst x.1 y.1 x.2 y.2
    show dist s y.1 ≤ _
    rw [h]
    have := dist_nonneg (x := x.1) (y := t)
    linarith
  · have h : dist (Sum.inl (Sum.inl y) : Chain3Point X s t) (Sum.inr x)
        = dist y t + dist s t + dist s x.1 := dist_emb0_emb2 s t hst y x.1 x.2
    show dist x.1 s ≤ _
    rw [dist_comm (Sum.inr x : Chain3Point X s t) (Sum.inl (Sum.inl y)),
      h, dist_comm x.1 s]
    have h1 := dist_nonneg (x := y) (y := t)
    have h2 := dist_nonneg (x := s) (y := t)
    linarith
  · have h : dist (Sum.inl (Sum.inr y) : Chain3Point X s t) (Sum.inr x)
        = dist y.1 t + dist s x.1 := dist_emb1_emb2 s t hst y.1 x.1 y.2 x.2
    show dist x.1 s ≤ _
    rw [dist_comm (Sum.inr x : Chain3Point X s t) (Sum.inl (Sum.inr y)),
      h, dist_comm x.1 s]
    have := dist_nonneg (x := y.1) (y := t)
    linarith
  · have h : dist (Sum.inr x : Chain3Point X s t) (Sum.inr y)
        = dist x.1 y.1 := dist_emb2_emb2 s t hst x.1 y.1 x.2 y.2
    show dist x.1 y.1 ≤ _
    rw [h]

end Chain3

namespace ThetaChain

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-- The fold of the theta gluing onto the chain: both copies mapped
identically. -/
def fold : Step s t hst → Chain3Point X s t
  | Sum.inl p => p
  | Sum.inr p => p.1

theorem fold_lipschitz (p q : Step s t hst) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (fold s t hst p) (fold s t hst q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rcases p with p | p <;> rcases q with q | q
  · exact le_of_eq (step_dist_inl_inl s t hst p q).symm
  · have hred : dist (Sum.inl p : Step s t hst) (Sum.inr q)
        = min (dist p (Chain3.start s t) + dist (Chain3.start s t) q.1)
            (dist p (Chain3.stop s t hst) + dist (Chain3.stop s t hst) q.1) :=
      step_dist_inl_inr s t hst p q
    show dist p q.1 ≤ _
    rw [hred]
    refine le_min ?_ ?_
    · exact dist_triangle p (Chain3.start s t) q.1
    · exact dist_triangle p (Chain3.stop s t hst) q.1
  · have hred : dist (Sum.inl q : Step s t hst) (Sum.inr p)
        = min (dist q (Chain3.start s t) + dist (Chain3.start s t) p.1)
            (dist q (Chain3.stop s t hst) + dist (Chain3.stop s t hst) p.1) :=
      step_dist_inl_inr s t hst q p
    show dist p.1 q ≤ _
    rw [dist_comm (α := Step s t hst), hred, dist_comm p.1 q]
    refine le_min ?_ ?_
    · exact dist_triangle q (Chain3.start s t) p.1
    · exact dist_triangle q (Chain3.stop s t hst) p.1
  · exact le_of_eq (step_dist_inr_inr s t hst p q).symm

/-- The nonexpansive projections of the level step onto its six copies
(pairwise folded). -/
def stepRet0 (y : Step s t hst) : X := Chain3.ret0 s t (fold s t hst y)
def stepRet1 (y : Step s t hst) : X := Chain3.ret1 s t (fold s t hst y)
def stepRet2 (y : Step s t hst) : X := Chain3.ret2 s t (fold s t hst y)

theorem stepRet0_lipschitz (p q : Step s t hst) :
    letI := stepMetric s t hst
    dist (stepRet0 s t hst p) (stepRet0 s t hst q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  exact le_trans (Chain3.ret0_lipschitz s t hst _ _) (fold_lipschitz s t hst p q)

theorem stepRet1_lipschitz (p q : Step s t hst) :
    letI := stepMetric s t hst
    dist (stepRet1 s t hst p) (stepRet1 s t hst q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  exact le_trans (Chain3.ret1_lipschitz s t hst _ _) (fold_lipschitz s t hst p q)

theorem stepRet2_lipschitz (p q : Step s t hst) :
    letI := stepMetric s t hst
    dist (stepRet2 s t hst p) (stepRet2 s t hst q) ≤ dist p q := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  exact le_trans (Chain3.ret2_lipschitz s t hst _ _) (fold_lipschitz s t hst p q)

/-- Action on the copy embeddings. -/
theorem stepRet0_embL0 (x : X) : stepRet0 s t hst (embL0 s t hst x) = x := rfl
theorem stepRet0_embR0 (x : X) (hx : x ≠ s) :
    stepRet0 s t hst (embR0 s t hst x hx) = x := rfl
theorem stepRet1_embL1 (x : X) (hx : x ≠ s) :
    stepRet1 s t hst (embL1 s t hst x hx) = x := rfl
theorem stepRet1_embR1 (x : X) (hx : x ≠ s) :
    stepRet1 s t hst (embR1 s t hst x hx) = x := rfl
theorem stepRet2_embL2 (x : X) (hx : x ≠ s) :
    stepRet2 s t hst (embL2 s t hst x hx) = x := rfl
theorem stepRet2_embR2 (x : X) (hx : x ≠ s) (hx' : x ≠ t) :
    stepRet2 s t hst (embR2 s t hst x hx hx') = x := rfl

end ThetaChain

end KServer


