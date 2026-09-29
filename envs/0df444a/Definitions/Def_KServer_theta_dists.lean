-- Prove2me | Definitions.Def_KServer_theta_dists
-- name    : KServer_theta_dists
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T13:16:37.616261+00:00
-- url     : https://prove2.me/theorems/5c7fcef9-db5d-4b51-a91b-ad54ab44b203
-- title:
--   Distance catalog for the theta-chain step embeddings
-- statement:
--   For the theta gluing step Step s t (two 3-chain copies of a metric space X glued at both marked endpoints s and t), we define the six copy embeddings embL0/embL1/embL2 (left copy) and embR0/embR1/embR2 (right copy, with representatives excluding the shared endpoints), and prove a catalog of distance formulas: distances from each embedded copy to the start and stop junction points (chain_dist_emb0_start = d(x,s), chain_dist_emb1_start = D + d(s,x), chain_dist_emb2_start = 2D + d(s,x), and symmetrically to stop), same-side step distances agree with the chain distances, and cross-side distances equal the minimum of routing through the two junctions. Two stage-critical corollaries: the pair of first thirds is jointly 1-Lipschitz onto X (d(x,y) <= dist(embL0 x, embR0 y)), and the two middle thirds are at distance at least 2*d(s,t) from each other.
-- source:
--   BCR randomized k-server lower bound, theta-space geometry layer

import Mathlib
import Definitions.Def_KServer_glue2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ThetaChain

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-! ### The six copy embeddings of the theta step -/

/-- Left-side copies. -/
def embL0 (x : X) : Step s t hst := Sum.inl (Chain3.emb0 s t x)

def embL1 (x : X) (hx : x ≠ s) : Step s t hst := Sum.inl (Chain3.emb1 s t x hx)

def embL2 (x : X) (hx : x ≠ s) : Step s t hst := Sum.inl (Chain3.emb2 s t x hx)

/-- Right-side copies; representatives exclude the shared endpoints. -/
def embR0 (x : X) (hx : x ≠ s) : Step s t hst :=
  Sum.inr ⟨Chain3.emb0 s t x, by
    constructor
    · intro h
      simp [Chain3.emb0, Chain3.start] at h
      exact hx h
    · intro h
      simp [Chain3.emb0, Chain3.stop] at h⟩

def embR1 (x : X) (hx : x ≠ s) : Step s t hst :=
  Sum.inr ⟨Chain3.emb1 s t x hx, by
    constructor <;> intro h <;>
      simp [Chain3.emb1, Chain3.start, Chain3.stop] at h⟩

def embR2 (x : X) (hx : x ≠ s) (hx' : x ≠ t) : Step s t hst :=
  Sum.inr ⟨Chain3.emb2 s t x hx, by
    constructor
    · intro h
      simp [Chain3.emb2, Chain3.start] at h
    · intro h
      simp [Chain3.emb2, Chain3.stop] at h
      exact hx' h⟩

/-! ### Distances of chain points to the endpoints -/

section ChainEndpoints

variable {s t}

theorem chain_dist_emb0_start (x : X) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb0 s t x) (Chain3.start s t) = dist x s :=
  Chain3.dist_emb0_emb0 s t hst x s

theorem chain_dist_emb1_start (x : X) (hx : x ≠ s) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb1 s t x hx) (Chain3.start s t) = dist s t + dist s x := by
  letI := chain3Metric X s t hst
  rw [dist_comm]
  have h := Chain3.dist_emb0_emb1 s t hst s x hx
  rw [show Chain3.start s t = Chain3.emb0 s t s from rfl, h, dist_comm s t]

theorem chain_dist_emb2_start (x : X) (hx : x ≠ s) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb2 s t x hx) (Chain3.start s t)
      = 2 * dist s t + dist s x := by
  letI := chain3Metric X s t hst
  rw [dist_comm]
  have h := Chain3.dist_emb0_emb2 s t hst s x hx
  rw [show Chain3.start s t = Chain3.emb0 s t s from rfl, h, dist_comm s t]
  ring

theorem chain_dist_emb0_stop (x : X) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb0 s t x) (Chain3.stop s t hst)
      = dist x t + 2 * dist s t := by
  letI := chain3Metric X s t hst
  have h := Chain3.dist_emb0_emb2 s t hst x t hst.symm
  rw [show Chain3.stop s t hst = Chain3.emb2 s t t hst.symm from rfl, h,
    dist_comm s t]
  ring

theorem chain_dist_emb1_stop (x : X) (hx : x ≠ s) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb1 s t x hx) (Chain3.stop s t hst)
      = dist x t + dist s t := by
  letI := chain3Metric X s t hst
  have h := Chain3.dist_emb1_emb2 s t hst x t hx hst.symm
  rw [show Chain3.stop s t hst = Chain3.emb2 s t t hst.symm from rfl, h,
    dist_comm s t]

theorem chain_dist_emb2_stop (x : X) (hx : x ≠ s) :
    letI := chain3Metric X s t hst
    dist (Chain3.emb2 s t x hx) (Chain3.stop s t hst) = dist x t := by
  letI := chain3Metric X s t hst
  exact Chain3.dist_emb2_emb2 s t hst x t hx hst.symm

end ChainEndpoints

/-! ### Step-level distance reductions -/

theorem step_dist_inl_inl (p q : Chain3Point X s t) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (Sum.inl p : Step s t hst) (Sum.inl q) = dist p q := by
  letI := chain3Metric X s t hst
  show thetaDist (Chain3.start s t) (Chain3.stop s t hst) false p false q = _
  exact thetaDist_same _ _ false p q

theorem step_dist_inr_inr
    (p q : {u : Chain3Point X s t //
      u ≠ Chain3.start s t ∧ u ≠ Chain3.stop s t hst}) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (Sum.inr p : Step s t hst) (Sum.inr q) = dist p.1 q.1 := by
  letI := chain3Metric X s t hst
  show thetaDist (Chain3.start s t) (Chain3.stop s t hst) true p.1 true q.1 = _
  exact thetaDist_same _ _ true p.1 q.1

theorem step_dist_inl_inr (p : Chain3Point X s t)
    (q : {u : Chain3Point X s t //
      u ≠ Chain3.start s t ∧ u ≠ Chain3.stop s t hst}) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (Sum.inl p : Step s t hst) (Sum.inr q)
      = min (dist p (Chain3.start s t) + dist (Chain3.start s t) q.1)
          (dist p (Chain3.stop s t hst) + dist (Chain3.stop s t hst) q.1) := by
  letI := chain3Metric X s t hst
  show thetaDist (Chain3.start s t) (Chain3.stop s t hst) false p true q.1 = _
  exact thetaDist_cross _ _ p q.1 (by simp)

/-! ### Stage-critical corollaries -/

/-- Stage 1 shadow bound: the two first thirds are jointly `1`-Lipschitz
onto the level space. -/
theorem dist_le_embL0_embR0 (x y : X) (hy : y ≠ s) :
    letI := stepMetric s t hst
    dist x y ≤ dist (embL0 s t hst x) (embR0 s t hst y hy) := by
  letI := stepMetric s t hst
  letI := chain3Metric X s t hst
  have hred : dist (embL0 s t hst x) (embR0 s t hst y hy)
      = min (dist (Chain3.emb0 s t x) (Chain3.start s t)
          + dist (Chain3.start s t) (Chain3.emb0 s t y))
        (dist (Chain3.emb0 s t x) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) (Chain3.emb0 s t y)) :=
    step_dist_inl_inr s t hst _ _
  rw [hred, chain_dist_emb0_start hst x,
    dist_comm (Chain3.start s t) (Chain3.emb0 s t y),
    chain_dist_emb0_start hst y, chain_dist_emb0_stop hst x,
    dist_comm (Chain3.stop s t hst) (Chain3.emb0 s t y),
    chain_dist_emb0_stop hst y]
  refine le_min ?_ ?_
  · have h1 := dist_triangle x s y
    have h2 := dist_comm s y
    linarith
  · have h1 := dist_triangle x t y
    have h2 := dist_comm t y
    have h3 := dist_nonneg (x := s) (y := t)
    linarith

/-- Stage 2a crossing bound: the two middle thirds are `2 · dist s t` apart. -/
theorem two_D_le_embL1_embR1 (x y : X) (hx : x ≠ s) (hy : y ≠ s) :
    letI := stepMetric s t hst
    2 * dist s t ≤ dist (embL1 s t hst x hx) (embR1 s t hst y hy) := by
  letI := stepMetric s t hst
  letI := chain3Metric X s t hst
  have hred : dist (embL1 s t hst x hx) (embR1 s t hst y hy)
      = min (dist (Chain3.emb1 s t x hx) (Chain3.start s t)
          + dist (Chain3.start s t) (Chain3.emb1 s t y hy))
        (dist (Chain3.emb1 s t x hx) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) (Chain3.emb1 s t y hy)) :=
    step_dist_inl_inr s t hst _ _
  rw [hred, chain_dist_emb1_start hst x hx,
    dist_comm (Chain3.start s t) (Chain3.emb1 s t y hy),
    chain_dist_emb1_start hst y hy, chain_dist_emb1_stop hst x hx,
    dist_comm (Chain3.stop s t hst) (Chain3.emb1 s t y hy),
    chain_dist_emb1_stop hst y hy]
  refine le_min ?_ ?_
  · have h1 := dist_nonneg (x := s) (y := x)
    have h2 := dist_nonneg (x := s) (y := y)
    linarith
  · have h1 := dist_nonneg (x := x) (y := t)
    have h2 := dist_nonneg (x := y) (y := t)
    linarith

end ThetaChain

end KServer


