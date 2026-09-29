-- Prove2me | Definitions.Def_KServer_race_geo
-- name    : KServer_race_geo
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T19:23:52.005866+00:00
-- url     : https://prove2.me/theorems/cfb262ca-efb9-459b-b102-6b8f9cb702e9
-- title:
--   Geometry of the race on the level step
-- statement:
--   The geometric instantiation of the race on the BCR level step (the theta gluing of two three-copy chains of the level space $X$ with marked points $s, t$ at distance $D$). The six copy embeddings are totalized by sending excluded endpoints to canonical junction representatives, giving stage request maps: the head map (union of both first-third copies), the two coin maps (the two middle thirds), and the two closing maps (the last thirds). Proved here: the junction identities linking consecutive stage maps along each side and their common start; the closing maps send $\{t\}$ exactly to the stop point; the copy retractions invert the total embeddings, so each stage map is compatible with its nonexpansive projection; all six total embeddings are nonexpansive; the two coin copies are $2D$-separated,
--   $$\forall\, y \in G_L(S_L),\; z \in G_R(S_R): \quad 2D \le d(y, z),$$
--   yielding the dichotomy that every head-target or coin-copy point is $2D$-far from all images of one of the two coin maps; and the start-to-stop distance is the full path length $3D$. Finally, tautness — every point of $X$ lying on an $s$–$t$ geodesic, $d(s,x)+d(x,t)=d(s,t)$ — bounds the diameter of $X$ by $D$ and is preserved by the level step, which supplies the diameter arithmetic $J + p_e \le \mathrm{sep}$ for the coin-phase accounting at every level.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ThetaChain

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-! ### Total copy embeddings

The six copy embeddings, totalized: the excluded endpoints are sent to
their canonical junction representatives. -/

open Classical in
noncomputable def gL0 (x : X) : Step s t hst := embL0 s t hst x

open Classical in
noncomputable def gL1 (x : X) : Step s t hst :=
  if h : x = s then embL0 s t hst t else embL1 s t hst x h

open Classical in
noncomputable def gL2 (x : X) : Step s t hst :=
  if h : x = s then embL1 s t hst t hst.symm else embL2 s t hst x h

open Classical in
noncomputable def gR0 (x : X) : Step s t hst :=
  if h : x = s then embL0 s t hst s else embR0 s t hst x h

open Classical in
noncomputable def gR1 (x : X) : Step s t hst :=
  if h : x = s then embR0 s t hst t hst.symm else embR1 s t hst x h

open Classical in
noncomputable def gR2 (x : X) : Step s t hst :=
  if h : x = s then embR1 s t hst t hst.symm
  else if h' : x = t then stepT s t hst else embR2 s t hst x h h'

/-! ### The stage request maps -/

noncomputable def GA' (S : Set X) : Set (Step s t hst) :=
  gL0 s t hst '' S ∪ gR0 s t hst '' S

noncomputable def GL' (S : Set X) : Set (Step s t hst) := gL1 s t hst '' S

noncomputable def GR' (S : Set X) : Set (Step s t hst) := gR1 s t hst '' S

noncomputable def GTL' (S : Set X) : Set (Step s t hst) := gL2 s t hst '' S

noncomputable def GTR' (S : Set X) : Set (Step s t hst) := gR2 s t hst '' S

/-! ### Junctions -/

theorem gJ0 : gL0 s t hst s = gR0 s t hst s := by
  rw [gR0, dif_pos rfl]
  rfl

theorem gJ1L : gL0 s t hst t = gL1 s t hst s := by
  rw [gL1, dif_pos rfl]
  rfl

theorem gJ1R : gR0 s t hst t = gR1 s t hst s := by
  rw [gR0, dif_neg hst.symm, gR1, dif_pos rfl]

theorem gJ2L : gL1 s t hst t = gL2 s t hst s := by
  rw [gL1, dif_neg hst.symm, gL2, dif_pos rfl]

theorem gJ2R : gR1 s t hst t = gR2 s t hst s := by
  rw [gR1, dif_neg hst.symm, gR2, dif_pos rfl]

theorem gJ3L : gL2 s t hst t = stepT s t hst := by
  rw [gL2, dif_neg hst.symm]
  rfl

theorem gJ3R : gR2 s t hst t = stepT s t hst := by
  rw [gR2, dif_neg hst.symm, dif_pos rfl]

theorem gL0_s : gL0 s t hst s = stepS s t hst := rfl

/-- The closing maps send the target to the stop point exactly. -/
theorem GTL'_t : GTL' s t hst ({t} : Set X) = {stepT s t hst} := by
  unfold GTL'
  rw [Set.image_singleton, gJ3L]

theorem GTR'_t : GTR' s t hst ({t} : Set X) = {stepT s t hst} := by
  unfold GTR'
  rw [Set.image_singleton, gJ3R]

/-! ### Retraction compatibility -/

theorem ret_gL0 (x : X) : stepRet0 s t hst (gL0 s t hst x) = x := rfl

theorem ret_gR0 (x : X) : stepRet0 s t hst (gR0 s t hst x) = x := by
  by_cases h : x = s
  · rw [gR0, dif_pos h, h]
    rfl
  · rw [gR0, dif_neg h]
    rfl

theorem ret_gL1 (x : X) : stepRet1 s t hst (gL1 s t hst x) = x := by
  by_cases h : x = s
  · rw [gL1, dif_pos h, h]
    rfl
  · rw [gL1, dif_neg h]
    rfl

theorem ret_gR1 (x : X) : stepRet1 s t hst (gR1 s t hst x) = x := by
  by_cases h : x = s
  · rw [gR1, dif_pos h, h]
    rfl
  · rw [gR1, dif_neg h]
    rfl

theorem ret_gL2 (x : X) : stepRet2 s t hst (gL2 s t hst x) = x := by
  by_cases h : x = s
  · rw [gL2, dif_pos h, h]
    rfl
  · rw [gL2, dif_neg h]
    rfl

theorem ret_gR2 (x : X) : stepRet2 s t hst (gR2 s t hst x) = x := by
  by_cases h : x = s
  · rw [gR2, dif_pos h, h]
    rfl
  · by_cases h' : x = t
    · rw [gR2, dif_neg h, dif_pos h', h']
      rfl
    · rw [gR2, dif_neg h, dif_neg h']
      rfl

theorem hGA_ret : ∀ S : Set X, ∀ y ∈ GA' s t hst S,
    stepRet0 s t hst y ∈ S := by
  intro S y hy
  rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · rw [ret_gL0]
    exact hx
  · rw [ret_gR0]
    exact hx

theorem hGL_ret : ∀ S : Set X, ∀ y ∈ GL' s t hst S,
    stepRet1 s t hst y ∈ S := by
  rintro S y ⟨x, hx, rfl⟩
  rw [ret_gL1]
  exact hx

theorem hGR_ret : ∀ S : Set X, ∀ y ∈ GR' s t hst S,
    stepRet1 s t hst y ∈ S := by
  rintro S y ⟨x, hx, rfl⟩
  rw [ret_gR1]
  exact hx

theorem hGTL_ret : ∀ S : Set X, ∀ y ∈ GTL' s t hst S,
    stepRet2 s t hst y ∈ S := by
  rintro S y ⟨x, hx, rfl⟩
  rw [ret_gL2]
  exact hx

theorem hGTR_ret : ∀ S : Set X, ∀ y ∈ GTR' s t hst S,
    stepRet2 s t hst y ∈ S := by
  rintro S y ⟨x, hx, rfl⟩
  rw [ret_gR2]
  exact hx

/-! ### Nonemptiness and lift inclusions -/

theorem hGA_ne (S : Set X) (hS : S.Nonempty) :
    (GA' s t hst S).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨gL0 s t hst x, Or.inl ⟨x, hx, rfl⟩⟩

theorem hGL_ne (S : Set X) (hS : S.Nonempty) :
    (GL' s t hst S).Nonempty := hS.image _

theorem hGR_ne (S : Set X) (hS : S.Nonempty) :
    (GR' s t hst S).Nonempty := hS.image _

theorem hGTL_ne (S : Set X) (hS : S.Nonempty) :
    (GTL' s t hst S).Nonempty := hS.image _

theorem hGTR_ne (S : Set X) (hS : S.Nonempty) :
    (GTR' s t hst S).Nonempty := hS.image _

theorem hGAL_sub (S : Set X) : gL0 s t hst '' S ⊆ GA' s t hst S :=
  Set.subset_union_left

theorem hGAR_sub (S : Set X) : gR0 s t hst '' S ⊆ GA' s t hst S :=
  Set.subset_union_right

/-! ### Nonexpansiveness of the total embeddings -/

theorem gL0_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gL0 s t hst x) (gL0 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  show dist (Sum.inl (Chain3.emb0 s t x) : Step s t hst)
    (Sum.inl (Chain3.emb0 s t y)) ≤ dist x y
  rw [step_dist_inl_inl]
  exact le_of_eq (Chain3.dist_emb0_emb0 s t hst x y)

theorem gL1_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gL1 s t hst x) (gL1 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  by_cases hx : x = s <;> by_cases hy : y = s
  · rw [hx, hy, dist_self]
    exact dist_nonneg
  · rw [gL1, dif_pos hx, gL1, dif_neg hy, hx]
    show dist (Sum.inl (Chain3.emb0 s t t) : Step s t hst)
      (Sum.inl (Chain3.emb1 s t y hy)) ≤ dist s y
    rw [step_dist_inl_inl, Chain3.dist_emb0_emb1 s t hst t y hy,
      dist_self]
    linarith
  · rw [gL1, dif_neg hx, gL1, dif_pos hy, hy]
    show dist (Sum.inl (Chain3.emb1 s t x hx) : Step s t hst)
      (Sum.inl (Chain3.emb0 s t t)) ≤ dist x s
    rw [step_dist_inl_inl,
      dist_comm (Chain3.emb1 s t x hx) (Chain3.emb0 s t t),
      Chain3.dist_emb0_emb1 s t hst t x hx, dist_self, dist_comm x s]
    linarith
  · rw [gL1, dif_neg hx, gL1, dif_neg hy]
    show dist (Sum.inl (Chain3.emb1 s t x hx) : Step s t hst)
      (Sum.inl (Chain3.emb1 s t y hy)) ≤ dist x y
    rw [step_dist_inl_inl]
    exact le_of_eq (Chain3.dist_emb1_emb1 s t hst x y hx hy)

theorem gL2_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gL2 s t hst x) (gL2 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  by_cases hx : x = s <;> by_cases hy : y = s
  · rw [hx, hy, dist_self]
    exact dist_nonneg
  · rw [gL2, dif_pos hx, gL2, dif_neg hy, hx]
    show dist (Sum.inl (Chain3.emb1 s t t hst.symm) : Step s t hst)
      (Sum.inl (Chain3.emb2 s t y hy)) ≤ dist s y
    rw [step_dist_inl_inl,
      Chain3.dist_emb1_emb2 s t hst t y hst.symm hy, dist_self]
    linarith
  · rw [gL2, dif_neg hx, gL2, dif_pos hy, hy]
    show dist (Sum.inl (Chain3.emb2 s t x hx) : Step s t hst)
      (Sum.inl (Chain3.emb1 s t t hst.symm)) ≤ dist x s
    rw [step_dist_inl_inl,
      dist_comm (Chain3.emb2 s t x hx) (Chain3.emb1 s t t hst.symm),
      Chain3.dist_emb1_emb2 s t hst t x hst.symm hx, dist_self,
      dist_comm x s]
    linarith
  · rw [gL2, dif_neg hx, gL2, dif_neg hy]
    show dist (Sum.inl (Chain3.emb2 s t x hx) : Step s t hst)
      (Sum.inl (Chain3.emb2 s t y hy)) ≤ dist x y
    rw [step_dist_inl_inl]
    exact le_of_eq (Chain3.dist_emb2_emb2 s t hst x y hx hy)

theorem gR0_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gR0 s t hst x) (gR0 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  by_cases hx : x = s <;> by_cases hy : y = s
  · rw [hx, hy, dist_self]
    exact dist_nonneg
  · rw [gR0, dif_pos hx, gR0, dif_neg hy, hx]
    refine le_trans (le_of_eq (step_dist_inl_inr s t hst
      (Chain3.emb0 s t s) _)) ?_
    refine le_trans (min_le_left _ _) ?_
    dsimp only
    rw [chain_dist_emb0_start hst s, dist_self,
      dist_comm (Chain3.start s t) (Chain3.emb0 s t y),
      chain_dist_emb0_start hst y, dist_comm y s]
    linarith
  · rw [gR0, dif_neg hx, gR0, dif_pos hy, hy]
    rw [dist_comm]
    refine le_trans (le_of_eq (step_dist_inl_inr s t hst
      (Chain3.emb0 s t s) _)) ?_
    refine le_trans (min_le_left _ _) ?_
    dsimp only
    rw [chain_dist_emb0_start hst s, dist_self,
      dist_comm (Chain3.start s t) (Chain3.emb0 s t x),
      chain_dist_emb0_start hst x]
    linarith
  · rw [gR0, dif_neg hx, gR0, dif_neg hy]
    refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
    exact le_of_eq (Chain3.dist_emb0_emb0 s t hst x y)

theorem gR1_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gR1 s t hst x) (gR1 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  by_cases hx : x = s <;> by_cases hy : y = s
  · rw [hx, hy, dist_self]
    exact dist_nonneg
  · rw [gR1, dif_pos hx, gR1, dif_neg hy, hx]
    refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
    rw [Chain3.dist_emb0_emb1 s t hst t y hy, dist_self]
    linarith
  · rw [gR1, dif_neg hx, gR1, dif_pos hy, hy]
    refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
    rw [dist_comm (Chain3.emb1 s t x hx) (Chain3.emb0 s t t),
      Chain3.dist_emb0_emb1 s t hst t x hx, dist_self, dist_comm x s]
    linarith
  · rw [gR1, dif_neg hx, gR1, dif_neg hy]
    refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
    exact le_of_eq (Chain3.dist_emb1_emb1 s t hst x y hx hy)

theorem gR2_nonexp (x y : X) :
    letI := stepMetric s t hst
    dist (gR2 s t hst x) (gR2 s t hst y) ≤ dist x y := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  by_cases hx : x = s
  · by_cases hy : y = s
    · rw [hx, hy, dist_self]
      exact dist_nonneg
    · by_cases hy' : y = t
      · rw [gR2, dif_pos hx, gR2, dif_neg hy, dif_pos hy', hx, hy']
        rw [dist_comm]
        refine le_trans (le_of_eq (step_dist_inl_inr s t hst
          (Chain3.stop s t hst) _)) ?_
        refine le_trans (min_le_right _ _) ?_
        rw [dist_self, dist_comm (Chain3.stop s t hst)
          (Chain3.emb1 s t t hst.symm),
          chain_dist_emb1_stop hst t hst.symm, dist_self]
        linarith
      · rw [gR2, dif_pos hx, gR2, dif_neg hy, dif_neg hy', hx]
        refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
        rw [Chain3.dist_emb1_emb2 s t hst t y hst.symm hy, dist_self]
        linarith
  · by_cases hx' : x = t
    · by_cases hy : y = s
      · rw [gR2, dif_neg hx, dif_pos hx', gR2, dif_pos hy, hx', hy]
        refine le_trans (le_of_eq (step_dist_inl_inr s t hst
          (Chain3.stop s t hst) _)) ?_
        refine le_trans (min_le_right _ _) ?_
        rw [dist_self, dist_comm (Chain3.stop s t hst)
          (Chain3.emb1 s t t hst.symm),
          chain_dist_emb1_stop hst t hst.symm, dist_self]
        linarith [dist_comm t s]
      · by_cases hy' : y = t
        · rw [hx', hy', dist_self]
          exact dist_nonneg
        · rw [gR2, dif_neg hx, dif_pos hx', gR2, dif_neg hy, dif_neg hy',
            hx']
          refine le_trans (le_of_eq (step_dist_inl_inr s t hst
            (Chain3.stop s t hst) _)) ?_
          refine le_trans (min_le_right _ _) ?_
          rw [dist_self, dist_comm (Chain3.stop s t hst)
            (Chain3.emb2 s t y hy),
            chain_dist_emb2_stop hst y hy, dist_comm t y]
          linarith
    · by_cases hy : y = s
      · rw [gR2, dif_neg hx, dif_neg hx', gR2, dif_pos hy, hy]
        refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
        rw [dist_comm (Chain3.emb2 s t x hx) (Chain3.emb1 s t t hst.symm),
          Chain3.dist_emb1_emb2 s t hst t x hst.symm hx, dist_self,
          dist_comm x s]
        linarith
      · by_cases hy' : y = t
        · rw [gR2, dif_neg hx, dif_neg hx', gR2, dif_neg hy, dif_pos hy',
            hy']
          rw [dist_comm]
          refine le_trans (le_of_eq (step_dist_inl_inr s t hst
            (Chain3.stop s t hst) _)) ?_
          refine le_trans (min_le_right _ _) ?_
          rw [dist_self, dist_comm (Chain3.stop s t hst)
            (Chain3.emb2 s t x hx),
            chain_dist_emb2_stop hst x hx, dist_comm x t, dist_comm t x]
          linarith
        · rw [gR2, dif_neg hx, dif_neg hx', gR2, dif_neg hy, dif_neg hy']
          refine le_trans (le_of_eq (step_dist_inr_inr s t hst _ _)) ?_
          exact le_of_eq (Chain3.dist_emb2_emb2 s t hst x y hx hy)

/-! ### Cross-side separation -/

theorem two_D_le_embL0t_embR1 (y : X) (hy : y ≠ s) :
    letI := stepMetric s t hst
    2 * dist s t ≤ dist (embL0 s t hst t) (embR1 s t hst y hy) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [show dist (embL0 s t hst t) (embR1 s t hst y hy)
      = min (dist (Chain3.emb0 s t t) (Chain3.start s t)
          + dist (Chain3.start s t) (Chain3.emb1 s t y hy))
        (dist (Chain3.emb0 s t t) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) (Chain3.emb1 s t y hy))
    from step_dist_inl_inr s t hst _ _,
    chain_dist_emb0_start hst t,
    dist_comm (Chain3.start s t) (Chain3.emb1 s t y hy),
    chain_dist_emb1_start hst y hy, chain_dist_emb0_stop hst t,
    dist_comm (Chain3.stop s t hst) (Chain3.emb1 s t y hy),
    chain_dist_emb1_stop hst y hy, dist_comm t s, dist_self]
  refine le_min ?_ ?_
  · linarith [dist_nonneg (x := s) (y := y)]
  · linarith [dist_nonneg (x := y) (y := t), dist_nonneg (x := s) (y := t)]

theorem two_D_le_embL1_embR0t (x : X) (hx : x ≠ s) :
    letI := stepMetric s t hst
    2 * dist s t ≤ dist (embL1 s t hst x hx) (embR0 s t hst t hst.symm) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [show dist (embL1 s t hst x hx) (embR0 s t hst t hst.symm)
      = min (dist (Chain3.emb1 s t x hx) (Chain3.start s t)
          + dist (Chain3.start s t) (Chain3.emb0 s t t))
        (dist (Chain3.emb1 s t x hx) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) (Chain3.emb0 s t t))
    from step_dist_inl_inr s t hst _ _,
    chain_dist_emb1_start hst x hx,
    dist_comm (Chain3.start s t) (Chain3.emb0 s t t),
    chain_dist_emb0_start hst t, chain_dist_emb1_stop hst x hx,
    dist_comm (Chain3.stop s t hst) (Chain3.emb0 s t t),
    chain_dist_emb0_stop hst t, dist_comm t s, dist_self]
  refine le_min ?_ ?_
  · linarith [dist_nonneg (x := s) (y := x)]
  · linarith [dist_nonneg (x := x) (y := t), dist_nonneg (x := s) (y := t)]

theorem two_D_le_embL0t_embR0t :
    letI := stepMetric s t hst
    2 * dist s t ≤ dist (embL0 s t hst t) (embR0 s t hst t hst.symm) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [show dist (embL0 s t hst t) (embR0 s t hst t hst.symm)
      = min (dist (Chain3.emb0 s t t) (Chain3.start s t)
          + dist (Chain3.start s t) (Chain3.emb0 s t t))
        (dist (Chain3.emb0 s t t) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) (Chain3.emb0 s t t))
    from step_dist_inl_inr s t hst _ _,
    chain_dist_emb0_start hst t,
    dist_comm (Chain3.start s t) (Chain3.emb0 s t t),
    chain_dist_emb0_start hst t, chain_dist_emb0_stop hst t,
    dist_comm (Chain3.stop s t hst) (Chain3.emb0 s t t),
    chain_dist_emb0_stop hst t, dist_comm t s, dist_self]
  refine le_min ?_ ?_
  · linarith
  · linarith [dist_nonneg (x := s) (y := t)]

/-- Separation of the two coin copies, on the total maps. -/
theorem sep_GL_GR (xl xr : X) :
    letI := stepMetric s t hst
    2 * dist s t ≤ dist (gL1 s t hst xl) (gR1 s t hst xr) := by
  letI := stepMetric s t hst
  by_cases hxl : xl = s <;> by_cases hxr : xr = s
  · rw [gL1, dif_pos hxl, gR1, dif_pos hxr]
    exact two_D_le_embL0t_embR0t s t hst
  · rw [gL1, dif_pos hxl, gR1, dif_neg hxr]
    exact two_D_le_embL0t_embR1 s t hst xr hxr
  · rw [gL1, dif_neg hxl, gR1, dif_pos hxr]
    exact two_D_le_embL1_embR0t s t hst xl hxl
  · rw [gL1, dif_neg hxl, gR1, dif_neg hxr]
    exact two_D_le_embL1_embR1 s t hst xl xr hxl hxr

theorem hsepLR_geo : ∀ SL SR : Set X,
    ∀ y ∈ GL' s t hst SL, ∀ z ∈ GR' s t hst SR,
    letI := stepMetric s t hst
    2 * dist s t ≤ dist y z := by
  rintro SL SR y ⟨xl, _, rfl⟩ z ⟨xr, _, rfl⟩
  exact sep_GL_GR s t hst xl xr

/-- The dichotomy: every point of a head target request or a coin-copy
image is far from all images of one of the two coin copies. -/
theorem hdicho_geo : ∀ z : Step s t hst,
    (z ∈ GA' s t hst ({t} : Set X) ∨ (∃ S, z ∈ GL' s t hst S)
      ∨ (∃ S, z ∈ GR' s t hst S)) →
    (∀ S' : Set X, ∀ p ∈ GR' s t hst S',
      letI := stepMetric s t hst
      2 * dist s t ≤ dist z p)
    ∨ (∀ S' : Set X, ∀ p ∈ GL' s t hst S',
      letI := stepMetric s t hst
      2 * dist s t ≤ dist z p) := by
  letI := stepMetric s t hst
  intro z hz
  rcases hz with hz | ⟨S, hz⟩ | ⟨S, hz⟩
  · rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · left
      rintro S' p ⟨xr, _, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h1 : gL0 s t hst t = gL1 s t hst s := gJ1L s t hst
      rw [h1]
      exact sep_GL_GR s t hst s xr
    · right
      rintro S' p ⟨xl, _, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h1 : gR0 s t hst t = gR1 s t hst s := gJ1R s t hst
      rw [h1, dist_comm (gR1 s t hst s) (gL1 s t hst xl)]
      exact sep_GL_GR s t hst xl s
  · left
    rintro S' p ⟨xr, _, rfl⟩
    obtain ⟨xl, _, rfl⟩ := hz
    exact sep_GL_GR s t hst xl xr
  · right
    rintro S' p ⟨xl, _, rfl⟩
    obtain ⟨xr, _, rfl⟩ := hz
    rw [dist_comm (gR1 s t hst xr) (gL1 s t hst xl)]
    exact sep_GL_GR s t hst xl xr

/-- The lifted start-to-stop distance is the full path length. -/
theorem hd3_geo :
    letI := stepMetric s t hst
    3 * dist s t ≤ dist (gL0 s t hst s) (stepT s t hst) := by
  letI := stepMetric s t hst
  exact le_of_eq (dist_stepS_stepT s t hst).symm

/-! ### Tautness: every point on an `s`–`t` geodesic

Tautness gives the diameter bound `diam ≤ dist s t` needed for the coin
arithmetic, and is preserved by the level step. -/

/-- Tautness bounds the diameter by the marked distance. -/
theorem taut_diam (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    (x y : X) : dist x y ≤ dist s t := by
  have h1 := dist_triangle x s y
  have h2 := dist_triangle x t y
  have h3 := htaut x
  have h4 := htaut y
  have h5 := dist_comm x s
  have h6 := dist_comm x t
  have h7 := dist_comm y t
  linarith

/-- Distance from the start junction to a right-chain point reduces to the
chain. -/
theorem step_dist_stepS_inr
    (q : {u : Chain3Point X s t //
      u ≠ Chain3.start s t ∧ u ≠ Chain3.stop s t hst}) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (stepS s t hst) (Sum.inr q : Step s t hst)
      = dist (Chain3.start s t) q.1 := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [show dist (stepS s t hst) (Sum.inr q : Step s t hst)
      = min (dist (Chain3.start s t) (Chain3.start s t)
          + dist (Chain3.start s t) q.1)
        (dist (Chain3.start s t) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) q.1)
    from step_dist_inl_inr s t hst _ _, dist_self, zero_add]
  refine min_eq_left ?_
  exact dist_triangle (Chain3.start s t) (Chain3.stop s t hst) q.1

/-- Distance from a right-chain point to the stop junction reduces to the
chain. -/
theorem step_dist_inr_stepT
    (q : {u : Chain3Point X s t //
      u ≠ Chain3.start s t ∧ u ≠ Chain3.stop s t hst}) :
    letI := stepMetric s t hst
    letI := chain3Metric X s t hst
    dist (Sum.inr q : Step s t hst) (stepT s t hst)
      = dist q.1 (Chain3.stop s t hst) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [dist_comm]
  rw [show dist (stepT s t hst) (Sum.inr q : Step s t hst)
      = min (dist (Chain3.stop s t hst) (Chain3.start s t)
          + dist (Chain3.start s t) q.1)
        (dist (Chain3.stop s t hst) (Chain3.stop s t hst)
          + dist (Chain3.stop s t hst) q.1)
    from step_dist_inl_inr s t hst _ _, dist_self, zero_add]
  rw [dist_comm q.1 (Chain3.stop s t hst)]
  refine min_eq_right ?_
  calc dist (Chain3.stop s t hst) q.1
      ≤ dist (Chain3.stop s t hst) (Chain3.start s t)
        + dist (Chain3.start s t) q.1 := dist_triangle _ _ _

/-- Chain-level tautness through the three copies. -/
theorem chain_taut (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    (p : Chain3Point X s t) :
    letI := chain3Metric X s t hst
    dist (Chain3.start s t) p + dist p (Chain3.stop s t hst)
      = 3 * dist s t := by
  letI := chain3Metric X s t hst
  rcases p with (x | ⟨x, hx⟩) | ⟨x, hx⟩
  · -- copy 0
    show dist (Chain3.start s t) (Chain3.emb0 s t x)
      + dist (Chain3.emb0 s t x) (Chain3.stop s t hst) = 3 * dist s t
    rw [dist_comm (Chain3.start s t) (Chain3.emb0 s t x),
      chain_dist_emb0_start hst x, chain_dist_emb0_stop hst x]
    have h1 := htaut x
    have h2 := dist_comm x s
    linarith
  · -- copy 1
    show dist (Chain3.start s t) (Chain3.emb1 s t x hx)
      + dist (Chain3.emb1 s t x hx) (Chain3.stop s t hst) = 3 * dist s t
    rw [dist_comm (Chain3.start s t) (Chain3.emb1 s t x hx),
      chain_dist_emb1_start hst x hx, chain_dist_emb1_stop hst x hx]
    have h1 := htaut x
    linarith
  · -- copy 2
    show dist (Chain3.start s t) (Chain3.emb2 s t x hx)
      + dist (Chain3.emb2 s t x hx) (Chain3.stop s t hst) = 3 * dist s t
    rw [dist_comm (Chain3.start s t) (Chain3.emb2 s t x hx),
      chain_dist_emb2_start hst x hx, chain_dist_emb2_stop hst x hx]
    have h1 := htaut x
    linarith

/-- The level step preserves tautness. -/
theorem step_taut (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    (p : Step s t hst) :
    letI := stepMetric s t hst
    dist (stepS s t hst) p + dist p (stepT s t hst)
      = dist (stepS s t hst) (stepT s t hst) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  rw [dist_stepS_stepT s t hst]
  rcases p with p | q
  · show dist (Sum.inl (Chain3.start s t) : Step s t hst) (Sum.inl p)
      + dist (Sum.inl p : Step s t hst)
          (Sum.inl (Chain3.stop s t hst)) = 3 * dist s t
    rw [step_dist_inl_inl, step_dist_inl_inl]
    exact chain_taut s t hst htaut p
  · rw [step_dist_stepS_inr s t hst q, step_dist_inr_stepT s t hst q]
    exact chain_taut s t hst htaut q.1

end ThetaChain

end KServer


