-- Prove2me | Definitions.Def_CoverTime537_SpecifiedStart_Walk
-- name    : CoverTime537_SpecifiedStart_Walk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:24.803569+00:00
-- url     : https://prove2.me/theorems/8c8cc07c-4bed-49a6-a835-46f2e130c206
-- title:
--   Ordinary graph walk, cover expectation, and discovery events
-- statement:
--   For a finite simple graph $H$, the transition probability from a nonisolated vertex is the reciprocal of its degree on every incident edge. An isolated vertex is absorbing; on connected instances this affects only the singleton. The full-cover expectation is
--
--   $$C_H(s)=\sum_{t\ge0}\mathbb P_s(\text{some vertex is still unseen at time }t).$$
--
--   The starting vertex is visited at time zero. The last-discovery event is a sum of disjoint first-hit cylinders: $v$ has not appeared earlier and all other vertices have appeared earlier. The module also defines first-hit probabilities for finite local substochastic chains. These definitions share the published trajectory semantics; summability remains an explicit supporting proof obligation.
-- source:
--   Ryan Aghazadeh, STOC 2027 submission #537 (October 2026), §1 p.2 (1), §3 p.7 (6), §5 pp.9–10

import Mathlib
import Definitions.Def_mm_network

namespace CoverTime537.SpecifiedStart
noncomputable section
open scoped BigOperators

/-- Ordinary uniform-neighbor walk, absorbing at an isolated vertex (only the
singleton is used when connected). Source §1, p.2; no holding probability is added. -/
def walk {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact fun x y => if H.degree x = 0 then if x = y then 1 else 0
    else MarkovMixing.graphWalk H x y

/-- Full-cover expectation, counting the starting visit at time zero. -/
def cover {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (x : V) : ℝ :=
  MarkovMixing.expCoverTime (walk H) x

/-- Probability that v is discovered last: disjoint finite first-hit cylinders.
At time t all vertices except v have appeared strictly before t, and v has not. -/
def lastAt {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x v : V) (t : ℕ) : ℝ := by
  classical
  exact ∑ w : Fin (t + 1) → V,
    if w 0 = x ∧ w (Fin.last t) = v ∧
      (∀ i : Fin (t+1), i.val < t → w i ≠ v) ∧
      (∀ y, y ≠ v → ∃ i : Fin (t+1), i.val < t ∧ w i = y)
    then MarkovMixing.pathWeight (walk H) w else 0

def lastProb {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x v : V) : ℝ := ∑' t, lastAt H x v t

/-- Finite path event: first hit of a target set B occurs at y at time t.
This is also used on the small killed local chains in §5. -/
def hitAt {V : Type} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Set V) (x y : V) (t : ℕ) : ℝ := by
  classical
  exact ∑ w : Fin (t+1) → V,
    if w 0 = x ∧ w (Fin.last t) = y ∧ y ∈ B ∧
      (∀ i : Fin (t+1), i.val < t → w i ∉ B)
    then MarkovMixing.pathWeight P w else 0

def hitProb {V : Type} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Set V) (x y : V) : ℝ := ∑' t, hitAt P B x y t

end
end CoverTime537.SpecifiedStart


