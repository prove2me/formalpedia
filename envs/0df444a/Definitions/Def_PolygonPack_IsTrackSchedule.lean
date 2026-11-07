-- Prove2me | Definitions.Def_PolygonPack_IsTrackSchedule
-- name    : PolygonPack_IsTrackSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:58:13.970046+00:00
-- url     : https://prove2.me/theorems/00ba90e0-7b7b-48f4-aab2-605e19c66f54
-- title:
--   Track schedules and job data
-- statement:
--   A set $S$ of jobs with latest starts $d_i$ and processing times $p_i$ has an **$m$-track schedule** if each job can be assigned a track and a start time in $[0,d_i]$ so that jobs on one track have non-overlapping intervals $[\text{start},\text{start}+p_i]$.
--
--   The **job data** of a positive-Tight polygon are $d$ and the vertical span $p$ of a canonical pose, and those of a Slack polygon are $d=\delta/2-h$, $p=h$. The completion deadline is $\Delta=d+p$.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.2, p.8; Lemma A.7, p.29

import Mathlib
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight

namespace PolygonPack

/-- **Track schedules and the job data.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.2, p.8 (page of the main text) and App. B, p.29: a track is a
sequence of non-overlapping job intervals, each starting at a nonnegative time no later than its latest start.
Lemma A.7, p.29: "a positive-Tight polygon has latest start d, processing time p, and completion deadline
Δ = d + p [...] For a diagonal Slack polygon, the corresponding data are d = δ/2 − h > 0, p = h, Δ = δ/2."

`IsTrackSchedule d p S m`: the jobs of `S` can be put on `m` tracks. `IsJobData c a0 v d p`: `(d, p)` are the job data
of a positive-Tight or Slack polygon, with `p` the vertical span of some canonical pose.

**Formalization Note.** `p` depends on the chosen maximizer, so `IsJobData` allows every canonical pose. Open
intervals express non-overlap. -/
def IsTrackSchedule {ι : Type} (d p : ι → ℝ) (S : Finset ι) (m : ℕ) : Prop :=
  ∃ (track : ι → Fin m) (start : ι → ℝ),
    (∀ i ∈ S, 0 ≤ start i ∧ start i ≤ d i) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → track i = track j →
        Disjoint (Set.Ioo (start i) (start i + p i)) (Set.Ioo (start j) (start j + p j))

/-- `(d, p)` are the job data of a positive-Tight polygon or of a diagonal Slack polygon. -/
def IsJobData (c a0 : ℝ) (v : List (ℚ × ℚ)) (d p : ℝ) : Prop :=
  (IsTPlus c a0 v ∧ d = canonD v ∧
      ∃ T, IsCanonicalPose v (diamPair v).1 (diamPair v).2 T ∧ p = vSpan (placedUV v T)) ∨
    (IsSlack c a0 v ∧ d = polyDelta v / 2 - polyH v ∧ p = polyH v)

end PolygonPack


