-- Prove2me | Definitions.Def_PolygonPack_IsTwoTrackSelection
-- name    : PolygonPack_IsTwoTrackSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:09.672301+00:00
-- url     : https://prove2.me/theorems/ca9e7738-7f2d-4606-9b89-877c4e81bf2c
-- title:
--   Two tracks with deadlines, and their encoders
-- statement:
--   Consider jobs of heights $h_i$ with capacities $C_i$, offset $z_0$ and reserve $\sigma$. A selection $S$ with tracks and start times is a **two-track selection** if every selected job starts at or after $z_0$ and finishes by $C_k/2$, and jobs on one track do not overlap. The hypotheses of Lemma C.7 are collected in `IsTrackData`, and its profit conclusion in `DominatesPrefix`:
--   $$
--   \frac{1-\sigma}\alpha\,\pi(S')\le\pi(S)\quad\text{for all }\alpha\ge1\text{ and all }S'\text{ with }\sum_{i\in S',\,i\le k}h_i\le\alpha C_k\ \ \forall k.
--   $$
--   `encJobs` and `encTrackOut` are the binary encoders of the rational version.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma C.7, p.37

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PolygonPack_encInstance
open OnlineCRS.Combine

namespace PolygonPack

/-- The preamble of Lemma C.7 (p.37) and its offset hypothesis: positive heights with `h_i ≤ cC_i`, positive
nondecreasing capacities, nonnegative profits, `z0 ≥ 0`, `0 < σ < 1`, and `2z0/C_k + 2c ≤ σ` for every `k`. -/
def IsTrackData {m : ℕ} (c : ℝ) (h π C : Fin m → ℝ) (z0 σ : ℝ) : Prop :=
  (∀ i, 0 < h i ∧ h i ≤ c * C i ∧ 0 ≤ π i ∧ 0 < C i) ∧ Monotone C ∧ 0 ≤ z0 ∧ 0 < σ ∧ σ < 1 ∧
    ∀ k, 2 * z0 / C k + 2 * c ≤ σ

/-- **Two tracks with deadlines.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma C.7, p.37: "two tracks starting at z0 can be constructed [...] such that
every selected job k finishes by its deadline C_k/2."

`IsTwoTrackSelection h C z0 S track start`: every selected job starts at or after `z0` and finishes by `C_k/2`, and the
jobs on one track have disjoint intervals.

**Formalization Note.** `Fin 2` names the tracks. -/
def IsTwoTrackSelection {m : ℕ} (h C : Fin m → ℝ) (z0 : ℝ) (S : Finset (Fin m)) (track : Fin m → Fin 2)
    (start : Fin m → ℝ) : Prop :=
  (∀ k ∈ S, z0 ≤ start k ∧ start k + h k ≤ C k / 2) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → track i = track j →
      Disjoint (Set.Ioo (start i) (start i + h i)) (Set.Ioo (start j) (start j + h j))

/-- The selection recovers `(1 − σ)/α` of the profit of every subset whose prefix loads are at most `αC_k`, for every
`α ≥ 1` (Lemma C.7, p.37). -/
def DominatesPrefix {m : ℕ} (h π C : Fin m → ℝ) (σ : ℝ) (S : Finset (Fin m)) : Prop :=
  ∀ α : ℝ, 1 ≤ α → ∀ S' : Finset (Fin m),
    (∀ k, ∑ i ∈ S'.filter (· ≤ k), h i ≤ α * C k) →
      (1 - σ) * (∑ i ∈ S', π i) / α ≤ ∑ i ∈ S, π i

/-- Rational job data `(h, C, π)`, in a list. -/
def encJobs (l : List (ℚ × ℚ × ℚ)) : List Sym :=
  encList (fun j => encRat j.1 ++ [(3 : Sym)] ++ encRat j.2.1 ++ [(3 : Sym)] ++ encRat j.2.2) l

/-- A track output: entries `(job, track, start)`. -/
def encTrackOut (l : List (ℕ × Bool × ℚ)) : List Sym :=
  encList (fun e => encNat e.1 ++ [(3 : Sym)] ++ [if e.2.1 then (1 : Sym) else (0 : Sym)] ++ [(3 : Sym)] ++
    encRat e.2.2) l

/-- The list `out` names exactly `S`, without repetition, with those tracks and start times. -/
def TrackOutRealizes {m : ℕ} (out : List (ℕ × Bool × ℚ)) (S : Finset (Fin m)) (track : Fin m → Fin 2)
    (start : Fin m → ℝ) : Prop :=
  (out.map Prod.fst).Nodup ∧ (∀ k : Fin m, k ∈ S ↔ k.val ∈ out.map Prod.fst) ∧
    ∀ e ∈ out, ∃ k : Fin m, k.val = e.1 ∧ track k = (if e.2.1 then 1 else 0) ∧ start k = ((e.2.2 : ℚ) : ℝ)

end PolygonPack


