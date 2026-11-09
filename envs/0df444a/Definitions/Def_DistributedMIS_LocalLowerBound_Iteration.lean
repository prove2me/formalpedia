-- Prove2me | Definitions.Def_DistributedMIS_LocalLowerBound_Iteration
-- name    : DistributedMIS_LocalLowerBound_Iteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:28.958801+00:00
-- url     : https://prove2.me/theorems/ee13ab4a-f869-4d7a-aec4-3b7a3238c6a5
-- title:
--   Actual reduction sequence and original-coordinate restrictions
-- statement:
--   Starting with a radius-r rule A, at step j compute its m most probable nonzero coordinates given the radius-(r-j-1) view, retain precisely those coordinates, and resample the kept law conditionally on that smaller view. This defines A_j recursively, rather than postulating a sequence of estimates.
--
--   $$S=\epsilon(A_r)+\sum_{j<r}\epsilon(D_j).$$
--
--   On the original rule's probability space, the hatted survivor retains the original coordinate precisely when it has passed all earlier lists; the hatted deleted part retains it at its first failed list. The definitions also express restriction, conditional support, and the deterministic first-failure partition. These objects support the full multi-round accounting without assuming its conclusions.
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; §9.1, p. 24; §10.2, pp. 27–28 (printed = PDF)

import Definitions.Def_DistributedMIS_LocalLowerBound_EdgeRules

noncomputable section

namespace DistributedMIS.LocalLowerBound

def iterateRule (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) : ℕ → RawRule k
  | 0 => A
  | j + 1 =>
    let B := iterateRule G r m A j
    let s := r - j
    resample G s (s-1) (keepBy B (truncationList G s m B))

def iterationList (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (j : ℕ) :=
  truncationList G (r-j) m (iterateRule G r m A j)

def iterationDeleted (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (j : ℕ) :=
  deleteBy (iterateRule G r m A j) (iterationList G r m A j)

def originalList (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (j v : ℕ) (ω : Matrices k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun a => ∀ i < j, a ∈ iterationList G r m A i v ω)

def originalSurvivor (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (j : ℕ) :=
  keepBy A (originalList G r m A j)

def originalDeleted (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (j : ℕ) :=
  deleteBy (originalSurvivor G r m A j) (iterationList G r m A j)

def totalConflict (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) (u v : ℕ) :=
  conflict G 0 (iterateRule G r m A r) u v +
  ∑ j ∈ Finset.range r, conflict G (r-j) (iterationDeleted G r m A j) u v

/-- Literal restriction of each original coordinate; includes the zero probability. -/
def IsRestriction {k : ℕ} (A B : RawRule k) : Prop :=
  ∀ v ω, ∃ P : Finset (Fin k), B v ω = (keepBy A (fun _ _ => P)) v ω

/-- Kernel-level partition coupled by the original private draw, not independent parts. -/
def PartitionsOriginal (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r m : ℕ) (A : RawRule k) : Prop :=
  ∀ v ω a, (originalSurvivor G r m A r) v ω (some a) +
      (∑ j ∈ Finset.range r, (originalDeleted G r m A j) v ω (some a)) = A v ω (some a) ∧
    ((Finset.range r).filter (fun j => a ∈ originalList G r m A j v ω ∧
      a ∉ iterationList G r m A j v ω)).card +
      (if a ∈ originalList G r m A r v ω then 1 else 0) = 1

end DistributedMIS.LocalLowerBound


