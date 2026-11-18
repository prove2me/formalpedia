-- Prove2me | Definitions.Def_KoanaKPaths_ExteriorCoordinates
-- name    : KoanaKPaths_ExteriorCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:17:48.028405+00:00
-- url     : https://prove2.me/theorems/c87809af-1c06-4654-8981-da77e9f9ece2
-- title:
--   Subset coordinates and right multiplication by a vector
-- statement:
--   Integer coordinates for the exterior algebra on a basis of size $k$, indexed by the subsets $S\subseteq\{0,\ldots,k-1\}$. The unit has coordinate one at the empty subset and zero elsewhere. For an array $A$ and a vector $v$, right multiplication by $v$ is specified by
--
--   $$
--   (A\wedge v)_S=\sum_{r\in S}(-1)^{|S|-1+\operatorname{rank}_S(r)}A_{S\setminus\{r\}}v_r,
--   $$
--
--   where the rank is zero-based in increasing order. Repeated right multiplication evaluates a word of vectors. These are the coordinate operations used by the paper's circuit and walk dynamic programs; each output coordinate of a right product has at most $k$ summands.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, Section 2, printed p. 5 / PDF p. 6 (exterior coordinates, right multiplication by a vector, determinant identity), and Section 3.2, printed p. 9 / PDF p. 10 (factorial coefficient bound). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Mathlib

open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates

/-- Integer coordinates of the exterior algebra, indexed by all subsets of the basis. -/
abbrev Coordinates (k : ℕ) := Finset (Fin k) → ℤ

/-- The unit has coefficient one at the empty subset and zero elsewhere. -/
def unit (k : ℕ) : Coordinates k := fun S => if S = ∅ then 1 else 0

/-- Right multiplication by a vector. For the selected row in a subset, its position in
increasing order gives the cofactor sign. The parity equals the number of larger rows. -/
def wedgeRight {k : ℕ} (A : Coordinates k) (v : Fin k → ℤ) : Coordinates k := fun S =>
  ∑ r : S, (-1 : ℤ) ^ (S.card-1+S.sort.idxOf r.val) * A (S.erase r.val) * v r.val

/-- Evaluate a sequence of vectors by repeated right multiplication, starting at the unit. -/
def wordCoordinates {k : ℕ} (vs : List (Fin k → ℤ)) : Coordinates k :=
  vs.foldl wedgeRight (unit k)

end KoanaKPaths.ExteriorCoordinates


