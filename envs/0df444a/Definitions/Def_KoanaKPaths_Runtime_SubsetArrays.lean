-- Prove2me | Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
-- name    : KoanaKPaths_Runtime_SubsetArrays
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:50:38.651233+00:00
-- url     : https://prove2.me/theorems/6a4fa344-3dd9-499e-a7b8-c3ea171f99a3
-- title:
--   Subset order and exterior coordinate recursion
-- statement:
--   Coordinates of the exterior algebra on k basis vectors are stored as integer lists indexed by subsets. The order recursively puts subsets omitting the last element before those containing it. The bundle defines this ordering, coefficient extraction, and the block recursion for multiplying an array by a vector.
--
--   $$
--   \operatorname{ord}_{k+1}=\operatorname{lower}(\operatorname{ord}_k)\mathbin{+\!+}\operatorname{upper}(\operatorname{ord}_k).
--   $$
--
--   The common ordering makes the mathematical exterior operations and the stack implementation use the same coordinate layout.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Definitions/Def_KoanaKPaths_SubsetArrays.lean; source snapshot SHA-256 f92320afee0c0be7e04d86d5656c129e8b863fc18dd46ee45c38dd9598d4112b.

import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.ExteriorCoordinates

/-- Lift a basis subset without selecting the new largest row. -/
def lowerSet {k : ℕ} (S : Finset (Fin k)) : Finset (Fin (k+1)) :=
  S.map Fin.castSuccOrderEmb.toEmbedding

/-- Lift a basis subset and select the new largest row. -/
def upperSet {k : ℕ} (S : Finset (Fin k)) : Finset (Fin (k+1)) :=
  insert (Fin.last k) (lowerSet S)

/-- Sequential order of basis subsets: the lower half omits the largest row and the upper
half includes it. -/
def subsetOrder : (k : ℕ) → List (Finset (Fin k))
  | 0 => [∅]
  | k+1 => (subsetOrder k).map lowerSet ++ (subsetOrder k).map upperSet

/-- Store coordinates in the sequential subset order. -/
def coefficientList {k : ℕ} (A : Coordinates k) : List ℤ := (subsetOrder k).map A

/-- Right multiplication on sequential arrays by splitting at the largest basis row.
The same vector list is shared by all recursive calls. -/
def wedgeList : (k : ℕ) → List ℤ → List ℤ → List ℤ
  | 0, _, _ => [0]
  | k+1, A, v =>
    let A0 := A.take (2^k)
    let A1 := A.drop (2^k)
    wedgeList k A0 v ++ List.zipWith (fun x y => v.getD k 0*x-y) A0 (wedgeList k A1 v)

end KoanaKPaths.ExteriorCoordinates

end


