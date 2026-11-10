-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_setSystems
-- name    : SmallClassesNeighbourhood_Linear_setSystems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:00.416847+00:00
-- url     : https://prove2.me/theorems/478e0c49-5588-4180-a4d4-70351d596dda
-- title:
--   Finite set families, separation and the shatter function
-- statement:
--   Let A be a finite set of vertices and let H be a finite family of subsets. Its traces on U are the distinct intersections with U. Separation uses strict symmetric-difference distance:
--
--   $$H|_U=\{X\cap U:X\in H\},\qquad X\ne Y\Longrightarrow |X\triangle Y|>t.$$
--
--   The shatter function τ_H(k) is the maximum of |H|_U| over k-element subsets U of A. It is implemented as a finite natural maximum; it is used only for k ≤ |A|, when there is an indexing subset. Its out-of-domain empty maximum is zero. The packing theorem uses Mathlib's finite-family VC dimension, with H nonempty and dimension at least one. These objects also cover empty families for Corollary 10.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §2.1, printed p. 7 (PDF p. 8)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

noncomputable section

namespace SmallClassesNeighbourhood.Linear
variable {V : Type} [Fintype V] [DecidableEq V]

def familyTraces (ℋ : Finset (Finset V)) (U : Finset V) : Finset (Finset V) := by
  classical
  exact ℋ.image (fun X => X ∩ U)

def Separated (t : ℕ) (ℛ : Finset (Finset V)) : Prop :=
  ∀ X ∈ ℛ, ∀ Y ∈ ℛ, X ≠ Y → t < (symmDiff X Y).card

/-- Only used at k ≤ |A|; the finite maximum is zero if its indexing family is empty. -/
def shatterFunction (A : Finset V) (ℋ : Finset (Finset V)) (k : ℕ) : ℕ := by
  classical
  exact (A.powersetCard k).sup (fun U => (familyTraces ℋ U).card)

end SmallClassesNeighbourhood.Linear


