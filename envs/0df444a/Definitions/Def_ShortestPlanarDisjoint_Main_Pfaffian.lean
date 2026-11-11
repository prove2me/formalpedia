-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Pfaffian
-- name    : ShortestPlanarDisjoint_Main_Pfaffian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:04.635166+00:00
-- url     : https://prove2.me/theorems/5ab90192-c278-4196-a8a1-c8fd3cc832e9
-- title:
--   The characteristic-two perfect-matching Pfaffian
-- statement:
--   A perfect matching of $N$ ordered indices is a fixed-point-free involution. Its
--   unordered pairs are represented once by the smaller endpoint. For a matrix $K$
--   over a commutative ring of characteristic two, define the sign-free matching sum
--
--   $$\operatorname{Pf}(K)=\sum_A\prod_{\{i,j\}\in A,\ i<j}K_{ij}.$$
--
--   On the symmetric zero-diagonal matrices of the source this is the Pfaffian.
--   There is no ordering of pairs or choice of pair directions in the sum, and no
--   factorial or division by two. For no indices there is one empty matching and its
--   product is one. For an odd number of indices there are no perfect matchings and
--   the sum is zero. The definition makes sense on any matrix, while the intended
--   port matrices are alternating in characteristic two. This is distinct from the
--   rational-algebra or complex exterior-power Pfaffians returned by prior-art search.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 2 (Pfaffian definition), p. 5 (PDF p. 7)

import Mathlib

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- A perfect matching is its fixed-point-free involution, so no ordering of pairs
or direction choices multiply its contribution. There is one empty matching. -/
def IndexMatching (N : ℕ) :=
  {p : Equiv.Perm (Fin N) // Function.Involutive p ∧ ∀ i, p i ≠ i}

noncomputable instance (N : ℕ) : Fintype (IndexMatching N) := by
  unfold IndexMatching
  exact Fintype.ofFinite _

/-- The sign-free matching sum used over characteristic two. No factorials,
no division by two, and the empty product is one. -/
noncomputable def matchingPfaffian {R : Type*} [CommRing R] [CharP R 2] {N : ℕ}
    (K : Matrix (Fin N) (Fin N) R) : R := by
  classical
  exact ∑ p : IndexMatching N,
    ∏ i ∈ Finset.univ.filter (fun i : Fin N => i < p.val i), K i (p.val i)

end ShortestPlanarDisjoint.Main


