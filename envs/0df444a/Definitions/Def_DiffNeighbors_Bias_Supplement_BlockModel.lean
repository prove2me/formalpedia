-- Prove2me | Definitions.Def_DiffNeighbors_Bias_Supplement_BlockModel
-- name    : DiffNeighbors_Bias_Supplement_BlockModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:12:35.854747+00:00
-- url     : https://prove2.me/theorems/fa5674a5-d28f-4f8b-8f58-48efc23e6a65
-- title:
--   Lemma 1 — simultaneous block updates and their signed mixed difference
-- statement:
--   For a finite set $S$ of coordinates, let $z^{S=b}$ set every coordinate of $S$ to $b\in\{0,1\}$ and leave all others unchanged. Define
--   $$D_{S,T}h(z)=h(z^{S=1,T=1})-h(z^{S=1,T=0})-h(z^{S=0,T=1})+h(z^{S=0,T=0}).$$
--   The $S$ update precedes the $T$ update. In Lemma 1 the blocks are disjoint, so the updates commute. The source clusters give $S=C_j\cap\mathcal N_i$, $T=C_k\cap\mathcal N_i$; all other entries retain their original values.
--
--   These definitions express Lemma 1's block notation for every block size. An empty block gives zero mixed difference. They assert no smoothness bound.
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 28, Appendix A.2, Lemma 1

import Mathlib

namespace DiffNeighbors.Bias.Supplement

variable {ι : Type*} [DecidableEq ι]

/-- Set all entries in S to b, leaving every other entry unchanged.
This is the block treatment notation z^{1_m}, z^{0_m} of Lemma 1 (p. 28). -/
def setBlock (S : Finset ι) (b : Bool) (z : ι → Bool) : ι → Bool :=
  fun j => if j ∈ S then b else z j

/-- The signed block mixed difference of Lemma 1 (p. 28). The S update
is made first and the T update second. The lemma requires Disjoint S T. -/
def blockDiff (h : (ι → Bool) → ℝ) (S T : Finset ι) (z : ι → Bool) : ℝ :=
  h (setBlock T true (setBlock S true z))
    - h (setBlock T false (setBlock S true z))
    - h (setBlock T true (setBlock S false z))
    + h (setBlock T false (setBlock S false z))

end DiffNeighbors.Bias.Supplement


