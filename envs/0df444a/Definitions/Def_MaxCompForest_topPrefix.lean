-- Prove2me | Definitions.Def_MaxCompForest_topPrefix
-- name    : MaxCompForest_topPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:45.937309+00:00
-- url     : https://prove2.me/theorems/2a4f578f-3186-4c85-af97-1b7882cf2d9b
-- title:
--   The top $M$ labels by diagonal, with fixed ties
-- statement:
--   The first $M$ labels of a finite linearly ordered label set, in decreasing order of a score $p$, with ties broken by the fixed label order. A label belongs to the prefix when fewer than $M$ labels precede it.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), proof of Lemma E.2, p.39

import Mathlib

namespace MaxCompForest

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open Classical in
/-- **The first `M` labels in decreasing order of `p`**, ties broken by a fixed label order: `e` is in the
prefix when fewer than `M` labels come before it.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), proof of Lemma E.2, p.39 ("the top `M0` diagonals"). -/
noncomputable def topPrefix (p : ι → ℝ) (M : ℕ) : Finset ι :=
  Finset.univ.filter fun e =>
    (Finset.univ.filter fun f => p e < p f ∨ (p e = p f ∧ f < e)).card < M

end MaxCompForest


