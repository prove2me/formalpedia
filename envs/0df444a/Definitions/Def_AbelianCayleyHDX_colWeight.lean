-- Prove2me | Definitions.Def_AbelianCayleyHDX_colWeight
-- name    : AbelianCayleyHDX_colWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:37.581307+00:00
-- url     : https://prove2.me/theorems/bed01498-89b6-4158-ba91-416fbbbf0406
-- title:
--   Weight of a column of a binary matrix
-- statement:
--   The weight of column $c$ of a binary matrix $H$ is the number of its nonzero entries.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9

import Mathlib

namespace AbelianCayleyHDX

/-- **The weight of a column** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9): the number of nonzero entries of
column `c` of the binary matrix `H`. -/
def colWeight {ι κ : Type*} [Fintype ι] (H : Matrix ι κ (ZMod 2)) (c : κ) : ℕ :=
  (Finset.univ.filter fun r => H r c ≠ 0).card

end AbelianCayleyHDX


