-- Prove2me | Definitions.Def_AbelianCayleyHDX_rowWeight
-- name    : AbelianCayleyHDX_rowWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:15.839782+00:00
-- url     : https://prove2.me/theorems/b23fe6af-c550-44d8-ad97-20a2c6d39f37
-- title:
--   Weight of a row of a binary matrix
-- statement:
--   The weight of row $r$ of a binary matrix $H$ is the number of its nonzero entries.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9

import Mathlib

namespace AbelianCayleyHDX

/-- **The weight of a row** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9): the number of nonzero entries of row `r`
of the binary matrix `H`. -/
def rowWeight {ι κ : Type*} [Fintype κ] (H : Matrix ι κ (ZMod 2)) (r : ι) : ℕ :=
  (Finset.univ.filter fun c => H r c ≠ 0).card

end AbelianCayleyHDX


