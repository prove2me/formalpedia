-- Prove2me | Definitions.Def_AbelianCayleyHDX_Htilde
-- name    : AbelianCayleyHDX_Htilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:41.77621+00:00
-- url     : https://prove2.me/theorems/efcc5399-e564-49cc-8289-fd7f0c1af5f2
-- title:
--   The real 0/1 matrix $\tilde H$
-- statement:
--   For a binary matrix $H$, $\tilde H$ is the real 0/1 matrix with the same entries. Thus $\tilde H^{\mathsf T} \tilde H$ is the real Gram matrix whose $(i,j)$-entry counts the rows in which columns $i$ and $j$ both have entry one.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.1, p.8

import Mathlib

namespace AbelianCayleyHDX

/-- **The real 0/1 matrix `H̃`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.1, p.8): "for a binary matrix `H`, let `H̃`
denote the real 0/1 matrix with the same entries". -/
def Htilde {ι κ : Type*} (H : Matrix ι κ (ZMod 2)) : Matrix ι κ ℝ :=
  Matrix.of fun r c => ((H r c).val : ℝ)

end AbelianCayleyHDX


