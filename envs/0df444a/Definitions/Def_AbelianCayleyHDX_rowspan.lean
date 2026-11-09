-- Prove2me | Definitions.Def_AbelianCayleyHDX_rowspan
-- name    : AbelianCayleyHDX_rowspan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:36.916868+00:00
-- url     : https://prove2.me/theorems/100fcf98-27dc-4d47-b55a-6ef1f351591d
-- title:
--   Binary row space $R_H$
-- statement:
--   For a binary matrix $H \in \mathbb F_2^{R \times M}$ (rows and columns indexed by finite types), $R_H = \mathrm{rowspan}_{\mathbb F_2} H$ is the $\mathbb F_2$-span of its rows in $\mathbb F_2^M$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9

import Mathlib

namespace AbelianCayleyHDX

/-- **The binary row space `R_H = rowspan_{𝔽₂} H`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9): the
`𝔽₂`-span of the rows of a binary matrix `H` (rows indexed by `ι`, columns by `κ`). -/
def rowspan {ι κ : Type*} (H : Matrix ι κ (ZMod 2)) : Submodule (ZMod 2) (κ → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range H)

end AbelianCayleyHDX


