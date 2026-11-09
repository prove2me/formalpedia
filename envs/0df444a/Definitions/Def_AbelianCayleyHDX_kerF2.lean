-- Prove2me | Definitions.Def_AbelianCayleyHDX_kerF2
-- name    : AbelianCayleyHDX_kerF2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:55.992294+00:00
-- url     : https://prove2.me/theorems/857a35ba-a6f2-4e02-93b5-486d121fb97b
-- title:
--   Binary kernel $\ker H$
-- statement:
--   For a binary matrix $H$, $\ker H = \{v \in \mathbb F_2^M : Hv = 0\}$, taken over $\mathbb F_2$. It is the dual code of the row space: $\ker H = R_H^\perp$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.1, p.8

import Mathlib

namespace AbelianCayleyHDX

/-- **The binary kernel `ker H`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.1, p.8: "kernels and row spans of `H` are taken
over `𝔽₂`"): the vectors `v ∈ 𝔽₂^κ` with `H v = 0`. -/
def kerF2 {ι κ : Type*} [Fintype κ] (H : Matrix ι κ (ZMod 2)) : Submodule (ZMod 2) (κ → ZMod 2) :=
  LinearMap.ker H.mulVecLin

end AbelianCayleyHDX


