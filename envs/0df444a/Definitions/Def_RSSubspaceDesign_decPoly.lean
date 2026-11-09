-- Prove2me | Definitions.Def_RSSubspaceDesign_decPoly
-- name    : RSSubspaceDesign_decPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:33.588363+00:00
-- url     : https://prove2.me/theorems/43664560-b8c5-44f0-9889-1a268ab4967c
-- title:
--   A polynomial over $K=\mathbb F_p[Y]/(f)$ from its coefficient lists
-- statement:
--   A list $[c_0,\dots,c_D]$ of coordinate lists names the polynomial $\sum_j \bar c_j X^j\in K[X]$, where $\bar c_j\in K$ is the element named by $c_j$.
--
--   An algorithm outputs an extension field $F/K$ as a monic irreducible $h\in K[X]$, $F=K[X]/(h)$, written by its coefficient lists; a point of $F$ is written by its $\deg h$ coordinates in the power basis of $F/K$, i.e. as the residue of the polynomial these lists name.
--
--   **Formalization Note** Decoding is structural (sums and the quotient map); no choice is involved.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 1.1, p.4 (PDF p.6); Theorem 7.2, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_RSSubspaceDesign_decK

open Polynomial

namespace RSSubspaceDesign

/-- **A polynomial over the input field `K = 𝔽_p[Y]/(f)` from its coefficient list.**
Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.1,
p.4 and Theorem 7.2, p.40 (the constructed extension `F/K`).

The list `[c₀, …, c_D]` of coordinate lists stands for `∑ⱼ decK(cⱼ) Xʲ ∈ K[X]`.

**Formalization Note.** An extension `F/K` is output as a monic irreducible `h ∈ K[X]`,
`F = AdjoinRoot h`, written as its `deg h + 1` coefficients; a point of `F` is written by its
`deg h` coordinates in the power basis of `F/K` and decoded as `AdjoinRoot.mk h (decPoly p f c)`.
Decoding is structural; no choice is involved. -/
noncomputable def decPoly (p : ℕ) (f : (ZMod p)[X]) (hc : List (List ℕ)) : (AdjoinRoot f)[X] :=
  ∑ j : Fin hc.length, C (decK p f (hc.get j)) * X ^ (j : ℕ)

end RSSubspaceDesign


