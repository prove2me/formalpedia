-- Prove2me | Definitions.Def_PSDPolyApprox_chi
-- name    : PSDPolyApprox_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:54.724982+00:00
-- url     : https://prove2.me/theorems/f3dc89f4-41ea-4708-a8c9-741b0646ea33
-- title:
--   Character $\chi_S(x)=\prod_{j\in S}x_j$ on $H_n$
-- statement:
--   For $S\subseteq\{1,\dots,n\}$ and $x\in H_n$, the **character** (multilinear monomial)
--   $$
--   \chi_S(x)=\prod_{j\in S}x_j,\qquad \chi_\emptyset\equiv1.
--   $$
--   The homogeneous multilinear polynomials of degree $i$ on $H_n$ are the linear combinations of the $\chi_S$ with $|S|=i$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube

namespace PSDPolyApprox

/-- **Character (monomial) `χ_S` on the hypercube.**
Fawzi, arXiv:1811.09649v1, §2.1, p.3: the Fourier expansion `f = f0 + f1 + · · · + fn` "where
each fi is a homogeneous multilinear polynomial of degree i"; the multilinear monomials are the
`χ_S`.

`chi S x = ∏_{j ∈ S} xⱼ` for `S ⊆ {1, …, n}` and `x ∈ Hₙ` (`chi ∅ = 1`). -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ j ∈ S, ((x j : ℤ) : ℝ)

end PSDPolyApprox


