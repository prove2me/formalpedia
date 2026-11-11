-- Prove2me | Definitions.Def_HopfieldPSpin_Shattering_MultilinearPoly
-- name    : HopfieldPSpin_Shattering_MultilinearPoly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:07:48.983197+00:00
-- url     : https://prove2.me/theorems/fe2aaec7-2369-41ce-8733-bee56d3bb4b2
-- title:
--   Homogeneous multilinear polynomials of degree $p$
-- statement:
--   A **homogeneous multilinear polynomial of degree $p$** in $N$ variables is
--   $$Y(z)=\sum_{I\subseteq[N],\,|I|=p}c_I\prod_{i\in I}z_i ,$$
--   so every monomial has degree $p$ and each variable has exponent at most one in each monomial. It is given by its coefficients $(c_I)$; only those of the size-$p$ sets enter.
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 17 (PDF 19), §4.1 'Hypercontractivity'; p. 18 (PDF 20), proof of Lemma 4.4

import Mathlib

noncomputable section

namespace HopfieldPSpin.Shattering

/-- A homogeneous multilinear polynomial of degree `p` in `N` variables,
`Y(z) = ∑_{I ⊆ [N], |I| = p} c_I ∏_{i ∈ I} z_i`, given by its coefficient family
`c : Finset (Fin N) → ℝ` (only the coefficients of the size-`p` sets enter). Every monomial
has degree `p` and each variable appears with exponent at most one (§4.1, p. 17). -/
def multilinPoly {N : ℕ} (p : ℕ) (c : Finset (Fin N) → ℝ) (z : Fin N → ℝ) : ℝ :=
  ∑ I ∈ Finset.powersetCard p (Finset.univ : Finset (Fin N)), c I * ∏ i ∈ I, z i

end HopfieldPSpin.Shattering


