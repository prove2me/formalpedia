-- Prove2me | Definitions.Def_BorderD4_toK
-- name    : BorderD4_toK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:33.08292+00:00
-- url     : https://prove2.me/theorems/d65c15b3-7a77-4bcb-a74c-b15cec227319
-- title:
--   The maps $F[[\varepsilon]][x]\to F((\varepsilon))[x]$ and $\pi$, and the ideal $\langle\varepsilon,x\rangle$
-- statement:
--   This item names the inclusion $F[[\varepsilon]][x]\to F((\varepsilon))[x]$, through which $p\cap F[[\varepsilon]][x]$ and $IF((\varepsilon))[x]$ are expressed; the ideal $\langle\varepsilon,x_1,\dots,x_N\rangle$ of $F[[\varepsilon]][x]$; and the homomorphism $\pi:F[[\varepsilon]][x]\to F[x]$ sending $\varepsilon$ to $0$ and fixing $F[x]$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {F σ : Type*} [Field F]

/-- The inclusion `F[[ε]][x] → F((ε))[x]`. The contraction `p ∩ F[[ε]][x]` of an ideal `p` of `F((ε))[x]` is
`p.comap toK`, and `I F((ε))[x]` is `I.map toK`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40. -/
noncomputable def toK : MvPolynomial σ F⟦X⟧ →+* MvPolynomial σ (LaurentSeries F) :=
  map (algebraMap F⟦X⟧ (LaurentSeries F))

/-- The ideal `⟨ε, x_1, …, x_N⟩` of `F[[ε]][x]`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40. -/
noncomputable def epsXIdeal (F σ : Type*) [Field F] : Ideal (MvPolynomial σ F⟦X⟧) :=
  Ideal.span ({MvPolynomial.C PowerSeries.X} ∪ Set.range X)

/-- The homomorphism `π : F[[ε]][x] ↠ F[x]` sending `ε` to `0` and fixing `F[x]`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40. -/
noncomputable def specialize : MvPolynomial σ F⟦X⟧ →+* MvPolynomial σ F :=
  map PowerSeries.constantCoeff

end

end BorderD4


