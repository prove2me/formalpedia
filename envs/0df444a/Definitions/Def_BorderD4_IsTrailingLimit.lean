-- Prove2me | Definitions.Def_BorderD4_IsTrailingLimit
-- name    : BorderD4_IsTrailingLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:50.558194+00:00
-- url     : https://prove2.me/theorems/03471b5a-1415-43b1-bd64-60ee5dfac43d
-- title:
--   Coefficients $[z^d]A$ and the trailing coefficient $\mathrm{tc}(\lim\tilde A)$
-- statement:
--   For a nonzero $A$ of the form $\varepsilon^{-c}z^{-b}h$ with $h\in F[[\varepsilon]][u][[z]]$, let $\tilde A$ be its normalization in $\varepsilon$ and put $a=\mathrm{val}_\varepsilon(A)$, $b'=\mathrm{val}_z(\lim\tilde A)$. Then
--   $$\mathrm{tc}(\lim\tilde A)=[z^{b'}][\varepsilon^{a}]A\in F[u].$$
--   `IsZRep` records the form of $A$, `zCoeffOf` is $[z^d]A=\varepsilon^{-c}h_{d+b}$, and `IsTrailingLimit A G` says that $G=\mathrm{tc}(\lim\tilde A)$.
--
--   **Formalization Note** All are defined through coefficients of a representation, and do not depend on it.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.2, p.65; Definition 2.5, p.29; Definition 4.1, p.38; proof of Lemma 6.14, pp.65–66

import Mathlib
import Definitions.Def_BorderD4_BorderComputes
import Definitions.Def_BorderD4_Psi
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {F τ : Type*} [Field F]

/-- `A = ε^{−c} z^{−b} h` with `h ∈ F[[ε]][u][[z]]`, which is the form of an element of
`S = F[[ε]][u][[z]]_{εz}`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64; proof of Lemma 6.14, p.65. -/
def IsZRep (A : ZFrac F τ) (c b : ℕ) (h : ZRing F τ) : Prop :=
  A * algebraMap (ZRing F τ) (ZFrac F τ)
      (PowerSeries.C (MvPolynomial.C PowerSeries.X) ^ c * PowerSeries.X ^ b) =
    algebraMap (ZRing F τ) (ZFrac F τ) h

/-- The coefficient `[z^d]A ∈ F((ε))[u]` of `A = ε^{−c} z^{−b} h`, which is `ε^{−c} h_{d+b}`, and `0` when
`d + b < 0`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), proof of Lemma 6.14, pp.65–66. -/
noncomputable def zCoeffOf (c b : ℕ) (h : ZRing F τ) (d : ℤ) : MvPolynomial τ (LaurentSeries F) :=
  if 0 ≤ d + b then
    MvPolynomial.C ((epsK F ^ c)⁻¹) *
      map (algebraMap F⟦X⟧ (LaurentSeries F)) (PowerSeries.coeff (d + b).toNat h)
  else 0

/-- The coefficient `[ε^v]p ∈ F[u]` of `p ∈ F[[ε]][u]`. -/
noncomputable def epsCoeff (v : ℕ) (p : MvPolynomial τ F⟦X⟧) : MvPolynomial τ F :=
  ∑ m ∈ p.support, monomial m (PowerSeries.coeff v (coeff m p))

/-- `G = tc(lim Ã)`, for nonzero `A`, where `Ã` is the normalization of `A` in `ε`:
`tc(lim Ã) = [z^{b′}][ε^a]A` with `a = val_ε(A)` and `b′ = val_z(lim Ã)`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.2, p.65; Definition 2.5, p.29; Definition 4.1, p.38.

**Formalization Note** Defined through coefficients of a representation `A = ε^{−c} z^{−b} h`. Then `w` is the least
power of `ε` in any coefficient of `h`, so `a = w − c`, and `j₀` the least index with `[ε^w]h_j ≠ 0`, so
`b′ = j₀ − b`. Both are unchanged when the representation changes. -/
def IsTrailingLimit (A : ZFrac F τ) (G : MvPolynomial τ F) : Prop :=
  ∃ (c b : ℕ) (h : ZRing F τ) (w j₀ : ℕ), IsZRep A c b h ∧
    (∀ j v, v < w → epsCoeff v (PowerSeries.coeff j h) = 0) ∧
    (∀ j, j < j₀ → epsCoeff w (PowerSeries.coeff j h) = 0) ∧
    epsCoeff w (PowerSeries.coeff j₀ h) = G ∧ G ≠ 0

end

end BorderD4


