-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_HilbertSeries
-- name    : DetSupportRank_DeterminantSupport_HilbertSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:15.776761+00:00
-- url     : https://prove2.me/theorems/b184139d-f11c-48c1-808a-808535e3ba43
-- title:
--   Positive Hilbert series and Hilbert numerators
-- statement:
--   For a nonnegatively graded finitely generated module over a positively multigraded polynomial ring, define
--   $$H_M(t)=\sum_{u\in\mathbb N^d}\dim_F(M_u)t^u,\qquad K_M^S(t)=H_M(t)\prod_j(1-t^{p_j}).$$
--   The series is a formal power series. The positive K-polynomial is selected by this defining series identity when a polynomial exists and is zero otherwise. The supporting agreement target proves finite-dimensionality of every piece, polynomiality, and equality with the resolution-defined Laurent polynomial under precisely the positive, nonnegative source assumptions.
--
--   The auxiliary total definitions are never used to infer facts from infinite-dimensional components or from an unproved existence hypothesis.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Definitions 5.4 and 5.6, pp.18–19, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_KPolynomials

noncomputable section
open scoped BigOperators
universe uDSHilbert

namespace DetSupportRank.DeterminantSupport

/-- Definition 5.4, on the nonnegative, positive-weight, finitely generated domain.
No infinite-dimensional component is used in any Hilbert-series theorem. -/
def hilbertSeries {K : Type uDSHilbert} [Field K] {V : Type} {d : ℕ}
    (M : GradedModuleData K V (Fin d)) : MvPowerSeries (Fin d) ℤ :=
  fun e => (Module.finrank K (M.piece (fun i => (e i : ℤ))) : ℤ)

/-- Definition 5.6 as a formal series; polynomiality is a mathematical theorem. -/
def hilbertNumerator {K : Type uDSHilbert} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℕ) (M : GradedModuleData K (Fin m) (Fin d)) :
    MvPowerSeries (Fin d) ℤ :=
  hilbertSeries M * ∏ j, (1 - (MvPolynomial.monomial
    (Finsupp.equivFunOnFinite.symm (p j)) (1 : ℤ) : MvPowerSeries (Fin d) ℤ))

/-- The positive-domain K-polynomial selected by its defining Hilbert-series identity.
Polynomiality and agreement with the resolution definition are not assumed. -/
def positiveKPolynomial {K : Type uDSHilbert} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℕ) (M : GradedModuleData K (Fin m) (Fin d)) :
    MvPolynomial (Fin d) ℤ := by
  classical
  exact if h : ∃ Q : MvPolynomial (Fin d) ℤ, (Q : MvPowerSeries (Fin d) ℤ) =
      hilbertNumerator p M then Classical.choose h else 0

end DetSupportRank.DeterminantSupport


