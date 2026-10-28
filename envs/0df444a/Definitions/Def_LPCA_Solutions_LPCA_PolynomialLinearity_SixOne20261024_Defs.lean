-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:38.405386+00:00
-- url     : https://prove2.me/theorems/da279e13-9d30-4296-aaf9-d6a22193e72b
-- title:
--   Polynomial Linearity — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for polynomial linearity used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   An additive map respecting constants and each actual polynomial variable
--   respects the complete polynomial action. No replacement action is introduced.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_PolynomialLinearity.lean, selected declarations in lines 14–35; source SHA-256 6b58c267ae9f0eeeafd8a9b9c9ec21651cebf9ae8fe3b97c2a2e7b6abc8be611; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic

set_option autoImplicit false

namespace LPCA

universe u

variable {k W M N : Type u} [CommRing k]
variable [AddCommGroup M] [Module (MvPolynomial W k) M]
variable [AddCommGroup N] [Module (MvPolynomial W k) N]

/-- An additive map respecting constants and each actual polynomial variable
respects the complete polynomial action. No replacement action is introduced. -/
theorem additiveMap_polynomial_smul (f : M →+ N)
    (hC : ∀ c x, f ((MvPolynomial.C c : MvPolynomial W k) • x) =
      (MvPolynomial.C c : MvPolynomial W k) • f x)
    (hX : ∀ j x, f ((MvPolynomial.X j : MvPolynomial W k) • x) =
      (MvPolynomial.X j : MvPolynomial W k) • f x)
    (p : MvPolynomial W k) : ∀ x, f (p • x) = p • f x := by
  refine MvPolynomial.induction_on
    (motive := fun p => ∀ x : M, f (p • x) = p • f x) p hC ?_ ?_
  · intro p q hp hq x
    rw [add_smul, map_add, hp, hq, add_smul]
  · intro p j hp x
    rw [mul_smul, hp, hX, mul_smul]

def polynomialLinearEquivOfGenerators (e : M ≃+ N)
    (hC : ∀ c x, e ((MvPolynomial.C c : MvPolynomial W k) • x) =
      (MvPolynomial.C c : MvPolynomial W k) • e x)
    (hX : ∀ j x, e ((MvPolynomial.X j : MvPolynomial W k) • x) =
      (MvPolynomial.X j : MvPolynomial W k) • e x) : M ≃ₗ[MvPolynomial W k] N where
  __ := e
  map_smul' := additiveMap_polynomial_smul e.toAddMonoidHom hC hX

end LPCA


