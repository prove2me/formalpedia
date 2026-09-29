-- Prove2me | Definitions.Def_KN_TruncatedHorizontalCoefficientsV2
-- name    : KN_TruncatedHorizontalCoefficientsV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:19:04.429912+00:00
-- url     : https://prove2.me/theorems/1e4e830e-baad-42f7-91d7-6be4cb3f6e23
-- title:
--   Truncated horizontal coefficients over rebased propagation data
-- statement:
--   Truncated finite-level horizontal coefficient constructions rebuilt over the rebased prime-power propagation definitions.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Reduce every coordinate of a finite horizontal quotient modulo `p ^ m`. -/
def truncateHorizontalCoordinates {p : ℕ} {e : ℕ → ℕ} (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    HorizontalFiniteGroup p e A → HorizontalFiniteGroup p (fun _ ↦ m) A :=
  fun x i ↦ Multiplicative.ofAdd
    (ZMod.castHom (pow_dvd_pow p (he i.1)) (ZMod (p ^ m)) (x i).toAdd)

/-- The finite-level coefficients after reducing every coordinate modulo `p ^ m`.
Coefficients in the same fibre are added in the original coefficient ring. -/
def HorizontalMeasure.truncatedFiniteLevel {R : Type*} [CommRing R]
    {p : ℕ} {e : ℕ → ℕ} (μ : HorizontalMeasure R p e) (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    HorizontalGroupRing R p (fun _ ↦ m) A :=
  Finsupp.mapDomain (truncateHorizontalCoordinates m he A) (μ.finiteLevel A)

end HorizontalPadicL


