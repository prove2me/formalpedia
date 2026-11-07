-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
-- name    : QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:31:34.853422+00:00
-- url     : https://prove2.me/theorems/bf764d75-a071-4d81-b1d9-b9d7944fdcf3
-- title:
--   FPS
-- statement:
--   Definitions and structural lemmas for FPS, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
section Finite
variable {R : Type*} [CommRing R]
def qPochhammer (a : R⟦X⟧) (n : ℕ) : R⟦X⟧ :=
  ∏ k ∈ range n, (1 - a * X ^ k)
end Finite
section Stabilisation
variable {R : Type*} [CommRing R]
end Stabilisation
section Infinite
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
def qPochhammerInf (a : R⟦X⟧) : R⟦X⟧ :=
  ∏' k : ℕ, (1 - a * X ^ k)
end Infinite
section JTP
local notation "A" => LaurentPolynomial ℚ
scoped instance instTopologicalSpaceLaurentPolyComplex : TopologicalSpace A := ⊥
scoped instance instDiscreteTopologyLaurentPolyComplex : DiscreteTopology A := ⟨rfl⟩
local notation "PS" => (PowerSeries.C : A →+* A⟦X⟧)
abbrev laurentZ : A⟦X⟧ := PS (LaurentPolynomial.T 1)
abbrev laurentZInv : A⟦X⟧ := PS (LaurentPolynomial.T (-1))
def qPochhammerInfX : A⟦X⟧ := qPochhammerInf X
def qPochhammerInfNegZ : A⟦X⟧ := qPochhammerInf (-laurentZ)
def qPochhammerInfNegXMulZInv : A⟦X⟧ := qPochhammerInf (-X * laurentZInv)
def jacobiProd : A⟦X⟧ := qPochhammerInfX * qPochhammerInfNegZ * qPochhammerInfNegXMulZInv
def jacobiBilateral : A⟦X⟧ :=
  (∑' n : ℕ, PS (LaurentPolynomial.T (n : ℤ)) * X ^ n.choose 2) +
  (∑' m : ℕ, PS (LaurentPolynomial.T (-(↑m + 1))) * X ^ (m + 2).choose 2)
end JTP
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
end


