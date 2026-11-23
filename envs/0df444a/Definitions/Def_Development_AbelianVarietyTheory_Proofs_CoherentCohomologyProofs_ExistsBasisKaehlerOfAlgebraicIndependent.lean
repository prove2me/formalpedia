-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:59.921947+00:00
-- url     : https://prove2.me/theorems/9d427b70-a9ef-4ca7-9ca0-42bd34e98552
-- title:
--   Exists Basis Kaehler Of Algebraic Independent
-- statement:
--   Definitions and structural lemmas for Exists Basis Kaehler Of Algebraic Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
section Alternating
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]
end Alternating
section TwoInIdeal
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {p : ℕ}
end TwoInIdeal
section RegForms
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
noncomputable def formMap : (⋀[V]^p Ω[V⁄K]) →ₗ[V] (⋀[F]^p Ω[F⁄K]) :=
  exteriorPowerMapOver F p (KaehlerDifferential.map K K V F)
noncomputable def regForms : Submodule V (⋀[F]^p Ω[F⁄K]) :=
  LinearMap.range (formMap K V F p)
variable {V p}
end RegForms
section LogWedge
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
noncomputable def dlogWedge (S : Finset (Fin p)) (x : Fin p → F) : ⋀[F]^p Ω[F⁄K] :=
  exteriorPower.ιMulti F p (fun k => if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k))
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]
end LogWedge
section Order
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
open Classical in

noncomputable def ordTop_vw (f : F) : WithTop ℤ :=
  if f = 0 then ⊤ else (WithZero.log (Ring.ordFrac V f) : ℤ)
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
noncomputable def fracKaehlerBasis (b : Basis (Fin n) V Ω[V⁄K]) : Basis (Fin n) F Ω[F⁄K] :=
  b.ofIsLocalizedModule F V⁰ (KaehlerDifferential.map K K V F)
noncomputable def topFormGen (b : Basis (Fin n) V Ω[V⁄K]) : ⋀[F]^n Ω[F⁄K] :=
  formMap K V F n (exteriorPower.ιMulti V n b)
noncomputable def topFormCoeff (b : Basis (Fin n) V Ω[V⁄K]) : (⋀[F]^n Ω[F⁄K]) →ₗ[F] F :=
  exteriorPower.alternatingMapLinearEquiv (fracKaehlerBasis F b).det
noncomputable def topFormOrd_vw (b : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]) : WithTop ℤ :=
  ordTop_vw V (topFormCoeff F b ω)
variable {F} (b : Basis (Fin n) V Ω[V⁄K])
end Order
section Existence
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]
end Existence
section Main
end Main
section Example
open Polynomial
variable (K : Type*) [Field K]
end Example
end GlobalTheory


