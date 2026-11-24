-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:49.078433+00:00
-- url     : https://prove2.me/theorems/b8058320-cbe6-4225-8eee-27fdca95ff4c
-- title:
--   Zarhin Bundle Kernel First Coord Equations
-- statement:
--   Definitions and structural lemmas for Zarhin Bundle Kernel First Coord Equations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.CompanionTheory.Ar
namespace ProjCoord
section OpenImm
variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩
end OpenImm
section Chart
variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]
end Chart
section Away
open HomogeneousLocalization
variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]
def awayEval (ψ : A →+* Ω) (f : A) (hf : ψ f ≠ 0) : Away 𝒜 f →+* Ω :=
  (Localization.awayLift ψ f (IsUnit.mk0 _ hf)).comp (algebraMap (Away 𝒜 f) (Localization.Away f))
end Away
section Poly
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
theorem X_mem (c : κ) : (X c : MvPolynomial κ o) ∈ homogeneousSubmodule κ o 1 := isHomogeneous_X o c
def chartEval (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    Away (homogeneousSubmodule κ o) (X c : MvPolynomial κ o) →+* Ω :=
  awayEval (homogeneousSubmodule κ o) (aeval x : MvPolynomial κ o →ₐ[o] Ω).toRingHom (X c) (by simpa using hc)
end Poly
end ProjCoord
attribute [local instance] MvPolynomial.gradedAlgebra
end GlobalTheory.CompanionTheory.Ar


