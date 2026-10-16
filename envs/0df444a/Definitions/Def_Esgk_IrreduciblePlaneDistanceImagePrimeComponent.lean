-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneDistanceImagePrimeComponent
-- name    : Esgk_IrreduciblePlaneDistanceImagePrimeComponent
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:25.126248+00:00
-- url     : https://prove2.me/theorems/70dec854-5a55-4563-9dfa-0a9c7d5dde49
-- title:
--   Prime component of a normalized distance correspondence
-- statement:
--   This packages a prime ideal component of a two-curve normalized distance correspondence, its contractions to both curve coordinate rings, its distance relations, and its quotient coordinate domain.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]

 
abbrev NormalizedDistancePairAmbient (F : Type*) [Field F] :=
  MvPolynomial (Sum (Fin 2) (Fin 2)) F

 
def firstRename :
    MvPolynomial (Fin 2) F →ₐ[F] NormalizedDistancePairAmbient F :=
  MvPolynomial.rename Sum.inl

 
def secondRename :
    MvPolynomial (Fin 2) F →ₐ[F] NormalizedDistancePairAmbient F :=
  MvPolynomial.rename Sum.inr

 
def normalizedLeftSquaredDistancePolynomial (r : F) :
    MvPolynomial (Fin 2) F :=
  (MvPolynomial.X 0 + MvPolynomial.C r) ^ 2 + MvPolynomial.X 1 ^ 2

 
def normalizedRightSquaredDistancePolynomial (r : F) :
    MvPolynomial (Fin 2) F :=
  (MvPolynomial.X 0 - MvPolynomial.C r) ^ 2 + MvPolynomial.X 1 ^ 2


structure NormalizedDistancePairPrimeComponent
    (C₁ C₂ : IrreduciblePlanePolynomial F) (r₁ r₂ : F) where
  ideal : Ideal (NormalizedDistancePairAmbient F)
  isPrime : ideal.IsPrime
  first_contraction :
    ideal.comap (firstRename (F := F)).toRingHom =
      Ideal.span ({C₁.polynomial} : Set (MvPolynomial (Fin 2) F))
  second_contraction :
    ideal.comap (secondRename (F := F)).toRingHom =
      Ideal.span ({C₂.polynomial} : Set (MvPolynomial (Fin 2) F))
  left_relation :
    firstRename (normalizedLeftSquaredDistancePolynomial r₁) -
        secondRename (normalizedLeftSquaredDistancePolynomial r₂) ∈ ideal
  right_relation :
    firstRename (normalizedRightSquaredDistancePolynomial r₁) -
        secondRename (normalizedRightSquaredDistancePolynomial r₂) ∈ ideal

namespace NormalizedDistancePairPrimeComponent

variable {C₁ C₂ : IrreduciblePlanePolynomial F} {r₁ r₂ : F}

 
abbrev CoordinateRing
    (D : NormalizedDistancePairPrimeComponent C₁ C₂ r₁ r₂) :=
  NormalizedDistancePairAmbient F ⧸ D.ideal

 
instance coordinateRingIsDomain
    (D : NormalizedDistancePairPrimeComponent C₁ C₂ r₁ r₂) :
    IsDomain D.CoordinateRing := by
  letI : D.ideal.IsPrime := D.isPrime
  exact Ideal.Quotient.isDomain D.ideal


end NormalizedDistancePairPrimeComponent


end IrreduciblePlanePolynomial

end Esgk


