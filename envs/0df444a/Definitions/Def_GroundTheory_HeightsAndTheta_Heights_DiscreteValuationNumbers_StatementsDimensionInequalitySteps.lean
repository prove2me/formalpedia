-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:47.78252+00:00
-- url     : https://prove2.me/theorems/304fc68a-8b94-4dbf-ab9b-27309fe4a86c
-- title:
--   Statements Dimension Inequality Steps
-- statement:
--   Definitions and structural lemmas for Statements Dimension Inequality Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsDimensionInequalitySteps.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u v
open Polynomial
def PolynomialPrimeOverZeroHeight.Statement : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] (Q : Ideal D[X]) [Q.IsPrime],
    Q.comap (C : D →+* D[X]) = ⊥ → Q.height ≤ 1
def QuotientHeightAddOne.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (I : Ideal R), I ≠ ⊥ →
    ∀ (P : Ideal (R ⧸ I)) [P.IsPrime], P.height + 1 ≤ (P.comap (Ideal.Quotient.mk I)).height
def PolynomialDimensionInequality.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (P : Ideal A[X]) [P.IsPrime],
    Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P) ≤
      Cardinal.ofENat (P.under A).height + 1
def DimensionInequalityOneGenerator.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (x : B), Algebra.adjoin A {x} = ⊤ → Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B
end GroundTheory.Heights₂.Heights.NumbersDVR


