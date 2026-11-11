-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
-- name    : OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:48:34.300493+00:00
-- url     : https://prove2.me/theorems/8961670f-0184-4d56-a73e-be7180624090
-- title:
--   Completed Energy
-- statement:
--   Definitions and structural lemmas for Completed Energy, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/CompletedEnergy.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_coprime
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)
def outsideLogEnergy (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ→ℂ) (X K : ℝ) : ℝ :=
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) Finset.univ Ψ m labels V X K
def HasCanonicalThetaModels (S : Finset (Ideal ActualEisensteinCubic.O)) (base : ActualEisensteinCubic.O→*ℂ)
    (ρ q levelBound : ℝ) : Prop :=
  ∀(A : ℝ),0≤A → ∀(W : ℝ→ℂ),
    Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
    ∀κ : ℝ,0<κ → ∃C : ℝ,0≤C ∧
    ∀(Z K X F θ : ℝ),1≤Z → 1≤K → 0<X → 1≤F → F≤Z^((1:ℝ)/1000) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),IsBaseRayTwist base Ψ → ∀m : ActualEisensteinCubic.O,m≠0 →
    let G : Ideal ActualEisensteinCubic.O:=Ideal.span {m*excludedGenerator S}
    (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∃(rays : ℕ) (lengthScale : ℂ),(rays:ℝ)^2*‖lengthScale‖^2≤C*Z^κ ∧
      ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays
          (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ)
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale
end CanonicalRowCompletion
open scoped BigOperators Classical
namespace CompletedGauss
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
def fractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val * eisEmbedding lambda^((m:ℤ)-4) * eisEmbedding n * eisEmbedding b^3
end
section
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)
def normalizedThetaAmplitude (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  normalizedCuspAmplitude (d (fractionalThetaPoint u m n b)) ((m:ℝ)-4) (‖eisEmbedding b‖^2) *
    (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ)) *
    vartheta (u.val*lambda^m*(n*b^3))
end
open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)
def paperLambda : ActualEisensteinCubic.O := 1+2*omega
def paperLambdaUnit : ActualEisensteinCubic.Oˣ where
  val := -omega
  inv := -omega^2
  val_inv := by
    calc
      (-omega)*(-omega^2)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
  inv_val := by
    calc
      (-omega^2)*(-omega)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
def paperFractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val*eisEmbedding paperLambda^((m:ℤ)-4)*eisEmbedding n*eisEmbedding b^3
def paperUnitReindex (m : ℕ) : ActualEisensteinCubic.Oˣ ≃ ActualEisensteinCubic.Oˣ := Equiv.mulRight (paperLambdaUnit^(m+2))
end CompletedGauss
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalCubeSeparation
end CanonicalCubeSeparation
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)
end CanonicalRowCompletion
namespace CanonicalCubeSeparation
def radiusIter (A : ℝ) : ℕ→ℝ
  | 0=>A
  | n+1=>radiusIter (2*A+11) n
end CanonicalCubeSeparation
open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisTraceModChar finite_quotient_span)
open FiniteGaussPhase hiding O
def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)
end QuadraticAllOddCRT
end
end OAI


