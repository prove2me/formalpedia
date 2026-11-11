-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
-- name    : OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:20:41.037945+00:00
-- url     : https://prove2.me/theorems/a7205eda-45b7-433c-a3c0-61e756883952
-- title:
--   Mobius Euler Correction
-- statement:
--   Definitions and structural lemmas for Mobius Euler Correction, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/MobiusEulerCorrection.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_CanonicalRowCompletion_primeValueHom_prime

set_option autoImplicit false
namespace OAI
noncomputable section
namespace SmoothMobiusCorrection
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
open scoped BigOperators Classical
section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)
abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}
def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val
def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)
def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I
end
section
open ActualEisensteinCubic
open Filter
def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)
def primeCharacterTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  χ (Ideal.absNorm P.val) * primeNormPower P s
def primeDensity (P : PrimeIdeal) : ℂ := 1-(1:ℂ)/(Ideal.absNorm P.val:ℂ)
def correctionTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) : ℂ :=
  if P.val∈S then 0 else
    -((1:ℂ)/(Ideal.absNorm P.val:ℂ))*primeCharacterTerm χ P s /
      (1-primeDensity P*primeCharacterTerm χ P s)
def eulerCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) : ℂ :=
  ∏' P : PrimeIdeal, (1+correctionTerm χ S P s)
end
section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)
def outsideMask (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if ∀P∈S,¬P∣I then 1 else 0
def ordinaryPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s)
def dampedPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else (1-(1:ℂ)/(Ideal.absNorm I:ℂ))*(χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s))
def ordinarySeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  outsideMask S I * baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I
def dampedSeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ordinarySeriesTerm χ S s I * SixthPowerAverage.totientDensity I
end
open ActualEisensteinCubic
open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
end SmoothMobiusCorrection
end
end OAI


