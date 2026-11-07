-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
-- name    : OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:08:02.402208+00:00
-- url     : https://prove2.me/theorems/fb083932-cea6-4acd-882f-9ecc603d38d0
-- title:
--   Squarefree Divisors
-- statement:
--   Definitions and structural lemmas for Squarefree Divisors, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
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
namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O
open DescentWeightedCauchy
end SquarefreeDivisorBound
namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology
end VerticalContourShift
open scoped BigOperators Classical
namespace FirstPassCubeLabels
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic
def bit (b : Bool) : ℕ := if b then 1 else 0
def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)
def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val
def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0
def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)
section Rows
variable {ι : Type*} (P : ι → Ideal OAI.FirstPassCubeLabels.O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
include hg
def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  rowCoprimeMask P S a *
    finiteSquarefreeRow P hg S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    finiteSquarefreeRow P hg S a ^ crtExponent side parityBit ε₁ ε₂ *
    finiteSquarefreeRow P hg S a ^ dilationExponent parityBit ε₁ ε₂
end Rows
def parity (m : ℕ) : Bool := decide (m % 2 = 1)
def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂
def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)
section Reassembly
variable {ι κ : Type*} (P : ι → Ideal OAI.FirstPassCubeLabels.O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j
def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j
def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))
def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))
def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))
def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))
def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))
def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))
def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))
end Reassembly
end FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion
def quadraticSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  quadraticRow (fun i => Ideal.span {p i}) hg A (∏ i ∈ B, p i)
end QuadraticInitialBound
end
end OAI


