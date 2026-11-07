-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:13:45.597449+00:00
-- url     : https://prove2.me/theorems/cf5d95da-e048-4182-bf46-e196d1bf66fb
-- title:
--   Local Brackets
-- statement:
--   Definitions and structural lemmas for Local Brackets, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LocalBrackets.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
def blockRow {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) : ℂ :=
  finiteSexticRow (fun i : S => Ideal.span {p i.val}) (fun i => hg i.val) (fun i => e i.val) u
def cubeBaseFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) : ℂ :=
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
  gaussBlock p hp hg C e * blockRow p hg C e d * star (blockRow p hg C e h)
def threeGaussRowFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
    (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) *
    (blockRow p hg S e d * star (blockRow p hg S e h))
def cubeTransformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
    quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
    quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
    star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
      FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (d * crtLabel p B v ε₁ ε₂ true) N *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
    (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
      FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (d * crtLabel p B v ε₁ ε₂ false) P *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h))
end FirstPassCubeLabels
section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace LocalLogFourier
end LocalLogFourier
namespace EisensteinSchwartzPoisson
end EisensteinSchwartzPoisson
end
open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets
section
abbrev O := ActualEisensteinCubic.O
variable {F : Type*} [Field F] [Fintype F]
def rootCard (F : Type*) [Fintype F] : ℝ := Real.sqrt (Fintype.card F)
def tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  (rootCard F : ℂ)⁻¹ * gaussSum (χ ^ j) ψ
def bracket (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then
    (rootCard F : ℂ)⁻¹ * (-1 + (Fintype.card F : ℂ) * if x = 0 then 1 else 0)
  else if j = 0 then (rootCard F : ℂ)⁻¹ * (χ ^ 2)⁻¹ x
  else (χ ^ (j + 2))⁻¹ x
def phase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (ε : Fˣ) : ℂ :=
  if j = 4 then tau χ (ψ.mulShift (-1)) 4
  else if j = 0 then -tau χ ψ 2 * (χ ^ 2)⁻¹ ε
  else tau χ (ψ.mulShift (-1)) j * tau χ ψ (j + 2) * (χ ^ (j + 2))⁻¹ ε
end
section
variable {F : Type*} [Field F] [Fintype F]
end
open ActualEisensteinCubic
noncomputable local instance quotientField (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintype (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _
end LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]
def activeRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ h : Fˣ, (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
      (((χ⁻¹) ^ 2) (σ * h)) * ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))
open ActualEisensteinCubic
noncomputable local instance quotientFieldNormalized (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeNormalized (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _
end LocalReflectionBrackets
end
end OAI


