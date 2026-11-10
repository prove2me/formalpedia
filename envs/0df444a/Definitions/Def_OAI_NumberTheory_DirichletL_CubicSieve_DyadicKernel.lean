-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T12:49:43.860686+00:00
-- url     : https://prove2.me/theorems/9bd04b2b-220f-4d1c-bb9f-b3984d7f22f3
-- title:
--   Dyadic Kernel
-- statement:
--   Definitions and structural lemmas for Dyadic Kernel, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DyadicKernel.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
def reopenedCanonicalRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z:O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f H S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic
def completedDualScale (X r C K U B : ℝ) (D E : Ideal O) : ℝ :=
  r^3*(Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)^3*U*B^3*X/(K^2*C^2)
end CompletedGauss
open scoped BigOperators
namespace CompletedDyadic
def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m
def normMajorant (deltaLoss A K t r H U B : ℝ) : ℝ :=
  K^deltaLoss/(r*Real.sqrt H)*
    (Real.sqrt K*B^(deltaLoss-1/2)*U^deltaLoss+B^deltaLoss*U^(deltaLoss+1/2))/(1+t*r^3*B^3*U)^A
def tripleTerm (t s A β ρ q : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  (ramifiedScale ρ q i.1)⁻¹*((2:ℝ)^i.2.1)^β*
    kernelTerm (t*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3) s A i.2.2
end CompletedDyadic
namespace CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
def completedSmoothDyadicBlock (V₀ V₁ V₂ W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  ∑n∈S i,∑v∈T i,quadraticRow k.val (primaryGenerator (n*v))*β i n v*
    (V₀ (Real.log ((Ideal.absNorm k.val:ℝ)/K))*
      V₁ (Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2))*
      V₂ (Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
          Real.exp (-2*Real.log ((Ideal.absNorm k.val:ℝ)/K)+
            Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
              3*Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))))
end CompletedGauss
end
end OAI


