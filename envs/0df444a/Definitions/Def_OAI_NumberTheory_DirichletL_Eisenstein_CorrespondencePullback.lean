-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:06:45.923482+00:00
-- url     : https://prove2.me/theorems/30eaf3f5-9fbc-4664-aaea-1ae5947b63e9
-- title:
--   Correspondence Pullback
-- statement:
--   Definitions and structural lemmas for Correspondence Pullback, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondencePullback.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_le_levelThree

set_option autoImplicit false
namespace OAI
noncomputable section
namespace CubicEisenstein
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
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
section
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
def kernelCorrespondenceL2 : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (integralCoverTrace hHK globalKubotaKernel_le_levelThree).comp
    ((integralConjugatePullback e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree))
end
def coverEnergyDensity (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x=>(F x).re) p+
    euclideanScalarDirichletDensity (fun x=>(F x).im) p
def coverGradientAt (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j=>(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))
end
section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
end
section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedCuspGaussSeries (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (s:ℂ) : ℂ :=
  (4:ℂ)⁻¹*(unitCuspGaussSeries 1 (ramifiedCuspRoot b) h s+
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑(ramifiedCuspRoot b)⁻¹:Eis))*
      (unitCuspGaussSeries (-(ramifiedCuspRoot b)) (-(ramifiedCuspRoot b)) h s+
        unitCuspGaussSeries (-(ramifiedCuspRoot b)) 1 h s+
          onceCuspGaussSeries (-(ramifiedCuspRoot b)) (ramifiedCuspScaleUnit b) h hf s))
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
local notation "Eis" => ActualEisensteinCubic.O
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open CubicKubota
def sourceArbitraryHeightFamily (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ :=
  (24:ℂ)⁻¹*∑i:RationalBruhatIndex,arbitraryCuspHeightFamily
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq s
def sourceArbitraryHeightFourier (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (24:ℂ)⁻¹ • ∑i:RationalBruhatIndex,arbitraryCuspHeightFourier
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq
end CubicEisenstein
end
end OAI


