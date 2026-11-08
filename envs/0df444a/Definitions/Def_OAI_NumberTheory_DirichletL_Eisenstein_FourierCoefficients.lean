-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FourierCoefficients
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_FourierCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:23:31.733625+00:00
-- url     : https://prove2.me/theorems/b2f6578f-0e43-4584-9f8b-e8fd518f428e
-- title:
--   Fourier Coefficients
-- statement:
--   Definitions and structural lemmas for Fourier Coefficients, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FourierCoefficients.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicSpace
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
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
section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT
def cuspFrequency (h : O) : ℂ := eisEmbedding h/(3*eisLam)
end
section
open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT
end
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
def shiftedHeightKernel (v : ℝ) (s b z : ℂ) : ℂ :=
  (v:ℂ)^(-s)*hyperbolicKernel s ((z+b)/(v:ℂ))
end
section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Pointwise
open ActualEisensteinCubic ConcreteTraceCRT
end
section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
def primitiveRowIntegral (v : ℝ) (s freq : ℂ) (c d : O) : ℂ :=
  ∫ z in periodDomain,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z)
def arithmeticResidueSum (h c : O) : ℂ :=
  ∑' r : AdmissibleResidue c,eisEmbedding (symbol c (denominatorRep c r.1))*
    ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)
end
section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
instance : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance
def arithmeticDirichletTerm (s : ℂ) (h : O) (c : LevelLower) : ℂ :=
  if c.1=0 then 0 else ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1
def arithmeticDirichletSeries (s : ℂ) (h : O) : ℂ :=
  ∑' c : LevelLower,arithmeticDirichletTerm s h c
def scatteringCoefficient (s : ℂ) (h : O) : ℂ :=
  arithmeticDirichletSeries s h/((9*Real.sqrt 3/2:ℝ):ℂ)
end
open MeasureTheory Set Filter
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
def eisensteinFourierCoefficient (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) : ℂ :=
  (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))/
    ((9*Real.sqrt 3/2:ℝ):ℂ)
end CubicEisenstein
end
end OAI


