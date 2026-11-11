-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T21:15:05.974117+00:00
-- url     : https://prove2.me/theorems/06c6dbaa-bfc4-48ab-98fa-7a8312b53e22
-- title:
--   Cusp Dilation
-- statement:
--   Definitions and structural lemmas for Cusp Dilation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
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
open scoped BigOperators Classical
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedTraceLambda : Eis := 1+2*omega
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3
def unitLowerGauss (h : Eis) (u : Eisˣ) (a : Eis) : ℂ :=
  ∑'r:CubicUnitResidue a,
    (eisEmbedding (symbol (u:Eis) (a+3*GaussianShiftedPartition.representative a r.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a r.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a r.val)/eisEmbedding ((u:Eis)*a))
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
def UnitCuspFrequency (h : Eis) (u : Eisˣ) (j : ℕ) : Prop :=
  (3:Eis)∣h*(↑u⁻¹:Eis)+(j:Eis)*ramifiedTraceLambda
def unitCuspArithmeticSeries (s : ℂ) (h : Eis) (u : Eisˣ) : ℂ :=
  ∑'a:PrimaryLower,((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace CubicEisenstein
def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
end CubicEisenstein
open scoped Classical MatrixGroups
namespace CubicKubota
section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
end
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
end CubicKubota
end
end OAI


