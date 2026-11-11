-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselDerivatives
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_BesselDerivatives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:41:49.13131+00:00
-- url     : https://prove2.me/theorems/aba8fc64-c774-4ab2-87cf-89e81948c782
-- title:
--   Bessel Derivatives
-- statement:
--   Definitions and structural lemmas for Bessel Derivatives, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/BesselDerivatives.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
def cubicBesselDensityDeriv (x t : ℝ) : ℝ := -(x/(2*t))*cubicBesselDensity x t
def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)+
    (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)
def schlafliBesselK_cubic_derivative (x : ℝ) : ℂ := (cubicBesselRealDeriv x:ℂ)
def cubicBesselDerivativeUpper (delta : ℝ) : ℝ :=
  ((1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)+
    (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*(4/delta))*
      ((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))
end
section
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
def primeExpansionTerm (p:Eis) (s:ℂ) (h:Eis) (k:ℕ):ℂ:=
  ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*cubicUnitGaussSum h (p^k)*
    unramifiedPrimeDeletedSeries p s (h*p^k)
end
section
open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
end
section
open scoped BigOperators Classical Topology
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate
def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℂ×ℝ :=
  (-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)),
    v/(‖c‖^2*(v^2+t^2*‖direction‖^2)))
end CubicEisenstein
end
end OAI


