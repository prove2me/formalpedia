-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_VerticalContourShift
-- name    : OAI_NumberTheory_DirichletL_Mellin_VerticalContourShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T21:21:34.924888+00:00
-- url     : https://prove2.me/theorems/9bc9782d-071b-438c-b6cd-39423bb89e29
-- title:
--   Vertical Contour Shift
-- statement:
--   Definitions and structural lemmas for Vertical Contour Shift, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
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
namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology
def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)
end VerticalContourShift
namespace GaussianMoment
end GaussianMoment
namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology
end VerticalContourShift
namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding
end CubicGammaExponential
open Filter MeasureTheory
open scoped Classical BigOperators Topology
namespace CubicEisenstein
end CubicEisenstein
open Filter MeasureTheory
open scoped Classical BigOperators Topology
namespace CubicEisenstein
def radialBesselProfile {α : Type*} (r : α→ℝ) (a : α→ℂ) (q v : ℝ) : ℂ :=
  ∑'i,(a i*(r i:ℂ))*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*q*Real.sqrt (r i)*v)
end CubicEisenstein
end
end OAI


