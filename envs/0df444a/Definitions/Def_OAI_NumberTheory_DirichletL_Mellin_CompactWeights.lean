-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
-- name    : OAI_NumberTheory_DirichletL_Mellin_CompactWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:52:11.084205+00:00
-- url     : https://prove2.me/theorems/81fbf702-1698-4bda-a72a-d912169d265f
-- title:
--   Compact Weights
-- statement:
--   Definitions and structural lemmas for Compact Weights, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
namespace CompactScaleBridge
section
open ConcretePrimeRowBridge ShortDraftHeckeBridge FiniteSFactor
end
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
end CompactScaleBridge
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ConcreteCompactWeight
noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
noncomputable def bump (y : ℝ) : ℝ := bumpData y
noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)
noncomputable def weight (ρ : ℂ) (y : ℝ) : ℂ :=
  (bump y : ℂ) * Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))
noncomputable def weightedBump (y : ℝ) : ℝ :=
  bump y / positiveExtension y
end ConcreteCompactWeight
namespace CompactScaleBridge
section
open ConcreteCompactWeight
end
end CompactScaleBridge
namespace ActualEisensteinCubic
open ShortDraftCusp
end ActualEisensteinCubic
namespace TwoPassProfiles
def firstCoeff : Fin 9 → ℝ
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -2 | 4 => -1
  | 5 => -2 | 6 => -1 | 7 => -1 | 8 => -1
noncomputable def firstLogs (K y d f E t c x₁ x₂ : ℝ) : Fin 9 → ℝ
  | 0 => Real.log K | 1 => Real.log y | 2 => Real.log d
  | 3 => Real.log f | 4 => Real.log E | 5 => Real.log t
  | 6 => Real.log c | 7 => Real.log x₁ | 8 => Real.log x₂
def secondCoeff : Fin 7 → ℝ
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -2
  | 4 => -2 | 5 => -1 | 6 => -1
noncomputable def secondLogs (Y k d e v n₁ n₂ : ℝ) : Fin 7 → ℝ
  | 0 => Real.log Y | 1 => Real.log k | 2 => Real.log d
  | 3 => Real.log e | 4 => Real.log v
  | 5 => Real.log n₁ | 6 => Real.log n₂
end TwoPassProfiles
end
end OAI


