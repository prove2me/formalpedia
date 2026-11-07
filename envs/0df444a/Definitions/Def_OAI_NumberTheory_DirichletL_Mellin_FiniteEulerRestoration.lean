-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
-- name    : OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:17:07.626354+00:00
-- url     : https://prove2.me/theorems/6f0d21e2-688e-40d8-801e-e98993b40db6
-- title:
--   Finite Euler Restoration
-- statement:
--   Definitions and structural lemmas for Finite Euler Restoration, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
namespace FiniteEulerRestoration
end FiniteEulerRestoration
namespace FiniteSFactor
noncomputable def outsideExpSum (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, outsideCoeff S w n * Real.exp (-(n : ℝ) * t)
end FiniteSFactor
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace CompactMellinBridge
structure BaseChangeCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  W : ℝ → ℂ
  F : ℝ → ℂ
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  sum_eq : ∀ t : ℝ, 0 < t →
    HasSum (fun n : ℕ =>
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)) (F t)
  term_integrable : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)))
      (Set.Ioi 0)
  fubini : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
    ∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t))‖)
  locally_integrable : LocallyIntegrableOn
    (fun D : ℝ => F D⁻¹) (Set.Ioi 0)
  power_bound : (fun D : ℝ => F D⁻¹) =O[atTop]
    (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0
end CompactMellinBridge
end
end OAI


