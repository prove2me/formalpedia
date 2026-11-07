-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
-- name    : OAI_NumberTheory_DirichletL_Mellin_CompactScale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:44:38.900207+00:00
-- url     : https://prove2.me/theorems/3a6190f5-a9dd-4843-9a1d-f1cde0a92b53
-- title:
--   Compact Scale
-- statement:
--   Definitions and structural lemmas for Compact Scale, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


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
namespace CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
noncomputable def realCompactOutsideSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∑ I ∈ outsideIdealsUpTo S (2 * Nat.ceil D),
    baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)
structure FixedTestPrimeMSConstants
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε Cmean Ccount : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : Ccount * ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      Cmean * ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)
noncomputable def FixedTestPrimeMSConstants.absorb
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε η Cmean Ccount : ℝ)
    (h : FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (hm : 0 < m) (hCmean : Cmean ≤ ((2 * m : ℕ) : ℝ) ^ η)
    (hCcount : 1 ≤ Ccount * ((2 * m : ℕ) : ℝ) ^ η) :
    FixedTestPrimeMS χ S hSbad W m (ε + η) := by
  let N : ℝ := (2 * m : ℕ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0 < 2 * m)
  have hcount' : N ^ ((11 / 60 : ℝ) - (ε + η)) ≤
      (h.selected.card : ℝ) := by
    calc
      N ^ ((11 / 60 : ℝ) - (ε + η)) =
          1 * N ^ ((11 / 60 : ℝ) - (ε + η)) := by ring
      _ ≤ (Ccount * N ^ η) * N ^ ((11 / 60 : ℝ) - (ε + η)) :=
        mul_le_mul_of_nonneg_right hCcount (Real.rpow_nonneg hNpos.le _)
      _ = Ccount * N ^ ((11 / 60 : ℝ) - ε) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        congr 1
        ring_nf
      _ ≤ _ := h.hcount
  have hmean' :
      (∑ u ∈ rowNormDisk h.H,
        ‖idealRowSum (outsideIdealsUpTo S (2 * m))
            (outsideIdealsUpTo_ne_bot S (2 * m))
            (outsideIdealsUpTo_good S (2 * m) hSbad)
            χ (fixedTestWeight W m) u‖ ^ 2) ≤
        N ^ ((21 / 10 : ℝ) + (ε + η)) := by
    calc
      _ ≤ Cmean * N ^ ((21 / 10 : ℝ) + ε) := h.hmean
      _ ≤ N ^ η * N ^ ((21 / 10 : ℝ) + ε) :=
        mul_le_mul_of_nonneg_right hCmean (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((21 / 10 : ℝ) + (ε + η)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  exact {
    H := h.H
    selected := h.selected
    hp := h.hp
    hprime := h.hprime
    hinj := h.hinj
    hnormlower := h.hnormlower
    hnormupper := h.hnormupper
    hH := h.hH
    hcount := hcount'
    hmean := hmean'
  }
end CompactScaleBridge
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace CompactMellinBridge
noncomputable def finiteEulerFactor
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O)) (s : ℂ) : ℂ :=
  ∏ P ∈ S,
    (1 - χ (Ideal.absNorm P) *
      ((Ideal.absNorm P : ℂ) ^ (-s)))
noncomputable def outsideCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ,
    FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
      W ((n : ℝ) * t)
structure BaseChangeOutsideCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  S : Finset (Ideal FiniteSFactor.O)
  S_prime : ∀ P ∈ S, Prime P
  W : ℝ → ℂ
  sigma : ℝ
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  power_bound :
    (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0
end CompactMellinBridge
end
end OAI


