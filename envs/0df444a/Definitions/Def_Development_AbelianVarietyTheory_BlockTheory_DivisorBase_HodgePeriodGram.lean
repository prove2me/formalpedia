-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:25.224474+00:00
-- url     : https://prove2.me/theorems/c45c43f7-110b-4080-90a5-f2b20c0c24ab
-- title:
--   Hodge Period Gram
-- statement:
--   Definitions and structural lemmas for Hodge Period Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
def polydisc (n : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | ∀ k, ‖z k‖ < ρ}
def punctured (ha : a ≤ n) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {z | z ∈ polydisc n ρ ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
def tlog (w : ℂ) : ℝ := -Real.log ‖w‖ / (2 * Real.pi)
structure IsPeriodChart (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Prop where

  rk_le : rk ≤ g

  holo : ∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (polydisc n 1)

  symm : ∀ z ∈ polydisc n 1, (τ₀ z).IsSymm

  psd : ∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef

  supp : ∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0

  toric : (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix
    (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef

  abelian : ∀ z ∈ polydisc n 1, (((τ₀ z).map Complex.im).submatrix
    (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef
def period (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (z : Fin n → ℂ) (L : Fin a → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ₀ z + ∑ i, (L i / (2 * Real.pi * I)) • (B i).map (Int.cast : ℤ → ℂ)
def imPeriod (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ₀ z).map Complex.im + ∑ i, tlog (z (Fin.castLE ha i)) • (B i).map (Int.cast : ℤ → ℝ)
def hodgeGram (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (imPeriod ha τ₀ B z).map Complex.ofReal
def poincareGram (a : ℕ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun k =>
    ((if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2 : ℝ) : ℂ)
def BoundsOn (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ρ c C : ℝ) : Prop :=
  (∀ z ∈ punctured ha ρ, (imPeriod ha τ₀ B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) ∧
  (∀ z ∈ punctured ha ρ,
    ((C * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ)
      - imPeriod ha τ₀ B z).PosSemidef) ∧
  OneFormBound (punctured ha ρ) (fun _ => 1) (poincareGram a) (conn (hodgeGram ha τ₀ B)) C ∧
  TwoFormBound (punctured ha ρ) (hodgeGram ha τ₀ B) (poincareGram a) (curv (hodgeGram ha τ₀ B)) C
def HodgeChartBounds : Prop :=
  ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B →
    ∃ ρ c C : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < c ∧ BoundsOn ha τ₀ B ρ c C
end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram


