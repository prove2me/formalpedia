-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:24.285858+00:00
-- url     : https://prove2.me/theorems/4ab02315-7b40-4326-b54d-9b317fd92385
-- title:
--   Statement P
-- statement:
--   Definitions and structural lemmas for Statement P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/StatementP.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
def gtBox {n : ℕ} (μ : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (μ i.succ) (μ i.castSucc)
def dGT : (n : ℕ) → (Fin n → ℤ) → ℕ
  | 0, _ => 1
  | n + 1, μ => ∑ κ ∈ gtBox μ, dGT n κ
open Classical in

def stripsUp {n : ℕ} (μ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (μ i) (μ i + b)).filter fun ν => HStrip ν μ b
open Classical in

def stripsDown {n : ℕ} (μ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (μ i - b) (μ i)).filter fun ν => HStrip μ ν b
def StripsMem : Prop :=
  ∀ (n : ℕ) (μ ν : Fin n → ℤ) (b : ℕ),
    (ν ∈ stripsUp μ b ↔ HStrip ν μ b) ∧ (ν ∈ stripsDown μ b ↔ HStrip μ ν b)
def GTPieri : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ) (b : ℕ), Antitone μ →
    ∑ ν ∈ stripsUp μ b, dGT n ν = dGT n μ * (n + b - 1).choose b ∧
    ∑ ν ∈ stripsDown μ b, dGT n ν = dGT n μ * (n + b - 1).choose b
def StdCountGT : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ →
    Finite {I : ℤ → Finset (Fin n) // IsStd μ I} ∧ Nat.card {I : ℤ → Finset (Fin n) // IsStd μ I} = dGT n μ
def CountPAll : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), CountP n N isVec B
def ContIdx (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ) : Type :=
  {x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n)) //
    x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2}
def CountCont : Prop :=
  ∀ (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ), i ≤ N → Antitone μ₀ →
    Finite (ContIdx n i N isVec B μ₀) ∧
    Nat.card (ContIdx n i N isVec B μ₀) = dGT n μ₀ * ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


