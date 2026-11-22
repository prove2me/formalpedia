-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:15.685856+00:00
-- url     : https://prove2.me/theorems/b907edc3-57cb-41dd-a68a-e3e55e503d59
-- title:
--   Antitone Of Mem Gt Box
-- statement:
--   Definitions and structural lemmas for Antitone Of Mem Gt Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
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
namespace Pieri
open Classical in

def sLe {n : ℕ} (κ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (κ i) (κ i + b)).filter fun l =>
    (∀ m, κ m ≤ l m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) ∧
      ∑ m, l m - ∑ m, κ m ≤ (b : ℤ)
def Lo {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  fun j => max (μ j) ((Fin.snoc l (μ (Fin.last n)) : Fin (n + 1) → ℤ) j)
def Hi {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) : Fin n → ℤ :=
  fun i => min (μ i.castSucc) (l i)
def fw {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (ν : Fin (n + 1) → ℤ) : Fin n → ℤ :=
  fun i => Lo μ l i.succ + Hi μ l i - ν i.succ
def bw {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (b : ℕ) (κ : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cons (Lo μ l 0 + b - (∑ i, l i - ∑ i, κ i)) (fun i => Lo μ l i.succ + Hi μ l i - κ i)
def star {n : ℕ} (μ : Fin n → ℤ) : Fin n → ℤ := fun i => -μ (Fin.rev i)
end Pieri
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


