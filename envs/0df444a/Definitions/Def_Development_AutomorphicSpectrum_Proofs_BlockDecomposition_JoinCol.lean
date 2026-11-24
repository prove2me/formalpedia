-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:31.698057+00:00
-- url     : https://prove2.me/theorems/34d2d0ca-5474-40da-a548-df3386ab6325
-- title:
--   Join Col
-- statement:
--   Definitions and structural lemmas for Join Col, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JoinCol.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace GlobalTheory.CompanionTheory.FSCrofton
def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))
def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)
def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2
def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩
end GlobalTheory.CompanionTheory.FSCrofton


