-- Prove2me | solution 1 for Auto.aux_overlap_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:04.307803+00:00
-- url     : https://prove2.me/submissions/fd460fb9-b0e2-4f31-a92c-bdf69ab6006c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} {ε δ : ℝ}
    (hwidth : ε + δ < 1) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (i j : Fin n) (s : ℝ)
    (m₁ m₂ : ℤ)
    (h₁ : ε - u i ≤ s - (m₁ : ℝ) ∧
      s - (m₁ : ℝ) < ε + δ - u i)
    (h₂ : ε - u j ≤ s - (m₂ : ℝ) ∧
      s - (m₂ : ℝ) < ε + δ - u j) :
    m₁ = m₂ := by
  have hupper : ((m₁ - m₂ : ℤ) : ℝ) < 1 := by
    push_cast
    linarith [h₁.1, h₂.2, (hu i).2, (hu j).1]
  have hlower : (-1 : ℝ) < ((m₁ - m₂ : ℤ) : ℝ) := by
    push_cast
    linarith [h₁.2, h₂.1, (hu i).1, (hu j).2]
  have hupperZ : m₁ - m₂ < 1 := by
    exact_mod_cast hupper
  have hlowerZ : (-1 : ℤ) < m₁ - m₂ := by
    exact_mod_cast hlower
  omega
end Auto
