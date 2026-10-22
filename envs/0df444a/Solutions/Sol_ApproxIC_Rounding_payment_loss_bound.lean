-- Prove2me | solution 1 for ApproxIC.Rounding.payment_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:36:24.699979+00:00
-- url     : https://prove2.me/submissions/65cf299b-e30b-44ca-b322-6e8ff08a77d5

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

set_option autoImplicit false
open ApproxIC.Rounding

theorem solution (M : Model) (hM : M.Standing) (ε δ : ℝ) (m : Mech)
    (hm : m ∈ Mset M ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (vs : ℝ → ℝ)
    (hvs : ∀ v ∈ Set.Icc 0 M.vbar, vs v ∈ Set.Icc 0 M.vbar ∧
      ∀ w ∈ Set.Icc 0 M.vbar, v * m.x w - (1 - δ) * m.t w ≤ v * m.x (vs v) - (1 - δ) * m.t (vs v)) :
    ∀ v ∈ Set.Icc 0 M.vbar, m.t v - ε / δ ≤ m.t (vs v) := by
  intro v hv
  obtain ⟨hS, hmax⟩ := hvs v hv
  have h1 := hmax v hv
  have h2 := hm.2.2 v hv (vs v) hS
  have hδ0 : 0 < δ := hδ.1
  have key : δ * (m.t v - ε / δ) ≤ δ * m.t (vs v) := by
    have : δ * (ε / δ) = ε := by field_simp
    nlinarith
  exact le_of_mul_le_mul_left key hδ0

