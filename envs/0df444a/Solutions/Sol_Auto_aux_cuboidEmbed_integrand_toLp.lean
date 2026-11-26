-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_integrand_toLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:10.742699+00:00
-- url     : https://prove2.me/submissions/7dc1e182-21af-4204-8865-839c1716b2ff

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_toLp_translateAxis
public import Theorems.Thm_Auto_aux_liftRaw_toLp

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
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (s : ℝ) :
    (∏ i, aux_liftRaw (aux_cuboidEmbed ε δ i (a i))
        (WithLp.toLp 2 (fun j ↦ (k j : ℝ) + u j) + s • ctCoordinateAxis i)) =
      ∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [← aux_toLp_translateAxis, aux_liftRaw_toLp]
end Auto
