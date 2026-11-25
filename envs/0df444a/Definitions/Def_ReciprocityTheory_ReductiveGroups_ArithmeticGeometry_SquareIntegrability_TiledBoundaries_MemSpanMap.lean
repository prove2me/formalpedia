-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:41.854849+00:00
-- url     : https://prove2.me/theorems/5c387abc-12bd-4bdd-a630-da4932bb4b1b
-- title:
--   Mem Span Map
-- statement:
--   Definitions and structural lemmas for Mem Span Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanMap.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_pi_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
section PiR
def piR (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim :=
  LinearEquiv.ofBijective (π.restrictScalars ℝ) (pi_bij X hq hπ)
def bP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) := X.b.map (piR X hq hπ).symm
theorem norm_pi (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π) (x : Vsp X.dim) : ‖π x‖ = Real.sqrt q * ‖x‖ := by
  have hn : ∀ v : Vsp X.dim, Hf v v = @inner ℂ _ _ v v := fun v => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have h := hπ.2.2.1 x x
  rw [hn, hn, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖π x‖ ^ 2 = (q : ℝ) * ‖x‖ ^ 2 := by
    have h' : ((‖π x‖ ^ 2 : ℝ) : ℂ) = (((q : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast; exact h
    exact Complex.ofReal_injective h'
  rw [← Real.sqrt_sq (norm_nonneg (π x)), h2, Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq (norm_nonneg x)]
theorem sqrt_q_pos {q : ℕ} (hq : 1 ≤ q) : 0 < Real.sqrt q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
def Ui (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗᵢ[ℝ] Vsp X.dim where
  toLinearEquiv := (piR X hq hπ).trans
    (LinearEquiv.smulOfNeZero ℝ _ (Real.sqrt q)⁻¹ (inv_ne_zero (sqrt_q_pos hq).ne'))
  norm_map' x := by
    show ‖(Real.sqrt q)⁻¹ • π x‖ = ‖x‖
    rw [norm_smul, norm_pi X hπ, Real.norm_eq_abs, abs_inv, abs_of_pos (sqrt_q_pos hq), ← mul_assoc,
      inv_mul_cancel₀ (sqrt_q_pos hq).ne', one_mul]
end PiR
section Q
theorem q_ne {q : ℕ} (hq : 1 ≤ q) : (q : ℝ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by omega)
def bQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) :=
  X.b.map (LinearEquiv.smulOfNeZero ℝ _ (q : ℝ) (q_ne hq)).symm
end Q
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


