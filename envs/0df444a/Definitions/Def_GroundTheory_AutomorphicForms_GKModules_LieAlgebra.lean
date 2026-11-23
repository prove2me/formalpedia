-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
-- name    : GroundTheory_AutomorphicForms_GKModules_LieAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:49.982636+00:00
-- url     : https://prove2.me/theorems/60932c59-f6dc-4290-85af-dc10cbbd7caf
-- title:
--   Lie Algebra
-- statement:
--   Definitions and structural lemmas for Lie Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
theorem exp_units_conj_real (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹ := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact exp_units_conj y x
theorem coe_inv_val (g : G) : (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) = ↑((g : 𝔸ˣ)⁻¹) := rfl
variable (h : IsExpLieAlgebra G 𝔤)
include h
theorem isClosed_lie : IsClosed (𝔤 : Set 𝔸) := 𝔤.closed_of_finiteDimensional
theorem conj_mem (g : G) {Y : 𝔸} (hY : Y ∈ 𝔤) :
    ((g : 𝔸ˣ) : 𝔸) * Y * (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) ∈ 𝔤 := by
  set Z := ((g : 𝔸ˣ) : 𝔸) * Y * (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) with hZ
  have ht : Tendsto (fun s : ℝ => s • Z) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => s • Z) (𝓝 0) (𝓝 ((0 : ℝ) • Z)) := tendsto_id.smul_const Z
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hs0⟩ :=
    ((ht.eventually_mem (h.isOpen_nhd.mem_nhds h.zero_mem_nhd)).and self_mem_nhdsWithin).exists
  have hG : expUnit ℝ 𝔸 (s • Z) ∈ G := by
    have he : expUnit ℝ 𝔸 (s • Z) = (g : 𝔸ˣ) * expUnit ℝ 𝔸 (s • Y) * (g : 𝔸ˣ)⁻¹ := by
      apply Units.ext
      simp only [coe_expUnit, Units.val_mul, hZ, coe_inv_val]
      rw [← exp_units_conj_real, mul_smul_comm, smul_mul_assoc]
    rw [he]
    exact G.mul_mem (G.mul_mem g.2 (h.expUnit_mem _ (𝔤.smul_mem s hY))) (G.inv_mem g.2)
  have := 𝔤.smul_mem s⁻¹ (h.mem_of_mem_nhd hs hG)
  rwa [smul_smul, inv_mul_cancel₀ (show s ≠ 0 from hs0), one_smul] at this
theorem lie_mem {X Y : 𝔸} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) : ⁅X, Y⁆ ∈ 𝔤 := by
  let c : ℝ → 𝔸 := fun t => exp (t • X) * Y * exp (t • (-X))
  have hc : ∀ t : ℝ, c t ∈ 𝔤 := by
    intro t
    have e : c t = ((h.expG ⟨t • X, 𝔤.smul_mem t hX⟩ : 𝔸ˣ) : 𝔸) * Y *
        ((((h.expG ⟨t • X, 𝔤.smul_mem t hX⟩)⁻¹ : G) : 𝔸ˣ) : 𝔸) := by
      show exp (t • X) * Y * exp (t • -X) = exp (t • X) * Y * ↑((expUnit ℝ 𝔸 (t • X))⁻¹)
      rw [coe_expUnit_inv, smul_neg]
    rw [e]
    exact h.conj_mem _ hY
  have hd : HasDerivAt c (X * Y - Y * X) 0 := by
    have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ))
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg, ← sub_eq_add_neg] at h1
    exact h1
  have hlim := hasDerivAt_iff_tendsto_slope.1 hd
  rw [Ring.lie_def]
  refine h.isClosed_lie.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact 𝔤.smul_mem _ (𝔤.sub_mem (hc t) (hc 0))
def lieSubalgebra : LieSubalgebra ℝ 𝔸 :=
  { 𝔤 with lie_mem' := fun hX hY => h.lie_mem hX hY }
@[simp] theorem lieSubalgebra_toSubmodule : h.lieSubalgebra.toSubmodule = 𝔤 := rfl
@[simp] theorem mem_lieSubalgebra {X : 𝔸} : X ∈ h.lieSubalgebra ↔ X ∈ 𝔤 := Iff.rfl
noncomputable def Ad (g : G) : 𝔤 →ₗ[ℝ] 𝔤 where
  toFun X := ⟨((g : 𝔸ˣ) : 𝔸) * X * (((g⁻¹ : G) : 𝔸ˣ) : 𝔸), h.conj_mem g X.2⟩
  map_add' X Y := by ext; simp [mul_add, add_mul]
  map_smul' r X := by ext; simp
def bracket (X Y : 𝔤) : 𝔤 := ⟨⁅(X : 𝔸), (Y : 𝔸)⁆, h.lie_mem X.2 Y.2⟩
noncomputable def AdL (g : G) : 𝔤 →L[ℝ] 𝔤 := LinearMap.toContinuousLinearMap (h.Ad g)
end IsExpLieAlgebra
end GroundTheory.Automorphic


