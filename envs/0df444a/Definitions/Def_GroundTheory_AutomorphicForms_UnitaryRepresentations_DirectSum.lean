-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
-- name    : GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:30.502802+00:00
-- url     : https://prove2.me/theorems/d891de59-1cce-489d-b229-bebde8a23706
-- title:
--   Direct Sum
-- statement:
--   Definitions and structural lemmas for Direct Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_continuous_inner_orbit
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_continuous_of_weak
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace UnitaryRep
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
section directSum
variable (ρ : ∀ i, UnitaryRep G (E i))
lemma memℓp_map (g : G) (x : lp E 2) : Memℓp (fun i => ρ i g (x i)) 2 := by
  apply memℓp_norm_iff.mp
  have : (fun i => ‖ρ i g (x i)‖) = fun i => ‖x i‖ := funext fun i => norm_map _ _ _
  rw [this]
  exact memℓp_norm_iff.mpr (lp.memℓp x)
noncomputable def hilbertDirectSumIsometry (g : G) : lp E 2 ≃ₗᵢ[ℂ] lp E 2 where
  toFun x := ⟨fun i => ρ i g (x i), memℓp_map ρ g x⟩
  invFun x := ⟨fun i => ρ i g⁻¹ (x i), memℓp_map ρ g⁻¹ x⟩
  map_add' x y := lp.ext (funext fun i => by simp; rfl)
  map_smul' c x := lp.ext (funext fun i => by simp)
  left_inv x := lp.ext (funext fun i => by simp)
  right_inv x := lp.ext (funext fun i => by simp)
  norm_map' x := by
    have hp : 0 < (2 : ℝ≥0∞).toReal := by simp
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 2
    ext i
    change ‖ρ i g (x i)‖ ^ _ = _
    rw [norm_map]
lemma hilbertDirectSumIsometry_apply (g : G) (x : lp E 2) (i : ι) :
    hilbertDirectSumIsometry ρ g x i = ρ i g (x i) := rfl
noncomputable def directSumHom : G →* (lp E 2 ≃ₗᵢ[ℂ] lp E 2) where
  toFun := hilbertDirectSumIsometry ρ
  map_one' := LinearIsometryEquiv.ext fun x => lp.ext (funext fun i => by
    simp [hilbertDirectSumIsometry_apply])
  map_mul' g h := LinearIsometryEquiv.ext fun x => lp.ext (funext fun i => by
    change ρ i (g * h) (x i) = ρ i g (ρ i h (x i))
    exact map_mul_apply _ g h _)
omit [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] in
lemma summable_norm_mul_norm (x y : lp E 2) : Summable fun i => ‖x i‖ * ‖y i‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by simp
  have hx := (lp.memℓp x).summable hp
  have hy := (lp.memℓp y).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i => ?_) (hx.add hy)
  nlinarith [sq_nonneg (‖x i‖ - ‖y i‖), norm_nonneg (x i), norm_nonneg (y i)]
noncomputable def directSum : UnitaryRep G (lp E 2) where
  toHom := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := lp E 2)).symm.toMonoidHom.comp
    (directSumHom ρ)
  continuous_orbit' := continuous_of_weak _ fun x y => by
    have e : ∀ g, ⟪(((Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := lp E 2)).symm.toMonoidHom.comp
        (directSumHom ρ) g : unitary (lp E 2 →L[ℂ] lp E 2)) : lp E 2 →L[ℂ] lp E 2) x, y⟫_ℂ =
        ∑' i, ⟪ρ i g (x i), y i⟫_ℂ := fun g => by
      rw [lp.inner_eq_tsum]
      rfl
    simp_rw [e]
    refine continuous_tsum (fun i => (ρ i).continuous_inner_orbit (x i) (y i))
      (summable_norm_mul_norm x y) (fun i g => ?_)
    calc ‖⟪ρ i g (x i), y i⟫_ℂ‖ ≤ ‖ρ i g (x i)‖ * ‖y i‖ := norm_inner_le_norm _ _
      _ = ‖x i‖ * ‖y i‖ := by rw [norm_map]
noncomputable def singleL [DecidableEq ι] (i : ι) : E i →L[ℂ] lp E 2 :=
  LinearMap.mkContinuous (lp.lsingle 2 i) 1 fun a => by
    rw [one_mul, lp.lsingle_apply]
    exact (lp.norm_single (by norm_num) i a).le
end directSum
noncomputable def equivDirectSumOfIsHilbertSum {π : UnitaryRep G H} {V : ι → Submodule ℂ H}
    [∀ i, CompleteSpace (V i)] (hinv : ∀ i, π.IsInvariant (V i))
    (hV : IsHilbertSum ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    π.Equiv (directSum fun i => π.restrict (V i) (hinv i)) where
  toLinearIsometryEquiv := hV.linearIsometryEquiv
  map_apply' g v := by
    apply hV.linearIsometryEquiv.symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply, hV.linearIsometryEquiv_symm_apply]
    conv_lhs => rw [← hV.linearIsometryEquiv.symm_apply_apply v,
      hV.linearIsometryEquiv_symm_apply,
      (π g).map_tsum (hV.OrthogonalFamily.summable_of_lp _)]
    rfl
end UnitaryRep
end GroundTheory.Automorphic


