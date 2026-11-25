-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:25:23.802947+00:00
-- url     : https://prove2.me/theorems/5fecb7fe-b90f-4d35-a962-3379fa3216fb
-- title:
--   Coe Polar Exp Homeomorph Complex Apply
-- statement:
--   Definitions and structural lemmas for Coe Polar Exp Homeomorph Complex Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/CoePolarExpHomeomorphComplexApply.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.D.Upq
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
theorem continuousOn_matrix_inv :
    ContinuousOn (fun A : Matrix n n 𝕜 => A⁻¹) {A | IsUnit A} := by
  rintro _ ⟨u, rfl⟩
  have h := NormedRing.inverse_continuousAt u
  have he : (fun A : Matrix n n 𝕜 => A⁻¹) = Ring.inverse := funext nonsing_inv_eq_ringInverse
  rw [he]
  exact h.continuousWithinAt
theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)
noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)
theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h
theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)
noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹
theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit
theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]
theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]
theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]
noncomputable def polarMul (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) : GL n 𝕜 :=
    ⟨kp.1 * kp.2, kp.2.1⁻¹ * star (kp.1 : Matrix n n 𝕜), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kp.2 : Matrix n n 𝕜),
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef kp.2.2), Matrix.one_mul]
      exact mem_unitaryGroup_iff.1 kp.1.2, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star (kp.1 : Matrix n n 𝕜)),
        mem_unitaryGroup_iff'.1 kp.1.2, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef kp.2.2)]⟩
noncomputable def polarEquiv : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ GL n 𝕜 where
  toFun := polarMul
  invFun g := (⟨polarUnitary g, polarUnitary_mem g⟩, ⟨polarPos g, polarPos_posDef g⟩)
  left_inv kp := by
    obtain ⟨⟨k, hk⟩, ⟨p, hp⟩⟩ := kp
    have := polar_unique (g := polarMul (⟨k, hk⟩, ⟨p, hp⟩)) hk hp rfl
    exact Prod.ext (Subtype.ext this.2) (Subtype.ext this.1)
  right_inv g := Units.ext (polarUnitary_mul_polarPos g)
@[simp] theorem coe_polarEquiv_apply (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) :
    ((polarEquiv kp : GL n 𝕜) : Matrix n n 𝕜) = kp.1 * kp.2 := rfl
theorem continuous_polarPos
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    Continuous (polarPos : GL n 𝕜 → Matrix n n 𝕜) :=
  hsqrt.comp_continuous
    ((Units.continuous_val.matrix_conjTranspose).mul Units.continuous_val)
    (fun g => (posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)
noncomputable def polarHomeomorph
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ₜ GL n 𝕜 where
  toEquiv := polarEquiv
  continuous_toFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuousOn_matrix_inv.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun kp => kp.2.2.isUnit)).mul
        (continuous_star.comp (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hP := continuous_polarPos (n := n) (𝕜 := 𝕜) hsqrt
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.mul
      (continuousOn_matrix_inv.comp_continuous hP (fun g => (polarPos_posDef g).isUnit))
noncomputable def polarHomeomorphReal :
    unitaryGroup n ℝ × {p : Matrix n n ℝ // p.PosDef} ≃ₜ GL n ℝ :=
  polarHomeomorph CFC.continuousOn_sqrt
noncomputable def polarHomeomorphComplex :
    unitaryGroup n ℂ × {p : Matrix n n ℂ // p.PosDef} ≃ₜ GL n ℂ :=
  polarHomeomorph CFC.continuousOn_sqrt
section ExpHermitianComplex
theorem posDef_exp_of_isHermitian_complex {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)
noncomputable def expHermitianHomeomorphComplex :
    {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ {p : Matrix n n ℂ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_complex X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℂ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _
noncomputable def polarExpHomeomorphComplex :
    unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ GL n ℂ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphComplex).trans polarHomeomorphComplex
end ExpHermitianComplex
section ExpHermitianReal
theorem posDef_exp_of_isHermitian_real {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)
noncomputable def expHermitianHomeomorphReal :
    {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ {p : Matrix n n ℝ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_real X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℝ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _
noncomputable def polarExpHomeomorphReal :
    unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ GL n ℝ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphReal).trans polarHomeomorphReal
end ExpHermitianReal
end CompanionTheory.D.Upq


