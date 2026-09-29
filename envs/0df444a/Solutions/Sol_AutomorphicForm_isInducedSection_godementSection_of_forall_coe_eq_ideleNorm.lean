-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9670c85d-806d-583a-be5b-10acb7f62006

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm Matrix

namespace GodementSectionLaw

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem cpow_ideleNorm_mul (a x : (𝔸)ˣ) (s : ℂ) :
    ((ideleNorm F (a * x) : ℝ) : ℂ) ^ s = ((ideleNorm F a : ℝ) : ℂ) ^ s * ((ideleNorm F x : ℝ) : ℂ) ^ s := by
  rw [ideleNorm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos a).le (ideleNorm_pos x).le]

theorem cpow_ideleNorm_ne_zero (a : (𝔸)ˣ) (s : ℂ) : ((ideleNorm F a : ℝ) : ℂ) ^ s ≠ 0 := fun h =>
  (ideleNorm_pos a).ne' (Complex.ofReal_eq_zero.mp ((Complex.cpow_eq_zero_iff _ _).mp h).1)

theorem zetaIntegral_comp_mul_left {mI : MeasurableSpace (𝔸)ˣ} [MeasurableMul (𝔸)ˣ]
    (ν : Measure (𝔸)ˣ) [ν.IsMulLeftInvariant] (f : 𝔸 → ℂ)
    (χ : (𝔸)ˣ →* ℂˣ) (s : ℂ) (a : (𝔸)ˣ) :
    zetaIntegral ν (fun t => f ((a : 𝔸) * t)) χ s
      = ((χ a : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F a : ℝ) : ℂ) ^ (-s) * zetaIntegral ν f χ s := by
  unfold zetaIntegral
  set G : (𝔸)ˣ → ℂ := fun x => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s with hG
  have hint : ∫ x, G (a * x) ∂ν = ∫ x, G x ∂ν := integral_mul_left_eq_self G a
  have hpt : ∀ x : (𝔸)ˣ, f ((a : 𝔸) * x) * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s
      = ((χ a : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F a : ℝ) : ℂ) ^ (-s) * G (a * x) := by
    intro x
    simp only [hG, Units.val_mul, map_mul, cpow_ideleNorm_mul, Complex.cpow_neg]
    field_simp [cpow_ideleNorm_ne_zero a s, Units.ne_zero (χ a)]
  simp_rw [hpt, integral_const_mul, hint]

theorem zetaIntegral_comp_mul_right {mI : MeasurableSpace (𝔸)ˣ} [MeasurableMul (𝔸)ˣ]
    (ν : Measure (𝔸)ˣ) [ν.IsMulLeftInvariant] (f : 𝔸 → ℂ)
    (χ : (𝔸)ˣ →* ℂˣ) (s : ℂ) (a : (𝔸)ˣ) :
    zetaIntegral ν (fun t => f (t * (a : 𝔸))) χ s
      = ((χ a : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F a : ℝ) : ℂ) ^ (-s) * zetaIntegral ν f χ s := by
  have : (fun t : 𝔸 => f (t * (a : 𝔸))) = fun t => f ((a : 𝔸) * t) := by
    funext t; rw [mul_comm]
  rw [this, zetaIntegral_comp_mul_left]

theorem bottomRowVec_borel_mul {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) (t : 𝔸) :
    bottomRowVec F (b * g) t = bottomRowVec F g (t * (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1) := by
  have hb0 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := hb
  funext j
  simp only [bottomRowVec, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb0,
    zero_mul, zero_add]
  ring

theorem cpow_add_half_mul_cpow_neg (r : ℂ) (hr : r ≠ 0) (s : ℂ) :
    r ^ (s + 1 / 2) * r ^ (-(2 * s + 1)) = r ^ (-(s + 1 / 2)) := by
  rw [← Complex.cpow_add _ _ hr]
  congr 1
  ring

theorem main {mI : MeasurableSpace (𝔸)ˣ} [MeasurableMul (𝔸)ˣ]
    (ν₀ : Measure (𝔸)ˣ) [ν₀.IsMulLeftInvariant] (μ ν : (𝔸)ˣ →* ℂˣ) (α : (𝔸)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (Φ : (Fin 2 → 𝔸) → ℂ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (godementSection F ν₀ μ ν α hα Φ s) := by
  intro b hb g
  set a : (𝔸)ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with ha
  set d : (𝔸)ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hd
  have hd1 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = (d : 𝔸) := rfl
  have hdet : Matrix.GeneralLinearGroup.det (b * g) = a * d * Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, det_borel_eq_diag_mul hb]
  have hZ : zetaIntegral ν₀ (fun t => Φ (bottomRowVec F (b * g) t)) (μ * ν⁻¹) (2 * s + 1)
      = (((μ * ν⁻¹) d : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F d : ℝ) : ℂ) ^ (-(2 * s + 1))
        * zetaIntegral ν₀ (fun t => Φ (bottomRowVec F g t)) (μ * ν⁻¹) (2 * s + 1) := by
    have e : (fun t => Φ (bottomRowVec F (b * g) t)) = fun t => Φ (bottomRowVec F g (t * (d : 𝔸))) := by
      funext t; rw [bottomRowVec_borel_mul hb, hd1]
    rw [e]
    exact zetaIntegral_comp_mul_right ν₀ (fun t => Φ (bottomRowVec F g t)) (μ * ν⁻¹) (2 * s + 1) d
  unfold godementSection
  rw [hZ, hdet]
  simp only [map_mul, Units.val_mul, etaFst_apply, etaSnd_apply, cpowChar_apply_val, MonoidHom.mul_apply,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val, mul_inv, inv_inv, hαN]
  have hdz : ((ideleNorm F d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos d).ne'
  have hμd : ((μ d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [← cpow_add_half_mul_cpow_neg _ hdz s]
  field_simp

end GodementSectionLaw

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [MeasurableMul (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (godementSection F ν₀ μ ν α hα Φ s) :=
  GodementSectionLaw.main ν₀ μ ν α hα hαN Φ s

end

end S_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm (solution)
