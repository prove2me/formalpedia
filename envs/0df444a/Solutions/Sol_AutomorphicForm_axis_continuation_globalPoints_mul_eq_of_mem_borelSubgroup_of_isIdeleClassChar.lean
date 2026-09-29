-- Prove2me | solution 1 for AutomorphicForm.axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c5d11435-02a0-58b1-adf8-3a4d3aed0212

import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar

set_option autoImplicit false

namespace R4BorelInv

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped NNReal

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_principal (u : Fˣ) :
    NumberField.TateGlobal.ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u)
      = 1 := by
  have hdet : Matrix.det !![(u : F), 0; 0, 1] ≠ 0 := by
    simp [Matrix.det_fin_two]
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)
  convert h using 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show algebraMap F (AdeleRing (𝓞 F) F) (u : F) =
    Matrix.det ((globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
  rw [Matrix.det_fin_two]
  simp [globalPoints_apply, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem globalPoints_unipotentGL2 (ξ : F) :
    globalPoints (𝓞 F) F (unipotentGL2 ξ) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  apply Units.ext
  ext i j
  rw [show ((globalPoints (𝓞 F) F (unipotentGL2 ξ) : AdelicGL2 (𝓞 F) F) : Matrix _ _ _) i j =
    algebraMap F (AdeleRing (𝓞 F) F) (((unipotentGL2 ξ : GL (Fin 2) F) : Matrix _ _ _) i j) from
    globalPoints_apply (𝓞 F) F _ i j]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField F] in

theorem weyl_unipotent_mul_borel (γ : GL (Fin 2) F) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (ξ : F)
    (hδ : Matrix.det !![(γ : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, (γ : Matrix (Fin 2) (Fin 2) F) 0 0] ≠ 0) :
    gl2Weyl * unipotentGL2 ξ * γ =
      Matrix.GeneralLinearGroup.mkOfDetNeZero _ hδ *
        (gl2Weyl * unipotentGL2 (((γ : Matrix (Fin 2) (Fin 2) F) 0 1 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 1) /
          (γ : Matrix (Fin 2) (Fin 2) F) 0 0)) := by
  have ha : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    apply hδ
    simp [Matrix.det_fin_two, h0]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hγ, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  field_simp

end R4BorelInv

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm R4BorelInv
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (O : Set ℂ) (Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hO : IsOpen O) (_hOc : IsPreconnected O) (_hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O)
      (_hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
      (_hE : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)),
    ∀ s ∈ O, ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      Ec s (globalPoints (𝓞 F) F γ * g) = Ec s g := by
  intro αm hαm μ ν hμ hν φ hφ O Ec hO hOc hOhalf hEa hE

  have hαmK : ∀ u : Fˣ, αm (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
    intro u
    apply Units.ext
    show ((distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) : ℝ≥0) : ℝ) = 1
    exact ideleNorm_principal F u
  have hcpow : ∀ (s : ℂ) (u : Fˣ),
      cpowChar αm hαm s (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
    intro s u
    apply Units.ext
    rw [cpowChar_apply_val, hαmK u]
    simp
  have hη₁ : ∀ (s : ℂ) (u : Fˣ),
      etaFst μ αm hαm s (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
    intro s u
    rw [etaFst_apply, hμ u, hcpow, one_mul]
  have hη₂ : ∀ (s : ℂ) (u : Fˣ),
      etaSnd ν αm hαm s (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
    intro s u
    rw [etaSnd_apply, hν u, hcpow, one_mul]

  have hφB : ∀ (s : ℂ), ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      φ s (globalPoints (𝓞 F) F γ * g) = φ s g := by
    intro s γ hγ g
    have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hγ
    rw [hφ s (globalPoints (𝓞 F) F γ) hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ hmem,
      borelDiagSnd_globalPoints (𝓞 F) F hγ hmem, hη₁, hη₂]
    simp

  have hhalf : ∀ s : ℂ, 1 / 2 < s.re → ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      Ec s (globalPoints (𝓞 F) F γ * g) = Ec s g := by
    intro s hs γ hγ g
    have hγ0 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hγ

    have hdetγ : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 * (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      have h := (Matrix.GeneralLinearGroup.det γ).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hγ0, mul_zero, sub_zero] at h
      exact h
    have ha : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdetγ
    have hd : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdetγ
    have hδ : Matrix.det !![(γ : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, (γ : Matrix (Fin 2) (Fin 2) F) 0 0] ≠ 0 := by
      simp [Matrix.det_fin_two]; exact ⟨hd, ha⟩
    have hδB : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hδ ∈ borelSubgroup F := by
      rw [mem_borelSubgroup_iff]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

    set a := (γ : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
    set b := (γ : Matrix (Fin 2) (Fin 2) F) 0 1 with hb_def
    set d := (γ : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
    let τ : F ≃ F :=
      { toFun := fun ξ => (b + ξ * d) / a
        invFun := fun η => (a * η - b) / d
        left_inv := fun ξ => by field_simp; ring
        right_inv := fun η => by field_simp; ring }
    have hterm : ∀ ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
        (globalPoints (𝓞 F) F γ * g)) =
        φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (τ ξ)) * g) := by
      intro ξ
      have hgl := weyl_unipotent_mul_borel F γ hγ0 ξ hδ
      have hprod : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
          (globalPoints (𝓞 F) F γ * g) =
          globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hδ) *
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (τ ξ)) * g) := by
        have h1 : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
            globalPoints (𝓞 F) F γ = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 ξ * γ) := by
          rw [map_mul, map_mul, globalPoints_unipotentGL2]; rfl
        have h2 : globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hδ) *
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (τ ξ))) =
            globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hδ *
              (gl2Weyl * unipotentGL2 ((b + ξ * d) / a))) := by
          rw [map_mul, map_mul, globalPoints_unipotentGL2]; rfl
        rw [← mul_assoc, h1, hgl, ← mul_assoc (globalPoints (𝓞 F) F _), h2]
      rw [hprod, hφB s _ hδB]
    calc Ec s (globalPoints (𝓞 F) F γ * g)
        = φ s (globalPoints (𝓞 F) F γ * g) + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (globalPoints (𝓞 F) F γ * g)) := hE s hs _
      _ = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (τ ξ)) * g) := by
          rw [hφB s γ hγ g]
          exact congrArg _ (tsum_congr hterm)
      _ = φ s g + ∑' η : F, φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) η) * g) := by
          rw [Equiv.tsum_eq τ (fun η => φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) η) * g))]
      _ = Ec s g := (hE s hs g).symm

  intro s hs γ hγ g
  have han : AnalyticOnNhd ℂ (fun s => Ec s (globalPoints (𝓞 F) F γ * g) - Ec s g) O :=
    (hEa _).sub (hEa _)
  have h1O : (1 : ℂ) ∈ O := hOhalf (by norm_num)
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun s => Ec s (globalPoints (𝓞 F) F γ * g) - Ec s g) =ᶠ[nhds (1 : ℂ)] 0 := by
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by norm_num)) fun z hz => ?_
    simp only [Pi.zero_apply]
    rw [hhalf z hz γ hγ g, sub_self]
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc h1O hev hs
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end S_AutomorphicForm_axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar
end P2MW
export P2MW.S_AutomorphicForm_axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar (solution)
