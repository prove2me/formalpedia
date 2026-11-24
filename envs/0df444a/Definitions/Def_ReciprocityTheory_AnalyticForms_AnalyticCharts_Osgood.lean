-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- name    : ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:11.894663+00:00
-- url     : https://prove2.me/theorems/a69b6782-b8a5-4f2c-b774-d136effed191
-- title:
--   Osgood
-- statement:
--   Definitions and structural lemmas for Osgood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_comp_torusMap
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U
variable {n : ℕ}
abbrev Cube (n : ℕ) : Type := Icc (0 : Fin n → ℝ) (fun _ => 2 * π)
instance : CompactSpace (Cube n) := isCompact_iff_compactSpace.mp isCompact_Icc
def cubeProj (θ : Fin n → ℝ) : Cube n :=
  ⟨fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ),
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.1,
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.2⟩
theorem continuous_cubeProj : Continuous (cubeProj (n := n)) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact continuous_subtype_val.comp (continuous_projIcc.comp (continuous_apply i))
def cubeCoord (c : Fin n → ℂ) (r : ℝ) (i : Fin n) : C(Cube n, ℂ) :=
  ⟨fun θ => torusMap c (fun _ => r) θ.1 i,
    ((continuous_apply i).comp (continuous_torusMap c r)).comp continuous_subtype_val⟩
def kern (c : Fin n → ℂ) (r : ℝ) (z : Fin n → ℂ) : C(Cube n, ℂ) :=
  ∏ i, Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ)))
def jac (r : ℝ) (θ : Fin n → ℝ) : ℂ := ∏ i, (r : ℂ) * exp (θ i * I) * I
def fctl (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ) (g : C(Cube n, ℂ)) : ℂ :=
  ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ)
theorem continuous_jac (r : ℝ) : Continuous (jac (n := n) r) := by
  unfold jac
  exact continuous_finsetProd _ fun i _ => by fun_prop
theorem integrableOn_fctl {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :=
  (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul
    (continuous_comp_torusMap hr.le hf)).integrableOn_Icc
def fctlCLM (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl hr hf g) (integrableOn_fctl hr hf g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul (continuous_comp_torusMap hr.le hf)).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
end ReciprocityTheory.AnForm.Osgood


