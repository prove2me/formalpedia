-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/854b5088-a76c-5512-b63a-680d1c1016cb

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "centralizerBorel IsOrbitalIntegralOn AdelicGL2 centralScalar"
namespace CentralOrbitalValue
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AutomorphicForm.AdelicGL2 (𝓞 K) K

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : 𝔾) :
    AutomorphicForm.centralScalar (𝓞 K) K z * g = g * AutomorphicForm.centralScalar (𝓞 K) K z := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).eq i) j

theorem conj_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) (x : 𝔾) :
    x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K z * x = AutomorphicForm.centralScalar (𝓞 K) K z := by
  rw [mul_assoc, centralScalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_centralizer_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) (g : 𝔾) :
    g ∈ Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K z} : Set 𝔾) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (centralScalar_mul_comm K z g).symm

noncomputable def toCentralizer (z : (AdeleRing (𝓞 K) K)ˣ) :
    𝔾 ≃ₜ* Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K z} : Set 𝔾) where
  toFun g := ⟨g, mem_centralizer_centralScalar K z g⟩
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

@[scoped simp] theorem coe_toCentralizer (z : (AdeleRing (𝓞 K) K)ˣ) (g : 𝔾) :
    ((toCentralizer K z g : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K z} : Set 𝔾)) :
      𝔾) = g := rfl

end AutomorphicForm.CentralOrbitalValue
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar.AutomorphicForm P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar.AutomorphicForm.CentralOrbitalValue"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar.AutomorphicForm"

open AutomorphicForm.CentralOrbitalValue in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c₀ : NNReal) (u : (AdeleRing (𝓞 K) K)ˣ) (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) :
    ∃ τ : Measure (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      τ.IsHaarMeasure ∧
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.centralScalar (𝓞 K) K u) τ f
        (((c₀ : ℝ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 K) K u)) := by
  classical
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  refine ⟨Measure.map (toCentralizer K u) μ, ContinuousMulEquiv.isHaarMeasure_map μ _, ?_⟩

  obtain ⟨C⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :=
    inferInstance
  have hCpos : 0 < μ C :=
    lt_of_lt_of_le (isOpen_interior.measure_pos μ C.interior_nonempty) (measure_mono interior_subset)
  have hCtop : μ C < ⊤ := C.isCompact.measure_lt_top
  have hCreal : 0 < μ.real (C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :=
    ENNReal.toReal_pos hCpos.ne' hCtop.ne

  set w : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ :=
    fun x => (μ.real (C : Set _))⁻¹ * (C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)).indicator 1 x
    with hw
  have hCmeas : MeasurableSet (C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :=
    C.isCompact.measurableSet
  have hw0 : ∀ x, 0 ≤ w x := fun x =>
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hwm : Measurable w := measurable_const.mul (measurable_const.indicator hCmeas)
  have hwc : HasCompactSupport w := by
    refine HasCompactSupport.intro C.isCompact fun x hx => ?_
    simp [hw, Set.indicator_of_notMem hx]
  have hwint : ∫ x, w x ∂μ = 1 := by
    simp only [hw]
    rw [integral_const_mul, integral_indicator_one hCmeas, inv_mul_cancel₀ hCreal.ne']
  refine ⟨w, ⟨hw0, hwm, hwc, fun x _ => ?_⟩, ?_⟩
  ·
    have hemb : MeasurableEmbedding (toCentralizer K u) :=
      (toCentralizer K u).toHomeomorph.measurableEmbedding
    rw [hemb.integral_map]
    have hrw : (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
        w (((toCentralizer K u g : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x)) =
        fun g => w (g * x) := by
      funext g
      rfl
    rw [hrw, integral_mul_right_eq_self (fun g => w g) x, hwint]
  ·
    have hrw : (fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
        f (x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K u * x) * (w x : ℂ)) =
        fun x => f (AutomorphicForm.centralScalar (𝓞 K) K u) * (w x : ℂ) := by
      funext x
      rw [conj_centralScalar]
    rw [hrw, integral_smul_nnreal_measure, integral_const_mul, integral_complex_ofReal, hwint]
    simp [NNReal.smul_def]

end S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar (solution)
