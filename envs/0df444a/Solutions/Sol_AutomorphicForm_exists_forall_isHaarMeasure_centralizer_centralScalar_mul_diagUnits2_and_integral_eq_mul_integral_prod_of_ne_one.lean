-- Prove2me | solution 1 for AutomorphicForm.exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0411dbd1-ef1d-567b-af2a-3f905fd0fb78

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace Coupling25

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

theorem globalPoints_diagUnits2 (u : Kˣ) :
    globalPoints (𝓞 K) K (diagUnits2 u 1) =
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 := by
  apply Units.ext
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) (((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) =
    ((diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 :
      GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  have : centralScalar (𝓞 K) K z ∈ Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 K) K)) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨z, rfl⟩
  exact ((Subgroup.mem_center_iff.mp this) g).symm

theorem centralizer_eq (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1} :
        Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) =
      Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K)) := by
  rw [globalPoints_diagUnits2]
  set d := diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 with hd
  ext t
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have : centralScalar (𝓞 K) K z * (d * t) = centralScalar (𝓞 K) K z * (t * d) := by
      calc centralScalar (𝓞 K) K z * (d * t) = centralScalar (𝓞 K) K z * d * t := (mul_assoc _ _ _).symm
        _ = t * (centralScalar (𝓞 K) K z * d) := h
        _ = t * centralScalar (𝓞 K) K z * d := (mul_assoc _ _ _).symm
        _ = centralScalar (𝓞 K) K z * t * d := by rw [← centralScalar_comm K z t]
        _ = centralScalar (𝓞 K) K z * (t * d) := mul_assoc _ _ _
    exact mul_left_cancel this
  · intro h
    calc centralScalar (𝓞 K) K z * d * t = centralScalar (𝓞 K) K z * (d * t) := mul_assoc _ _ _
      _ = centralScalar (𝓞 K) K z * (t * d) := by rw [h]
      _ = centralScalar (𝓞 K) K z * t * d := (mul_assoc _ _ _).symm
      _ = t * centralScalar (𝓞 K) K z * d := by rw [centralScalar_comm K z t]
      _ = t * (centralScalar (𝓞 K) K z * d) := mul_assoc _ _ _

noncomputable def congrCME (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K)) ≃ₜ*
      Subgroup.centralizer ({centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1} :
        Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) :=
  { MulEquiv.subgroupCongr (centralizer_eq K u z).symm with
    continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
    continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }

theorem congrCME_apply_coe (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ)
    (s : Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K))) :
    ((congrCME K u z s : Subgroup.centralizer ({centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1} :
        Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) : GL (Fin 2) (AdeleRing (𝓞 K) K)) = (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) := rfl

open scoped Classical in
theorem main
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK) :
    ∃ (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))),
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) := by

  have hsrc : ∀ u : Kˣ, ((u : Kˣ) : K) ≠ 1 →
      ∃ τ : Measure (Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K))),
        τ.IsHaarMeasure ∧ ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
          ∫ s : Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K)),
              g (s : AdelicGL2 (𝓞 K) K) ∂τ =
            cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK) := by
    intro u hu
    refine AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
      K νZK cτK hcτK (diagUnits2 u 1) ?_ ?_ ?_
    · simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · simpa [LanglandsTunnell.CubicInduction.coe_diagUnits2] using hu

  have hB1 : ∀ u : Kˣ, BorelSpace (Subgroup.centralizer ({globalPoints (𝓞 K) K (diagUnits2 u 1)} : Set (AdelicGL2 (𝓞 K) K))) :=
    fun u => ⟨rfl⟩
  have hB2 : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), BorelSpace (Subgroup.centralizer ({centralScalar (𝓞 K) K z *
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1} :
      Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) := fun u z => ⟨rfl⟩
  refine ⟨fun u z => if h : ((u : Kˣ) : K) ≠ 1 then Measure.map (congrCME K u z) (hsrc u h).choose else 0, ?_, ?_⟩
  · intro u z hu
    dsimp only
    rw [dif_pos hu]
    haveI := hB1 u; haveI := hB2 u z
    haveI := (hsrc u hu).choose_spec.1
    exact ContinuousMulEquiv.isHaarMeasure_map _ (congrCME K u z)
  · intro u z hu g
    dsimp only
    rw [dif_pos hu]
    haveI := hB1 u; haveI := hB2 u z
    have hspec := (hsrc u hu).choose_spec.2 g
    rw [← hspec]
    have := integral_map_equiv (μ := (hsrc u hu).choose) (congrCME K u z).toHomeomorph.toMeasurableEquiv
      (fun t => g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)))
    exact this

end Coupling25

open scoped Classical in
open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK) :
    ∃ (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))),
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) :=
  Coupling25.main K νZK cτK hcτK

end S_AutomorphicForm_exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one (solution)
