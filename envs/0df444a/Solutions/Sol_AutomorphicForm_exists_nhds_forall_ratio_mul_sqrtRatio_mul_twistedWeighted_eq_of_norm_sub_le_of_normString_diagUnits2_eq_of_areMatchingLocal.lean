-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8a2e62ec-a698-533c-a40f-33ef8aee1220

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Pointwise

namespace TwWindow

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

def P (a t : (v.adicCompletion K)ˣ) (J : ℂ) : Prop :=
  ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) ∧
    ∃ τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' ∧
      τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 ∧
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J

noncomputable def iotaU : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight :
    v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom)

section r2dropins

theorem coe_iotaU (d : (v.adicCompletion K)ˣ) :
    ((iotaU K L v d : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = Algebra.TensorProduct.includeRight (R := K) (A := L) (d : v.adicCompletion K) := rfl

theorem toTensorGL_diagUnits2_iotaU (a b : (v.adicCompletion K)ˣ) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) = diagUnits2 (iotaU K L v a) (iotaU K L v b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      coe_iotaU]

theorem diagUnits2_mul' (x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_mul_toTensorGL_diagUnits2 (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (d₁ d₂ : (v.adicCompletion K)ˣ) :
    diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d₁ d₂) =
      diagUnits2 (α * iotaU K L v d₁) (β * iotaU K L v d₂) := by
  rw [toTensorGL_diagUnits2_iotaU, diagUnits2_mul']

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) x)
        (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul']

theorem sigmaU_iotaU (d : (v.adicCompletion K)ˣ) :
    Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) (iotaU K L v d) = iotaU K L v d := by
  apply Units.ext
  rw [Units.coe_map, coe_iotaU]
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K)) ((1 : L) ⊗ₜ (d : v.adicCompletion K)) = (1 : L) ⊗ₜ (d : v.adicCompletion K)
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem prod_iterate_mul_fixed (f : (L ⊗[K] v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ) (x c : (L ⊗[K] v.adicCompletion K)ˣ) (hc : f c = c) (n : ℕ) :
    ((List.range n).map fun i => (⇑f)^[i] (x * c)).prod = ((List.range n).map fun i => (⇑f)^[i] x).prod * c ^ n := by
  have hit : ∀ i, (⇑f)^[i] (x * c) = (⇑f)^[i] x * c := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, hc]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, ih, hit, pow_succ]
    simp only [mul_assoc, mul_left_comm ((⇑f)^[n] x) (c ^ n) c, mul_comm ((⇑f)^[n] x) (c ^ n)]

theorem diagUnits2_inj {x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ} (h : diagUnits2 x y = diagUnits2 x' y') : x = x' ∧ y = y' := by
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp at h00 h11
  exact ⟨Units.ext h00, Units.ext h11⟩

theorem normString_diagUnits2_mul_iotaU [FiniteDimensional K L]
    (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b d₁ d₂ : (v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 (α * iotaU K L v d₁) (β * iotaU K L v d₂)) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K)
        (diagUnits2 (a * d₁ ^ Module.finrank K L) (b * d₂ ^ Module.finrank K L)) := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2_iotaU] at hN ⊢
  obtain ⟨h1, h2⟩ := diagUnits2_inj K L v hN
  rw [prod_iterate_mul_fixed K L v _ α _ (sigmaU_iotaU K L σ v d₁),
    prod_iterate_mul_fixed K L v _ β _ (sigmaU_iotaU K L σ v d₂), h1, h2, map_mul, map_pow, map_mul, map_pow]

theorem mem_centralizer_diagUnits2_iff (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) (v.adicCompletion K))) ↔
      ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
      ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
  have hsub : IsUnit ((a : v.adicCompletion K) - (b : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg
    have hcomm := hg _ (Set.mem_singleton _)
    have hM := congrArg (fun x : GL (Fin 2) (v.adicCompletion K) => ((x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) hcomm
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at hM
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    constructor
    · have : ((a : v.adicCompletion K) - (b : v.adicCompletion K)) * ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
        linear_combination e01
      exact (hsub.mul_right_eq_zero).1 this
    · have : ((a : v.adicCompletion K) - (b : v.adicCompletion K)) * ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
        linear_combination (-1 : v.adicCompletion K) * e10
      exact (hsub.mul_right_eq_zero).1 this
  · rintro ⟨h01, h10⟩ h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem twistedCentralizer_diagUnits2_eq [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β α' β' : (L ⊗[K] v.adicCompletion K)ˣ) (a b a' b' : (v.adicCompletion K)ˣ)
    (hab : a ≠ b) (hab' : a' ≠ b')
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (hN' : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' b')) :
    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β') := by
  have hu : IsUnit ((a : v.adicCompletion K) - (b : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))
  have hu' : IsUnit ((a' : v.adicCompletion K) - (b' : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab' (Units.ext h))
  rw [AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub K L σ hgen (v.adicCompletion K) a b hu α β hN,
    AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub K L σ hgen (v.adicCompletion K) a' b' hu' α' β' hN']
  congr 1
  ext g
  rw [mem_centralizer_diagUnits2_iff K v a b hab, mem_centralizer_diagUnits2_iff K v a' b' hab']

end r2dropins

theorem transport_of_subgroup_eq {G : Type*} [Group G] [TopologicalSpace G]
    (S : Set G) {H₁ H₂ : Subgroup G} (h : H₁ = H₂) (τ : @Measure H₁ (borel H₁))
    (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ) :
    ∃ τ₂ : @Measure H₂ (borel H₂), @Measure.IsHaarMeasure H₂ _ _ (borel H₂) τ₂ ∧
      τ₂ {t | (t : G) ∈ S} = τ {t | (t : G) ∈ S} ∧
      ∀ f : G → ℝ, ∀ x : G,
        (@integral H₂ ℝ _ _ (borel H₂) τ₂ fun t => f ((t : G) * x)) =
          @integral H₁ ℝ _ _ (borel H₁) τ fun t => f ((t : G) * x) := by
  subst h
  exact ⟨τ, hτ, rfl, fun _ _ => rfl⟩

end TwWindow

namespace TwShiftDiag
variable {R : Type*} [CommRing R]

theorem diagUnits2_mul_diagUnits2 (x y x' y' : Rˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_one : diagUnits2 (1 : Rˣ) 1 = 1 := by
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_inv (x y : Rˣ) : (diagUnits2 x y)⁻¹ = diagUnits2 x⁻¹ y⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits2_mul_diagUnits2, mul_inv_cancel, mul_inv_cancel, diagUnits2_one]

theorem diagUnits2_comm (x y x' y' : Rˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 x' y' * diagUnits2 x y := by
  rw [diagUnits2_mul_diagUnits2, diagUnits2_mul_diagUnits2, mul_comm x, mul_comm y]

end TwShiftDiag

namespace TwShiftTop

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

end TwShiftTop

namespace TwXi

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

noncomputable def Nm (x : L ⊗[K] v.adicCompletion K) : L ⊗[K] v.adicCompletion K :=
  ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] x).prod

noncomputable def NmU (x : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)ˣ :=
  ((List.range (Module.finrank K L)).map fun i =>
    (⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[i] x).prod

noncomputable def ι : v.adicCompletion K →+* L ⊗[K] v.adicCompletion K :=
  (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom

private noncomputable def _root_.TwXi.iotaU : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom)

p2m_export "TwXi" "iotaU"

theorem sigmaTensor_mul_apply (τ₁ τ₂ : L ≃ₐ[K] L) (x : L ⊗[K] v.adicCompletion K) :
    sigmaTensor K L (v.adicCompletion K) (τ₁ * τ₂) x = sigmaTensor K L (v.adicCompletion K) τ₁ (sigmaTensor K L (v.adicCompletion K) τ₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (τ₁ * τ₂).toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a) =
      Algebra.TensorProduct.map τ₁.toAlgHom (AlgHom.id K (v.adicCompletion K))
        (Algebra.TensorProduct.map τ₂.toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] v.adicCompletion K) : sigmaTensor K L (v.adicCompletion K) 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (n : ℕ) (x : L ⊗[K] v.adicCompletion K) :
    (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[n] x = sigmaTensor K L (v.adicCompletion K) (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem pow_finrank_eq_one [FiniteDimensional K L] : σ ^ Module.finrank K L = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
    IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at h1
  rw [← h1]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem sigmaTensor_iterate_finrank [FiniteDimensional K L] (x : L ⊗[K] v.adicCompletion K) :
    (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] x = x := by
  rw [sigmaTensor_iterate, pow_finrank_eq_one, sigmaTensor_one_apply]

theorem unitsMap_iterate_val (n : ℕ) (x : (L ⊗[K] v.adicCompletion K)ˣ) :
    (((⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[n] x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[n] (x : L ⊗[K] v.adicCompletion K) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]; rfl

theorem unitsMap_iterate_finrank [FiniteDimensional K L] (x : (L ⊗[K] v.adicCompletion K)ˣ) :
    (⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[Module.finrank K L] x = x :=
  Units.ext (by rw [unitsMap_iterate_val, sigmaTensor_iterate_finrank])

theorem coe_NmU (x : (L ⊗[K] v.adicCompletion K)ˣ) : ((NmU K L σ v x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = Nm K L σ v (x : L ⊗[K] v.adicCompletion K) := by
  unfold NmU Nm
  induction Module.finrank K L with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, Units.val_mul, ih, unitsMap_iterate_val]

theorem NmU_mul (x y : (L ⊗[K] v.adicCompletion K)ˣ) : NmU K L σ v (x * y) = NmU K L σ v x * NmU K L σ v y := by
  unfold NmU
  have hit : ∀ i, (⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[i] (x * y) =
      (⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[i] x *
        (⇑(Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)))^[i] y := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  induction Module.finrank K L with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, hit]
    exact mul_mul_mul_comm (_ : (L ⊗[K] v.adicCompletion K)ˣ) _ _ _

omit σ in
theorem iterate_telescope {G : Type*} [CommGroup G] (f : G →* G) (z : G) (n : ℕ) :
    ((List.range n).map fun i => (⇑f)^[i] (f z * z⁻¹)).prod = (⇑f)^[n] z * z⁻¹ := by
  have hit : ∀ i, (⇑f)^[i] (f z * z⁻¹) = (⇑f)^[i + 1] z * ((⇑f)^[i] z)⁻¹ := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_inv, ← Function.iterate_succ_apply' (⇑f) (k + 1) z,
        ← Function.iterate_succ_apply' (⇑f) k z]
  have key : ∀ a b w : G, a * w * (b * a⁻¹) = b * w := fun a b w => by
    rw [mul_comm b a⁻¹, mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, ih, hit, key]

theorem NmU_sigma_mul_inv [FiniteDimensional K L] (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    NmU K L σ v (Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) z * z⁻¹) = 1 := by
  have h := iterate_telescope (Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K)) z (Module.finrank K L)
  unfold NmU
  rw [h, unitsMap_iterate_finrank, mul_inv_cancel]

theorem unitsMap_toMonoidHom_eq :
    Units.map (sigmaTensor K L (v.adicCompletion K) σ).toMonoidHom = Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) := rfl

private theorem _root_.TwXi.coe_iotaU (d : (v.adicCompletion K)ˣ) :
    ((iotaU K L v d : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = Algebra.TensorProduct.includeRight (R := K) (A := L) (d : v.adicCompletion K) := rfl

p2m_export "TwXi" "coe_iotaU"
private theorem _root_.TwXi.toTensorGL_diagUnits2_iotaU (a b : (v.adicCompletion K)ˣ) :
    toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) = diagUnits2 (iotaU K L v a) (iotaU K L v b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2, coe_iotaU]

p2m_export "TwXi" "toTensorGL_diagUnits2_iotaU"
omit σ in
theorem diagUnits2_mul' (x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem _root_.TwXi.sigmaGL_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    sigmaGL K L (v.adicCompletion K) σ (diagUnits2 x y) =
      diagUnits2 (Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) x)
        (Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

p2m_export "TwXi" "sigmaGL_diagUnits2"
theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    (sigmaGL K L (v.adicCompletion K) σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] x)
        ((Units.map (sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    normString K L (v.adicCompletion K) σ (diagUnits2 x y) = diagUnits2 (NmU K L σ v x) (NmU K L σ v y) := by
  unfold normString NmU
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul']

omit σ in
theorem diagUnits2_inj {x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ} (h : diagUnits2 x y = diagUnits2 x' y') : x = x' ∧ y = y' := by
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp at h00 h11
  exact ⟨Units.ext h00, Units.ext h11⟩

theorem NmU_eq_of_normString_diagUnits2 {α β : (L ⊗[K] v.adicCompletion K)ˣ} {a b : (v.adicCompletion K)ˣ}
    (hN : normString K L (v.adicCompletion K) σ (diagUnits2 α β) = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) :
    NmU K L σ v α = iotaU K L v a ∧ NmU K L σ v β = iotaU K L v b := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2_iotaU] at hN
  exact diagUnits2_inj K L v hN

noncomputable def Pk (u : L ⊗[K] v.adicCompletion K) : ℕ → L ⊗[K] v.adicCompletion K
  | 0 => 1
  | k + 1 => sigmaTensor K L (v.adicCompletion K) σ (Pk u k) * u

noncomputable def Sk (u η : L ⊗[K] v.adicCompletion K) : ℕ → L ⊗[K] v.adicCompletion K
  | 0 => 0
  | k + 1 => sigmaTensor K L (v.adicCompletion K) σ (Pk K L σ v u k) * η + sigmaTensor K L (v.adicCompletion K) σ (Sk u η k)

theorem iterate_eq_Pk_mul_add_Sk {u η ξ : L ⊗[K] v.adicCompletion K} (h : sigmaTensor K L (v.adicCompletion K) σ ξ = u * ξ + η) (k : ℕ) :
    (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[k] ξ = Pk K L σ v u k * ξ + Sk K L σ v u η k := by
  induction k with
  | zero => simp [Pk, Sk]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_mul, h]
    simp only [Pk, Sk]
    ring

theorem Pk_eq_listProd (u : L ⊗[K] v.adicCompletion K) (k : ℕ) :
    Pk K L σ v u k = ((List.range k).map fun i => (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] u).prod := by
  induction k with
  | zero => simp [Pk]
  | succ k ih =>
    have hfun : ((⇑(sigmaTensor K L (v.adicCompletion K) σ)) ∘ fun i => (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] u) =
        fun i => (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i + 1] u :=
      funext fun i => (Function.iterate_succ_apply' (⇑(sigmaTensor K L (v.adicCompletion K) σ)) i u).symm
    show sigmaTensor K L (v.adicCompletion K) σ (Pk K L σ v u k) * u = _
    rw [ih, map_list_prod, List.map_map, hfun, List.prod_range_succ', Function.iterate_zero_apply]
    exact mul_comm _ _

theorem Pk_finrank_eq_Nm (u : L ⊗[K] v.adicCompletion K) : Pk K L σ v u (Module.finrank K L) = Nm K L σ v u := by
  rw [Pk_eq_listProd]; rfl

theorem continuous_Pk [FiniteDimensional K L] (k : ℕ) : Continuous fun u : L ⊗[K] v.adicCompletion K => Pk K L σ v u k := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hσ : Continuous (sigmaTensor K L (v.adicCompletion K) σ) :=
    IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
  induction k with
  | zero => simp only [Pk]; exact continuous_const
  | succ k ih => simp only [Pk]; exact (hσ.comp ih).mul continuous_id

theorem continuous_Sk [FiniteDimensional K L] (k : ℕ) : Continuous fun p : L ⊗[K] v.adicCompletion K × L ⊗[K] v.adicCompletion K => Sk K L σ v p.1 p.2 k := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hσ : Continuous (sigmaTensor K L (v.adicCompletion K) σ) :=
    IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
  induction k with
  | zero => simp only [Sk]; exact continuous_const
  | succ k ih =>
    simp only [Sk]
    exact ((hσ.comp ((continuous_Pk K L σ v k).comp continuous_fst)).mul continuous_snd).add (hσ.comp ih)

omit σ in
theorem du_e11 (p q : (L ⊗[K] v.adicCompletion K)ˣ) (η : L ⊗[K] v.adicCompletion K) :
    ((diagUnits2 p q * unipotentGL2 η : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 = (q : L ⊗[K] v.adicCompletion K) := by
  simp [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

omit σ in
theorem du_e01 (p q : (L ⊗[K] v.adicCompletion K)ˣ) (η : L ⊗[K] v.adicCompletion K) :
    ((diagUnits2 p q * unipotentGL2 η : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = (p : L ⊗[K] v.adicCompletion K) * η := by
  simp [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

omit σ in
theorem du_inv00 (p q : (L ⊗[K] v.adicCompletion K)ˣ) (η : L ⊗[K] v.adicCompletion K) :
    (((diagUnits2 p q * unipotentGL2 η)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 =
      ((p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := by
  have h : (((diagUnits2 p q * unipotentGL2 η)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      !![1, -η; 0, 1] * !![((p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K), 0; 0, ((q⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)] := by
    rw [mul_inv_rev, Units.val_mul]
    rfl
  rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def Fxi (z : (v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K × L ⊗[K] v.adicCompletion K)) : L ⊗[K] v.adicCompletion K :=
  ι K L v (((1 : v.adicCompletion K) - (z.1 : v.adicCompletion K))⁻¹) * Sk K L σ v z.2.1 z.2.2 (Module.finrank K L)

theorem continuous_iota [FiniteDimensional K L] : Continuous (ι K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have h : Continuous (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K))
  have heq : (ι K L v : v.adicCompletion K → L ⊗[K] v.adicCompletion K) = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) := by
    funext r
    show Algebra.TensorProduct.includeRight (R := K) (A := L) r = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) r
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.RightActions.algebraMap_eval]
  rw [heq]; exact h

theorem continuousOn_Fxi [FiniteDimensional K L] (Cc : Set (v.adicCompletion K)ˣ) (h1 : (1 : (v.adicCompletion K)ˣ) ∉ Cc)
    (T : Set (L ⊗[K] v.adicCompletion K × L ⊗[K] v.adicCompletion K)) : ContinuousOn (Fxi K L σ v) (Cc ×ˢ T) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  unfold Fxi
  refine ContinuousOn.mul ?_ ((continuous_Sk K L σ v (Module.finrank K L)).comp continuous_snd).continuousOn
  refine (continuous_iota K L v).comp_continuousOn ?_
  refine ContinuousOn.inv₀ ((continuous_const.sub (Units.continuous_val.comp continuous_fst)).continuousOn) ?_
  rintro ⟨c, w⟩ ⟨hc, -⟩
  show (1 : v.adicCompletion K) - (c : v.adicCompletion K) ≠ 0
  intro h0
  apply h1
  have : c = 1 := Units.ext ((sub_eq_zero.1 h0).symm)
  rwa [this] at hc

theorem Fxi_eq_of_key [FiniteDimensional K L] {u η ξ : L ⊗[K] v.adicCompletion K} {c : (v.adicCompletion K)ˣ}
    (hkey : ξ = ι K L v (c : v.adicCompletion K) * ξ + Sk K L σ v u η (Module.finrank K L))
    (h1c : (1 : v.adicCompletion K) - (c : v.adicCompletion K) ≠ 0) :
    Fxi K L σ v (c, (u, η)) = ξ := by
  unfold Fxi
  have hS : Sk K L σ v u η (Module.finrank K L) = ι K L v ((1 : v.adicCompletion K) - (c : v.adicCompletion K)) * ξ := by
    rw [map_sub, map_one, sub_mul, one_mul]
    linear_combination (-1 : L ⊗[K] v.adicCompletion K) * hkey
  show ι K L v (((1 : v.adicCompletion K) - (c : v.adicCompletion K))⁻¹) * Sk K L σ v u η (Module.finrank K L) = ξ
  rw [hS, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h1c, map_one, one_mul]

theorem exists_isCompact_forall_xi_mem [FiniteDimensional K L]
    (Ω' : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hΩ' : IsCompact Ω')
    (Cc : Set (v.adicCompletion K)ˣ) (hCc : IsCompact Cc) (h1 : (1 : (v.adicCompletion K)ˣ) ∉ Cc) :
    ∃ Ξ : Set (L ⊗[K] v.adicCompletion K), IsCompact Ξ ∧
      ∀ (p q : (L ⊗[K] v.adicCompletion K)ˣ) (ξ : L ⊗[K] v.adicCompletion K) (c : (v.adicCompletion K)ˣ), c ∈ Cc →
        Nm K L σ v ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = ι K L v (c : v.adicCompletion K) →
        (diagUnits2 p q * unipotentGL2 (sigmaTensor K L (v.adicCompletion K) σ ξ - ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * ξ) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Ω' → ξ ∈ Ξ := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)

  set e11 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 with he11
  set e01 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 with he01
  set i00 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 with hi00
  have he11c : Continuous e11 := Units.continuous_val.matrix_elem 1 1
  have he01c : Continuous e01 := Units.continuous_val.matrix_elem 0 1
  have hi00c : Continuous i00 := Units.continuous_coe_inv.matrix_elem 0 0
  set U₀ : Set (L ⊗[K] v.adicCompletion K) := (e11 '' Ω') * (i00 '' Ω') with hU₀
  set H₀ : Set (L ⊗[K] v.adicCompletion K) := (i00 '' Ω') * (e01 '' Ω') with hH₀
  have hU₀c : IsCompact U₀ := (hΩ'.image he11c).mul (hΩ'.image hi00c)
  have hH₀c : IsCompact H₀ := (hΩ'.image hi00c).mul (hΩ'.image he01c)
  refine ⟨Fxi K L σ v '' (Cc ×ˢ (U₀ ×ˢ H₀)),
    (hCc.prod (hU₀c.prod hH₀c)).image_of_continuousOn (continuousOn_Fxi K L σ v Cc h1 _), ?_⟩
  intro p q ξ c hc hN hΩ
  set u : L ⊗[K] v.adicCompletion K := ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) with hu
  set η : L ⊗[K] v.adicCompletion K := sigmaTensor K L (v.adicCompletion K) σ ξ - u * ξ with hη
  set g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := diagUnits2 p q * unipotentGL2 η with hg
  have hg11 : e11 g = (q : L ⊗[K] v.adicCompletion K) := du_e11 K L v p q η
  have hg01 : e01 g = (p : L ⊗[K] v.adicCompletion K) * η := du_e01 K L v p q η
  have hgi00 : i00 g = ((p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := du_inv00 K L v p q η
  have huU : u ∈ U₀ := by
    have : u = e11 g * i00 g := by rw [hg11, hgi00, hu, Units.val_mul]
    rw [this]
    exact Set.mul_mem_mul ⟨g, hΩ, rfl⟩ ⟨g, hΩ, rfl⟩
  have hηH : η ∈ H₀ := by
    have : η = i00 g * e01 g := by
      rw [hgi00, hg01, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Set.mul_mem_mul ⟨g, hΩ, rfl⟩ ⟨g, hΩ, rfl⟩
  refine ⟨(c, (u, η)), ⟨hc, huU, hηH⟩, ?_⟩
  have hrec : sigmaTensor K L (v.adicCompletion K) σ ξ = u * ξ + η := by rw [hη]; ring
  have hkey := iterate_eq_Pk_mul_add_Sk K L σ v hrec (Module.finrank K L)
  rw [sigmaTensor_iterate_finrank, Pk_finrank_eq_Nm, hN] at hkey
  have h1c : (1 : v.adicCompletion K) - (c : v.adicCompletion K) ≠ 0 := by
    intro h0; apply h1
    have : c = 1 := Units.ext ((sub_eq_zero.1 h0).symm)
    rwa [this] at hc
  exact Fxi_eq_of_key K L σ v hkey h1c

theorem exists_isCompact_forall_one_sub_Nm_mul_xi_mem [FiniteDimensional K L]
    (Ω' : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hΩ' : IsCompact Ω') :
    ∃ C : Set (L ⊗[K] v.adicCompletion K), IsCompact C ∧ ∀ (p q : (L ⊗[K] v.adicCompletion K)ˣ) (ξ : L ⊗[K] v.adicCompletion K),
      (diagUnits2 p q * unipotentGL2 (sigmaTensor K L (v.adicCompletion K) σ ξ - ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * ξ) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Ω' →
      (1 - Nm K L σ v ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) * ξ ∈ C := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  set e11 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 with he11
  set e01 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 with he01
  set i00 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → L ⊗[K] v.adicCompletion K := fun g => ((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 with hi00
  have he11c : Continuous e11 := Units.continuous_val.matrix_elem 1 1
  have he01c : Continuous e01 := Units.continuous_val.matrix_elem 0 1
  have hi00c : Continuous i00 := Units.continuous_coe_inv.matrix_elem 0 0
  set U₀ : Set (L ⊗[K] v.adicCompletion K) := (e11 '' Ω') * (i00 '' Ω') with hU₀
  set H₀ : Set (L ⊗[K] v.adicCompletion K) := (i00 '' Ω') * (e01 '' Ω') with hH₀
  have hU₀c : IsCompact U₀ := (hΩ'.image he11c).mul (hΩ'.image hi00c)
  have hH₀c : IsCompact H₀ := (hΩ'.image hi00c).mul (hΩ'.image he01c)
  refine ⟨(fun z : L ⊗[K] v.adicCompletion K × L ⊗[K] v.adicCompletion K => Sk K L σ v z.1 z.2 (Module.finrank K L)) '' (U₀ ×ˢ H₀),
    (hU₀c.prod hH₀c).image (continuous_Sk K L σ v (Module.finrank K L)), ?_⟩
  intro p q ξ hΩ
  set u : L ⊗[K] v.adicCompletion K := ((q * p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) with hu
  set η : L ⊗[K] v.adicCompletion K := sigmaTensor K L (v.adicCompletion K) σ ξ - u * ξ with hη
  set g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := diagUnits2 p q * unipotentGL2 η with hg
  have hg11 : e11 g = (q : L ⊗[K] v.adicCompletion K) := du_e11 K L v p q η
  have hg01 : e01 g = (p : L ⊗[K] v.adicCompletion K) * η := du_e01 K L v p q η
  have hgi00 : i00 g = ((p⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := du_inv00 K L v p q η
  have huU : u ∈ U₀ := by
    have : u = e11 g * i00 g := by rw [hg11, hgi00, hu, Units.val_mul]
    rw [this]
    exact Set.mul_mem_mul ⟨g, hΩ, rfl⟩ ⟨g, hΩ, rfl⟩
  have hηH : η ∈ H₀ := by
    have : η = i00 g * e01 g := by
      rw [hgi00, hg01, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Set.mul_mem_mul ⟨g, hΩ, rfl⟩ ⟨g, hΩ, rfl⟩
  refine ⟨(u, η), ⟨huU, hηH⟩, ?_⟩
  have hrec : sigmaTensor K L (v.adicCompletion K) σ ξ = u * ξ + η := by rw [hη]; ring
  have hkey := iterate_eq_Pk_mul_add_Sk K L σ v hrec (Module.finrank K L)
  rw [sigmaTensor_iterate_finrank, Pk_finrank_eq_Nm] at hkey
  show Sk K L σ v u η (Module.finrank K L) = (1 - Nm K L σ v u) * ξ
  linear_combination (-1 : L ⊗[K] v.adicCompletion K) * hkey

end TwXi

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

def triv : E ≃L[F] (Fin (Module.finrank F E) → F) :=
  let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem secondCountableTopology_E : SecondCountableTopology E :=
  (triv (K := K) (L := L) (v := v)).toHomeomorph.secondCountableTopology

attribute [local instance] secondCountableTopology_E

theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem isUnit_iff_norm_ne_zero (x : E) : IsUnit x ↔ Algebra.norm F x ≠ 0 := by
  constructor
  · intro hx h0
    obtain ⟨u, rfl⟩ := hx
    have h1 : Algebra.norm F ((u : E)) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    have hdet : LinearMap.det (Algebra.lmul F E x) ≠ 0 := by
      rwa [← Algebra.norm_apply]
    have hbij : Function.Bijective (Algebra.lmul F E x) := by
      have hu : IsUnit (Algebra.lmul F E x) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      exact (Module.End.isUnit_iff _).1 hu
    obtain ⟨y, hy⟩ := hbij.2 1
    have hy' : x * y = 1 := by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hy; exact hy
    exact IsUnit.of_mul_eq_one y hy'

theorem isClosed_nonunits : IsClosed {x : E | ¬ IsUnit x} := by
  have : {x : E | ¬ IsUnit x} = (Algebra.norm F : E → F) ⁻¹' {0} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, isUnit_iff_norm_ne_zero, not_not]
  rw [this]
  exact isClosed_singleton.preimage continuous_algebraNorm

theorem isOpen_units : IsOpen {x : E | IsUnit x} := by
  have : {x : E | IsUnit x} = {x : E | ¬ IsUnit x}ᶜ := by ext; simp
  rw [this]; exact isClosed_nonunits.isOpen_compl

section Inverse

open scoped Classical in

def adjLin : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F →ₗ[F] E :=
  (LinearMap.applyₗ (1 : E)) ∘ₗ
    (Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)).toLinearMap

open scoped Classical in

def adjE (y : E) : E := adjLin (K := K) (L := L) (v := v) (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate

theorem adjE_eq (y : E) :
    adjE y = Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)
      (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate 1 := rfl

theorem mul_adjE (y : E) : y * adjE y = algebraMap F E (Algebra.norm F y) := by
  classical
  set b := Module.finBasis F E with hb
  have h1 : Matrix.toLin b b (Algebra.leftMulMatrix b y) = Algebra.lmul F E y := by
    rw [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
  have h2 : Matrix.toLin b b (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) =
      (Algebra.lmul F E y) ∘ₗ Matrix.toLin b b (Algebra.leftMulMatrix b y).adjugate := by
    rw [Matrix.toLin_mul b b b, h1]
  have h3 : y * adjE y = Matrix.toLin b b
      (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) 1 := by
    rw [h2, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', adjE_eq]
  rw [h3, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply,
    Algebra.norm_eq_matrix_det b, Algebra.algebraMap_eq_smul_one]

theorem continuous_adjE : Continuous (adjE : E → E) := by
  classical
  have h1 : Continuous fun y : E => Algebra.leftMulMatrix (Module.finBasis F E) y :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (Module.finBasis F E)).toLinearMap
  haveI : IsModuleTopology F (Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F) :=
    inferInstanceAs (IsModuleTopology F (Fin (Module.finrank F E) → Fin (Module.finrank F E) → F))
  have h2 : Continuous (adjLin (K := K) (L := L) (v := v)) := IsModuleTopology.continuous_of_linearMap _
  exact h2.comp h1.matrix_adjugate

theorem ringInverse_eq {y : E} (hy : IsUnit y) :
    Ring.inverse y = (Algebra.norm F y)⁻¹ • adjE y := by
  have hN : Algebra.norm F y ≠ 0 := (isUnit_iff_norm_ne_zero y).1 hy
  have hmul := mul_adjE (K := K) (L := L) (v := v) y
  have h1 : Ring.inverse y * (y * adjE y) = adjE y := by
    rw [← mul_assoc, Ring.inverse_mul_cancel _ hy, one_mul]
  rw [hmul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem continuous_ringInverse_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (hu : ∀ x, IsUnit (f x)) :
    Continuous fun x => Ring.inverse (f x) := by
  have : (fun x => Ring.inverse (f x)) = fun x => (Algebra.norm F (f x))⁻¹ • adjE (f x) := by
    funext x; exact ringInverse_eq (hu x)
  rw [this]
  refine (Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_).smul (continuous_adjE.comp hf)
  exact (isUnit_iff_norm_ne_zero _).1 (hu x)

end Inverse

theorem t2Space_GL : T2Space G := AutomorphicForm.t2Space_tensorGL K L F

theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_GL : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F

theorem isTopologicalGroup_GL : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

private theorem _root_.KcSemiLocalIwasawaHaar.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "KcSemiLocalIwasawaHaar" "isHaarMeasure_semiLocalHaar"
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

theorem measurableMul_GL : MeasurableMul₂ G := inferInstance
theorem measurableInv_GL : MeasurableInv G := inferInstance

attribute [local instance] measurableMul_GL measurableInv_GL

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) E) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

local notation "μG" => AutomorphicForm.semiLocalHaar K L v
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v
local notation "𝒪" => AutomorphicForm.semiLocalIntegers K L v

section Charts

open scoped Classical

def tm (p : Q) : Matrix (Fin 2) (Fin 2) E := !![p.1, 0; 0, p.2]

theorem det_tm (p : Q) : (tm p).det = p.1 * p.2 := by
  simp [tm, Matrix.det_fin_two_of]

theorem continuous_tm : Continuous (tm : Q → Matrix (Fin 2) (Fin 2) E) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_snd

theorem continuous_det_tm : Continuous fun p : Q => (tm p).det := continuous_tm.matrix_det

def goodT : Set Q := {p | IsUnit (tm p).det}

theorem mem_goodT_iff (p : Q) : p ∈ goodT ↔ IsUnit p.1 ∧ IsUnit p.2 := by
  simp only [goodT, mem_setOf_eq, det_tm, IsUnit.mul_iff]

theorem isOpen_goodT : IsOpen (goodT : Set Q) :=
  (isOpen_units (K := K) (L := L) (v := v)).preimage continuous_det_tm

theorem one_mem_goodT : ((1, 1) : Q) ∈ goodT := by
  rw [mem_goodT_iff]; exact ⟨isUnit_one, isUnit_one⟩

def uGL (p : Q) : G := if h : IsUnit (tm p).det then Matrix.GeneralLinearGroup.mk'' (tm p) h else 1

theorem uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : uGL p = Matrix.GeneralLinearGroup.mk'' (tm p) h := by
  simp [uGL, h]

theorem coe_uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) = tm p := by
  rw [uGL_of_mem h]; rfl

theorem uGL_of_not {p : Q} (h : ¬ IsUnit (tm p).det) : uGL p = 1 := by
  simp [uGL, h]

theorem coe_uGL_inv_of_mem {p : Q} (h : IsUnit (tm p).det) :
    (((uGL p)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = Ring.inverse (tm p).det • (tm p).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL_of_mem h, Matrix.inv_def]

theorem continuous_uGL_restrict : Continuous ((goodT : Set Q).restrict (uGL : Q → G)) := by
  have hent : ∀ i j, Continuous fun x : (goodT : Set Q) => tm (x : Q) i j := fun i j =>
    (continuous_tm.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (goodT : Set Q) => (((goodT : Set Q).restrict uGL x : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => tm (x : Q) i j := by
      funext x; rw [show (goodT : Set Q).restrict uGL x = uGL x from rfl, coe_uGL_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (goodT : Set Q) =>
        ((((goodT : Set Q).restrict uGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det * (tm (x : Q)).adjugate i j := by
      funext x
      rw [show (goodT : Set Q).restrict uGL x = uGL x from rfl, coe_uGL_inv_of_mem x.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    have hdet : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).det :=
      continuous_det_tm.comp continuous_subtype_val
    have hri : Continuous fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det :=
      continuous_ringInverse_comp hdet fun x => x.2
    refine hri.mul ?_
    have hadj : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).adjugate :=
      (continuous_tm.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

theorem uGL_mul_uGL {a q : Q} (ha : a ∈ goodT) (hq : q ∈ goodT) :
    uGL a * uGL q = uGL (a.1 * q.1, a.2 * q.2) := by
  have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∈ goodT := by
    rw [mem_goodT_iff] at ha hq ⊢
    exact ⟨ha.1.mul hq.1, ha.2.mul hq.2⟩
  apply Units.ext
  rw [Units.val_mul, coe_uGL_of_mem (show IsUnit (tm a).det from ha),
    coe_uGL_of_mem (show IsUnit (tm q).det from hq),
    coe_uGL_of_mem (show IsUnit (tm ((a.1 * q.1, a.2 * q.2) : Q)).det from haq)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

def nGL (x : E) : G := AutomorphicForm.unipotentGL2 x

theorem coe_nGL (x : E) : ((nGL x : G) : Matrix (Fin 2) (Fin 2) E) = !![1, x; 0, 1] := rfl

theorem nGL_add (x y : E) : nGL (x + y) = nGL x * nGL y := AutomorphicForm.unipotentGL2_add x y

theorem nGL_zero : nGL (0 : E) = 1 := AutomorphicForm.unipotentGL2_zero

theorem nGL_neg (x : E) : nGL (-x) = (nGL x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← nGL_add, neg_add_cancel, nGL_zero]

theorem coe_nGL_inv (x : E) : (((nGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![1, -x; 0, 1] := by
  rw [← nGL_neg]; rfl

theorem continuous_nGL : Continuous (nGL : E → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_nGL]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  · simp only [coe_nGL_inv]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_neg
    · exact continuous_const
    · exact continuous_const

theorem nGL_mul_uGL {q : Q} (hq : q ∈ goodT) (c : E) :
    nGL c * uGL q = uGL q * nGL (Ring.inverse q.1 * c * q.2) := by
  have h1 : IsUnit q.1 := ((mem_goodT_iff q).1 hq).1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm q).det from hq), coe_nGL, coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ h1, one_mul]

def ι (z : Q × E) : G := uGL z.1 * nGL z.2

theorem ι_apply (p : Q) (x : E) : ι (p, x) = uGL p * nGL x := rfl

theorem coe_ι_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = !![p.1, p.1 * x; 0, p.2] := by
  rw [ι_apply, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm p).det from hp), coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_ι_inv_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
  have h1 : IsUnit p.1 := ((mem_goodT_iff p).1 hp).1
  have h2 : IsUnit p.2 := ((mem_goodT_iff p).1 hp).2

  have hmul : ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] = 1 := by
    rw [coe_ι_of_mem hp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Ring.mul_inverse_cancel _ h1, Ring.mul_inverse_cancel _ h2]
    ring_nf
  have hinv : (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) * ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E)
      = (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) *
          (((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
            !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2]) := by rw [hmul, mul_one]
    _ = !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
          rw [← mul_assoc, hinv, one_mul]

end Charts

section Kgroup

theorem intg_zero_mem : (0 : E) ∈ 𝒪 := AutomorphicForm.zero_mem_semiLocalIntegers K L v
theorem intg_one_mem : (1 : E) ∈ 𝒪 := AutomorphicForm.one_mem_semiLocalIntegers K L v

theorem intg_add_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a + b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, map_add _ _ _⟩

theorem intg_mul_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a * b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, map_mul _ _ _⟩

theorem intg_neg_mem {a : E} (ha : a ∈ 𝒪) : -a ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; exact ⟨-x, map_neg _ _⟩

theorem isCompact_intg : IsCompact (𝒪 : Set E) := AutomorphicForm.isCompact_semiLocalIntegers K L v
theorem isOpen_intg : IsOpen (𝒪 : Set E) := AutomorphicForm.isOpen_semiLocalIntegers K L v

theorem mem_K_iff (g : G) : g ∈ 𝒦 ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪) ∧
    ∀ i j, ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪 := Iff.rfl

theorem matrix_mul_mem {A B : Matrix (Fin 2) (Fin 2) E} (hA : ∀ i j, A i j ∈ 𝒪) (hB : ∀ i j, B i j ∈ 𝒪)
    (i j : Fin 2) : (A * B) i j ∈ 𝒪 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact intg_add_mem (intg_mul_mem (hA _ _) (hB _ _)) (intg_mul_mem (hA _ _) (hB _ _))

theorem K_mul_mem {g h : G} (hg : g ∈ 𝒦) (hh : h ∈ 𝒦) : g * h ∈ 𝒦 := by
  rw [mem_K_iff] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]; exact matrix_mul_mem hg.1 hh.1 i j
  · rw [mul_inv_rev, Units.val_mul]; exact matrix_mul_mem hh.2 hg.2 i j

theorem K_inv_mem {g : G} (hg : g ∈ 𝒦) : g⁻¹ ∈ 𝒦 := by
  rw [mem_K_iff] at hg ⊢
  refine ⟨hg.2, fun i j => ?_⟩
  rw [inv_inv]; exact hg.1 i j

theorem K_one_mem : (1 : G) ∈ 𝒦 := AutomorphicForm.one_mem_semiLocalIntegralSet K L v

def Kgrp : Subgroup G where
  carrier := 𝒦
  mul_mem' := K_mul_mem
  one_mem' := K_one_mem
  inv_mem' := K_inv_mem

theorem mem_Kgrp {g : G} : g ∈ (Kgrp : Subgroup G) ↔ g ∈ 𝒦 := Iff.rfl

theorem K_mul_mem_iff_right {g k : G} (hk : k ∈ 𝒦) : g * k ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_right (mem_Kgrp.2 hk)

theorem K_mul_mem_iff_left {g k : G} (hk : k ∈ 𝒦) : k * g ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_left (mem_Kgrp.2 hk)

theorem K_inv_mem_iff {g : G} : g⁻¹ ∈ 𝒦 ↔ g ∈ 𝒦 := (Kgrp (K := K) (L := L) (v := v)).inv_mem_iff

theorem isOpen_K : IsOpen (𝒦 : Set G) := AutomorphicForm.isOpen_semiLocalIntegralSet K L v
theorem isCompact_K : IsCompact (𝒦 : Set G) := AutomorphicForm.isCompact_semiLocalIntegralSet K L v

end Kgroup

section Iwasawa

theorem exists_integral_mul_inv_upper {R Γ₀ : Type*} [Field R] [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (g : GL (Fin 2) R) :
    ∃ k : GL (Fin 2) R, (∀ i j, w ((k : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1) ∧
      (∀ i j, w (((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1) ∧
      ((g * k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  set γ : R := (g : Matrix (Fin 2) (Fin 2) R) 1 0 with hγ
  set δ : R := (g : Matrix (Fin 2) (Fin 2) R) 1 1 with hδ
  have hdet : (g : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hne : ¬ (γ = 0 ∧ δ = 0) := by
    rintro ⟨h1, h2⟩
    apply hdet
    rw [Matrix.det_fin_two, ← hγ, ← hδ, h1, h2, mul_zero, mul_zero, sub_zero]
  rcases le_total (w γ) (w δ) with h | h
  ·
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact hne ⟨h, h0⟩
    set t : R := γ / δ with ht
    have hwt : w t ≤ 1 := by
      rw [ht, map_div₀]
      exact div_le_one_of_le₀ h zero_le
    let k : GL (Fin 2) R :=
      ⟨!![1, 0; t, 1], !![1, 0; -t, 1],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨k, fun i j => ?_, fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [k, hwt]
    · show w ((!![1, 0; -t, 1] : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hwt]
    · show ((g : Matrix (Fin 2) (Fin 2) R) * !![1, 0; -t, 1]) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hγ, ← hδ, ht]
      field_simp
      ring
  ·
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact hne ⟨h0, h⟩
    set t : R := δ / γ with ht
    have hwt : w t ≤ 1 := by
      rw [ht, map_div₀]
      exact div_le_one_of_le₀ h zero_le
    let k : GL (Fin 2) R :=
      ⟨!![0, 1; 1, t], !![-t, 1; 1, 0],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨k, fun i j => ?_, fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [k, hwt]
    · show w ((!![-t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hwt]
    · show ((g : Matrix (Fin 2) (Fin 2) R) * !![-t, 1; 1, 0]) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hγ, ← hδ, ht]
      field_simp
      ring

local notation "W" => HeightOneSpectrum.Extension (𝓞 L) v

def π (w : W) : E →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w' : W => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
      E →+* Π w' : W, w'.1.adicCompletion L)

theorem π_apply (w : W) (x : E) :
    π w x = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w := rfl

theorem π_symm_apply (w : W) (y : Π w' : W, w'.1.adicCompletion L) :
    π (K := K) (L := L) (v := v) w ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm y) =
      y w := by
  rw [π_apply, AlgEquiv.apply_symm_apply]

theorem eq_of_forall_π_eq {x y : E} (h : ∀ w : W, π w x = π w y) : x = y := by
  apply (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective
  funext w; exact h w

theorem isUnit_of_forall_π_ne_zero {x : E} (h : ∀ w : W, π w x ≠ 0) : IsUnit x := by
  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with he
  have hu : IsUnit (e x) := by
    rw [Pi.isUnit_iff]
    intro w; exact isUnit_iff_ne_zero.2 (h w)
  have := hu.map e.symm
  rwa [AlgEquiv.symm_apply_apply] at this

theorem mem_K_iff_forall_π (g : G) :
    g ∈ 𝒦 ↔ ∀ w : W, Matrix.GeneralLinearGroup.map (π w) g ∈ AutomorphicForm.localIntegralSet L w.1 := by
  haveI : Finite W := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype W := Fintype.ofFinite W
  exact (AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    K L v).1 g

theorem GLmap_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) i j =
      f ((g : Matrix (Fin 2) (Fin 2) R) i j) := rfl

theorem iwasawa (g : G) : ∃ a : Q, a ∈ goodT ∧ ∃ c : E, ∃ k : G, k ∈ 𝒦 ∧ g = uGL a * nGL c * k := by
  classical
  haveI : Finite W := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v

  have hloc : ∀ w : W, ∃ kw : GL (Fin 2) (w.1.adicCompletion L),
      kw ∈ AutomorphicForm.localIntegralSet L w.1 ∧
      ((Matrix.GeneralLinearGroup.map (π w) g * kw⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 := by
    intro w
    obtain ⟨kw, h1, h2, h3⟩ := exists_integral_mul_inv_upper (Valued.v (R := w.1.adicCompletion L))
      (Matrix.GeneralLinearGroup.map (π w) g)
    refine ⟨kw, ?_, h3⟩
    rw [AutomorphicForm.mem_localIntegralSet]
    exact ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 i j),
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h2 i j)⟩
  choose kw hkw hup using hloc

  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with he
  let M : Matrix (Fin 2) (Fin 2) (Π w : W, w.1.adicCompletion L) := fun i j w =>
    ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  let M' : Matrix (Fin 2) (Fin 2) (Π w : W, w.1.adicCompletion L) := fun i j w =>
    (((kw w)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  have hMM' : M * M' = 1 := by
    ext i j w : 2
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) => m i j)
      (show ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) * (((kw w)⁻¹ : GL (Fin 2) _) : Matrix _ _ _) = 1
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    simpa [M, M', Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using h
  have hM'M : M' * M = 1 := by
    ext i j w : 2
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) => m i j)
      (show (((kw w)⁻¹ : GL (Fin 2) _) : Matrix _ _ _) * ((kw w : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) = 1
        by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    simpa [M, M', Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using h
  let kPi : GL (Fin 2) (Π w : W, w.1.adicCompletion L) := ⟨M, M', hMM', hM'M⟩
  let k : G := Matrix.GeneralLinearGroup.map (e.symm : (Π w : W, w.1.adicCompletion L) →+* E) kPi
  have hkw' : ∀ w : W, Matrix.GeneralLinearGroup.map (π w) k = kw w := by
    intro w
    apply Units.ext
    ext i j : 1
    rw [GLmap_apply]
    show π w (e.symm (M i j)) = _
    rw [he, π_symm_apply]
  have hk : k ∈ 𝒦 := by
    rw [mem_K_iff_forall_π]
    intro w; rw [hkw' w]; exact hkw w

  obtain ⟨b, hb⟩ : ∃ b : G, g * k⁻¹ = b := ⟨_, rfl⟩
  have hb10 : (b : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    apply eq_of_forall_π_eq
    intro w
    rw [map_zero, ← GLmap_apply (π w) b 1 0, ← hb, map_mul, map_inv, hkw' w]
    exact hup w
  have hbdet : IsUnit ((b : Matrix (Fin 2) (Fin 2) E) 0 0 * (b : Matrix (Fin 2) (Fin 2) E) 1 1) := by
    have h1 : IsUnit (b : Matrix (Fin 2) (Fin 2) E).det :=
      ⟨Matrix.GeneralLinearGroup.det b, Matrix.GeneralLinearGroup.val_det_apply b⟩
    rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero] at h1
    exact h1
  set a : Q := ((b : Matrix (Fin 2) (Fin 2) E) 0 0, (b : Matrix (Fin 2) (Fin 2) E) 1 1) with ha
  have hagood : a ∈ goodT := by
    rw [mem_goodT_iff]; exact IsUnit.mul_iff.1 hbdet
  set c : E := Ring.inverse ((b : Matrix (Fin 2) (Fin 2) E) 0 0) * (b : Matrix (Fin 2) (Fin 2) E) 0 1 with hc
  have hbeq : b = uGL a * nGL c := by
    apply Units.ext
    rw [Units.val_mul, coe_uGL_of_mem (show IsUnit (tm a).det from hagood), coe_nGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two, ha, hb10]
    rw [hc, ← mul_assoc, Ring.mul_inverse_cancel _ (IsUnit.mul_iff.1 hbdet).1, one_mul]
  refine ⟨a, hagood, c, k, hk, ?_⟩
  rw [← hbeq, ← hb, inv_mul_cancel_right]

end Iwasawa

section TwShift

variable (σ : L ≃ₐ[K] L)

theorem uGL_eq_diagUnits2 {a : Q} (ha : a ∈ goodT) :
    uGL a = diagUnits2 ((mem_goodT_iff a).1 ha).1.unit ((mem_goodT_iff a).1 ha).2.unit := by
  apply Units.ext
  rw [coe_uGL_of_mem ha, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, IsUnit.unit_spec]

theorem sigmaGL_nGL (ξ : E) :
    AutomorphicForm.sigmaGL K L F σ (nGL ξ) = nGL (AutomorphicForm.sigmaTensor K L F σ ξ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, nGL, AutomorphicForm.unipotentGL2]

def Theta (z : (Fˣ × Fˣ) × (E × G)) : G :=
  (AutomorphicForm.sigmaGL K L F σ z.2.2)⁻¹ *
    ((nGL (AutomorphicForm.sigmaTensor K L F σ z.2.1))⁻¹ *
      AutomorphicForm.toTensorGL K L F (diagUnits2 z.1.1 z.1.2) * nGL (AutomorphicForm.sigmaTensor K L F σ z.2.1)) *
    AutomorphicForm.sigmaGL K L F σ z.2.2

theorem includeRight_eq_smul_one (r : F) :
    (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E) = r • (1 : E) := by
  show (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) r = r • (1 : E)
  exact Algebra.algebraMap_eq_smul_one r

theorem continuous_iotaE : Continuous fun r : F => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E) := by
  have : (fun r : F => (Algebra.TensorProduct.includeRight (R := K) (A := L) r : E)) = fun r : F => r • (1 : E) :=
    funext (includeRight_eq_smul_one (K := K) (L := L) (v := v))
  rw [this]
  first | fun_prop | exact continuous_id.smul continuous_const

theorem continuous_toTensorGL_diagUnits2 :
    Continuous fun d : Fˣ × Fˣ => AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2) := by
  have hι := continuous_iotaE (K := K) (L := L) (v := v)
  apply continuous_GL_of
  · intro i j
    fin_cases i <;> fin_cases j
    · exact (hι.comp (Units.continuous_val.comp continuous_fst)).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (continuous_const (y := (0 : E))).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (continuous_const (y := (0 : E))).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (hι.comp (Units.continuous_val.comp continuous_snd)).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  · intro i j
    have hinv : ∀ d : Fˣ × Fˣ, (AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2))⁻¹ =
        AutomorphicForm.toTensorGL K L F (diagUnits2 d.1⁻¹ d.2⁻¹) := by
      intro d
      rw [← map_inv, TwShiftDiag.diagUnits2_inv]
    simp_rw [hinv]
    fin_cases i <;> fin_cases j
    · exact (hι.comp (Units.continuous_coe_inv.comp continuous_fst)).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (continuous_const (y := (0 : E))).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (continuous_const (y := (0 : E))).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · exact (hι.comp (Units.continuous_coe_inv.comp continuous_snd)).congr fun d => by
        simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem continuous_Theta [FiniteDimensional K L] : Continuous (Theta (K := K) (L := L) (v := v) σ) := by
  have hσG := TwShiftTop.continuous_sigmaGL K L F σ
  have hσE := TwShiftTop.continuous_sigmaTensor K L F σ
  unfold Theta
  refine ((hσG.comp (continuous_snd.comp continuous_snd)).inv.mul ?_).mul (hσG.comp (continuous_snd.comp continuous_snd))
  refine ((continuous_nGL.comp (hσE.comp (continuous_fst.comp continuous_snd))).inv.mul ?_).mul
    (continuous_nGL.comp (hσE.comp (continuous_fst.comp continuous_snd)))
  exact (continuous_toTensorGL_diagUnits2 (K := K) (L := L) (v := v)).comp continuous_fst

theorem Theta_one (ξ : E) (k : G) : Theta (K := K) (L := L) (v := v) σ (((1 : Fˣ), (1 : Fˣ)), (ξ, k)) = 1 := by
  unfold Theta
  simp only [TwShiftDiag.diagUnits2_one, map_one, mul_one, inv_mul_cancel]

theorem exists_nhds_forall_Theta_mem [FiniteDimensional K L] {W : Set G} (hWo : IsOpen W) (h1W : (1 : G) ∈ W)
    {Ξ : Set E} (hΞ : IsCompact Ξ) :
    ∃ D ∈ nhds ((1 : Fˣ), (1 : Fˣ)), ∀ d ∈ D, ∀ ξ ∈ Ξ, ∀ k ∈ 𝒦, Theta (K := K) (L := L) (v := v) σ (d, (ξ, k)) ∈ W := by
  have hcont := continuous_Theta (K := K) (L := L) (v := v) σ
  have hopen : IsOpen ((Theta (K := K) (L := L) (v := v) σ) ⁻¹' W) := hWo.preimage hcont
  have hsub : ({((1 : Fˣ), (1 : Fˣ))} : Set (Fˣ × Fˣ)) ×ˢ (Ξ ×ˢ 𝒦) ⊆ (Theta (K := K) (L := L) (v := v) σ) ⁻¹' W := by
    rintro ⟨d, ⟨ξ, k⟩⟩ ⟨hd, -⟩
    have hd' : d = ((1 : Fˣ), (1 : Fˣ)) := hd
    subst hd'
    show Theta (K := K) (L := L) (v := v) σ (((1 : Fˣ), (1 : Fˣ)), (ξ, k)) ∈ W
    rw [Theta_one]; exact h1W
  obtain ⟨u, w, hu, -, h1u, hsub2, huw⟩ :=
    generalized_tube_lemma isCompact_singleton (hΞ.prod isCompact_K) hopen hsub
  refine ⟨u, hu.mem_nhds (h1u (Set.mem_singleton _)), fun d hd ξ hξ k hk => ?_⟩
  exact huw (Set.mk_mem_prod hd (hsub2 (Set.mk_mem_prod hξ hk)))

theorem conj_shift_eq_Theta (a₁ a₂ : Eˣ) (ξ : E) (k : G) (d₁ d₂ : Fˣ) :
    (AutomorphicForm.sigmaGL K L F σ (diagUnits2 a₁ a₂ * nGL ξ * k))⁻¹ *
        AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
        AutomorphicForm.sigmaGL K L F σ (diagUnits2 a₁ a₂ * nGL ξ * k) =
      Theta (K := K) (L := L) (v := v) σ ((d₁, d₂), (ξ, k)) := by
  unfold Theta
  simp only [map_mul, sigmaGL_nGL, TwWindow.sigmaGL_diagUnits2]
  set Pm := diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₁)
    (Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₂) with hPm
  set Qm := nGL (K := K) (L := L) (v := v) (AutomorphicForm.sigmaTensor K L F σ ξ) with hQm
  set Rm := AutomorphicForm.sigmaGL K L F σ k with hRm
  set Dd := AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) with hDd
  have hcomm : Pm⁻¹ * Dd * Pm = Dd := by
    rw [hDd, TwWindow.toTensorGL_diagUnits2_iotaU, hPm, TwShiftDiag.diagUnits2_inv,
      TwShiftDiag.diagUnits2_mul_diagUnits2, TwShiftDiag.diagUnits2_mul_diagUnits2]
    have e1 : ∀ s t : Eˣ, s⁻¹ * t * s = t := fun s t => by rw [mul_comm (s⁻¹ * t) s, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [e1, e1]
  calc (Pm * Qm * Rm)⁻¹ * Dd * (Pm * Qm * Rm) = Rm⁻¹ * (Qm⁻¹ * (Pm⁻¹ * Dd * Pm) * Qm) * Rm := by
        simp only [mul_inv_rev, mul_assoc]
    _ = Rm⁻¹ * (Qm⁻¹ * Dd * Qm) * Rm := by rw [hcomm]

end TwShift

section TwShiftMain

variable (σ : L ≃ₐ[K] L)

private def _root_.KcSemiLocalIwasawaHaar.NmU (x : Eˣ) : Eˣ :=
  ((List.range (Module.finrank K L)).map fun i =>
    (⇑(Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E)))^[i] x).prod

p2m_export "KcSemiLocalIwasawaHaar" "NmU"
theorem unitsMap_toMonoidHom_eq :
    Units.map (AutomorphicForm.sigmaTensor K L F σ).toMonoidHom =
      Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) := rfl

theorem NmU_eq_TwXi (x : Eˣ) : NmU (K := K) (L := L) (v := v) σ x = TwXi.NmU K L σ v x := rfl

theorem xi_bound [FiniteDimensional K L] (Ω' : Set G) (hΩ' : IsCompact Ω') (Cc : Set Fˣ) (hCc : IsCompact Cc)
    (h1 : (1 : Fˣ) ∉ Cc) :
    ∃ Ξ : Set E, IsCompact Ξ ∧ ∀ (p q : Eˣ) (ξ : E) (c : Fˣ), c ∈ Cc →
      NmU (K := K) (L := L) (v := v) σ (q * p⁻¹) = TwWindow.iotaU K L v c →
      diagUnits2 p q * nGL (AutomorphicForm.sigmaTensor K L F σ ξ - ((q * p⁻¹ : Eˣ) : E) * ξ) ∈ Ω' → ξ ∈ Ξ := by
  obtain ⟨Ξ, hΞ, h⟩ := TwXi.exists_isCompact_forall_xi_mem K L σ v Ω' hΩ' Cc hCc h1
  refine ⟨Ξ, hΞ, fun p q ξ c hc hN hmem => h p q ξ c hc ?_ hmem⟩
  have h' := congrArg (Units.val : Eˣ → E) hN
  rw [NmU_eq_TwXi, TwXi.coe_NmU] at h'
  exact h'

private theorem _root_.KcSemiLocalIwasawaHaar.NmU_mul (x y : Eˣ) :
    NmU (K := K) (L := L) (v := v) σ (x * y) = NmU (K := K) (L := L) (v := v) σ x * NmU (K := K) (L := L) (v := v) σ y := by
  rw [NmU_eq_TwXi, NmU_eq_TwXi, NmU_eq_TwXi]
  exact TwXi.NmU_mul K L σ v x y

p2m_export "KcSemiLocalIwasawaHaar" "NmU_mul"
theorem NmU_one : NmU (K := K) (L := L) (v := v) σ 1 = 1 := by
  unfold NmU
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact iterate_map_one _ i

theorem NmU_inv (x : Eˣ) :
    NmU (K := K) (L := L) (v := v) σ x⁻¹ = (NmU (K := K) (L := L) (v := v) σ x)⁻¹ := by
  have h := NmU_mul (K := K) (L := L) (v := v) σ x⁻¹ x
  rw [inv_mul_cancel, NmU_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem _root_.KcSemiLocalIwasawaHaar.NmU_sigma_mul_inv [FiniteDimensional K L] (z : Eˣ) :
    NmU (K := K) (L := L) (v := v) σ (Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) z * z⁻¹) = 1 := by
  rw [NmU_eq_TwXi]
  exact TwXi.NmU_sigma_mul_inv K L σ v z

p2m_export "KcSemiLocalIwasawaHaar" "NmU_sigma_mul_inv"
theorem NmU_iotaU (c : Fˣ) :
    NmU (K := K) (L := L) (v := v) σ (TwWindow.iotaU K L v c) = TwWindow.iotaU K L v (c ^ Module.finrank K L) := by
  have h := TwWindow.prod_iterate_mul_fixed K L v
    (Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E)) 1 (TwWindow.iotaU K L v c)
    (TwWindow.sigmaU_iotaU K L σ v c) (Module.finrank K L)
  have h1 : NmU (K := K) (L := L) (v := v) σ (1 * TwWindow.iotaU K L v c) =
      NmU (K := K) (L := L) (v := v) σ 1 * TwWindow.iotaU K L v c ^ Module.finrank K L := h
  rw [one_mul, NmU_one, one_mul, ← map_pow] at h1
  exact h1

theorem NmU_mul_sigma_div [FiniteDimensional K L] (x z : Eˣ) :
    NmU (K := K) (L := L) (v := v) σ (x * Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) z * z⁻¹) =
      NmU (K := K) (L := L) (v := v) σ x := by
  rw [mul_assoc, NmU_mul, NmU_sigma_mul_inv, mul_one]

theorem NmU_of_normString_eq (α β : Eˣ) (a b : Fˣ)
    (hN : AutomorphicForm.normString K L F σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L F (diagUnits2 a b)) :
    NmU (K := K) (L := L) (v := v) σ α = TwWindow.iotaU K L v a ∧
      NmU (K := K) (L := L) (v := v) σ β = TwWindow.iotaU K L v b := by
  rw [NmU_eq_TwXi, NmU_eq_TwXi]
  exact TwXi.NmU_eq_of_normString_diagUnits2 K L σ v hN

theorem isCompact_units_preimage_closedBall (c₀ : Fˣ) {r : ℝ} (hr : r < ‖(c₀ : F)‖) :
    IsCompact ((Units.val : Fˣ → F) ⁻¹' Metric.closedBall (c₀ : F) r) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hsub : Metric.closedBall (c₀ : F) r ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg] at hx
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  rw [Set.inter_eq_left.2 hsub]
  exact isCompact_closedBall _ _

theorem twShift_main [FiniteDimensional K L] (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (a₀ b₀ : Fˣ) (hab : a₀ ≠ b₀) :
    ∃ U ∈ nhds (a₀, b₀), ∃ D ∈ nhds ((1 : Fˣ), (1 : Fˣ)),
      ∀ ab : Fˣ × Fˣ, ab ∈ U → ∀ d : Fˣ × Fˣ, d ∈ D → ∀ α β : Eˣ,
        AutomorphicForm.normString K L F σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L F (diagUnits2 ab.1 ab.2) →
        ∀ x : G, φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2)) *
            AutomorphicForm.sigmaGL K L F σ x) =
          φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) := by
  classical
  obtain ⟨hlc, hcs⟩ := hφ
  have hσG := TwShiftTop.continuous_sigmaGL K L F σ

  obtain ⟨W, hWo, h1W, hW⟩ := IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport φ hlc hcs

  set Ω' : Set G := (fun p : G × G => p.1 * p.2 * (AutomorphicForm.sigmaGL K L F σ p.1)⁻¹) '' ((𝒦 : Set G) ×ˢ tsupport φ)
    with hΩ'def
  have hΩ'c : IsCompact Ω' := by
    refine (isCompact_K.prod hcs).image ?_
    exact (continuous_fst.mul continuous_snd).mul (hσG.comp continuous_fst).inv
  have hΩ'mem : ∀ k ∈ (𝒦 : Set G), ∀ B : G,
      φ (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 → B ∈ Ω' := by
    intro k hk B hB
    refine ⟨(k, k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k), Set.mk_mem_prod hk (subset_tsupport _ hB), ?_⟩
    show k * (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) * (AutomorphicForm.sigmaGL K L F σ k)⁻¹ = B
    group

  set c₀ : Fˣ := b₀ * a₀⁻¹ with hc₀
  have hc₀1 : (c₀ : F) ≠ 1 := by
    intro h
    apply hab
    have h' : c₀ = 1 := Units.val_eq_one.1 h
    rw [hc₀, mul_inv_eq_one] at h'
    exact h'.symm
  set r : ℝ := min (‖(c₀ : F) - 1‖ / 2) (‖(c₀ : F)‖ / 2) with hr
  have hr0 : 0 < r := by
    have h1 : 0 < ‖(c₀ : F) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hc₀1)
    have h2 : 0 < ‖(c₀ : F)‖ := norm_pos_iff.2 c₀.ne_zero
    rw [hr]; positivity
  have hrlt : r < ‖(c₀ : F)‖ := by
    have h2 : 0 < ‖(c₀ : F)‖ := norm_pos_iff.2 c₀.ne_zero
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set Cc : Set Fˣ := (Units.val : Fˣ → F) ⁻¹' Metric.closedBall (c₀ : F) r with hCc
  have hCcc : IsCompact Cc := isCompact_units_preimage_closedBall c₀ hrlt
  have h1Cc : (1 : Fˣ) ∉ Cc := by
    intro h
    have h' : ‖(1 : F) - (c₀ : F)‖ ≤ r := by
      simpa [hCc, Metric.mem_closedBall, dist_eq_norm] using h
    have h1 : 0 < ‖(c₀ : F) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hc₀1)
    rw [norm_sub_rev] at h'
    have : r ≤ ‖(c₀ : F) - 1‖ / 2 := min_le_left _ _
    linarith

  obtain ⟨Ξ, hΞc, hΞ⟩ := xi_bound (K := K) (L := L) (v := v) σ Ω' hΩ'c Cc hCcc h1Cc
  obtain ⟨D₁, hD₁, hΘ⟩ := exists_nhds_forall_Theta_mem (K := K) (L := L) (v := v) σ hWo h1W hΞc

  set sc : (Fˣ × Fˣ) × (Fˣ × Fˣ) → Fˣ := fun z =>
    z.1.2 * z.2.2 ^ Module.finrank K L * (z.1.1 * z.2.1 ^ Module.finrank K L)⁻¹ with hsc
  have hsc_cont : Continuous sc := by
    rw [hsc]
    exact ((continuous_snd.comp continuous_fst).mul ((continuous_snd.comp continuous_snd).pow _)).mul
      ((continuous_fst.comp continuous_fst).mul ((continuous_fst.comp continuous_snd).pow _)).inv
  have hsc0 : sc ((a₀, b₀), ((1 : Fˣ), (1 : Fˣ))) = c₀ := by
    simp [hsc, hc₀]
  have hCcnhds : Cc ∈ nhds c₀ := by
    rw [hCc]
    refine Units.continuous_val.continuousAt.preimage_mem_nhds ?_
    exact Metric.closedBall_mem_nhds _ hr0
  have hpre : sc ⁻¹' Cc ∈ nhds ((a₀, b₀), ((1 : Fˣ), (1 : Fˣ))) :=
    hsc_cont.continuousAt.preimage_mem_nhds (by rw [hsc0]; exact hCcnhds)
  obtain ⟨U, hU, D₀, hD₀, hUD₀⟩ := mem_nhds_prod_iff.1 hpre
  refine ⟨U, hU, D₀ ∩ D₁, Filter.inter_mem hD₀ hD₁, ?_⟩
  rintro ab hab d ⟨hd₀, hd₁⟩ α β hN x
  have h11 : ((1 : Fˣ), (1 : Fˣ)) ∈ D₀ := mem_of_mem_nhds hD₀
  have hc_mem : ∀ d' ∈ D₀, sc (ab, d') ∈ Cc := fun d' hd' => hUD₀ (Set.mk_mem_prod hab hd')

  obtain ⟨aq, haq, ξ, k, hk, hx⟩ := iwasawa x
  rw [uGL_eq_diagUnits2 haq] at hx
  set a₁ : Eˣ := ((mem_goodT_iff aq).1 haq).1.unit with ha₁
  set a₂ : Eˣ := ((mem_goodT_iff aq).1 haq).2.unit with ha₂
  obtain ⟨hNα, hNβ⟩ := NmU_of_normString_eq (K := K) (L := L) (v := v) σ α β ab.1 ab.2 hN

  have hvanish : ξ ∉ Ξ → ∀ (α' β' : Eˣ) (c : Fˣ), c ∈ Cc →
      NmU (K := K) (L := L) (v := v) σ β' * (NmU (K := K) (L := L) (v := v) σ α')⁻¹ = TwWindow.iotaU K L v c →
      φ (x⁻¹ * diagUnits2 α' β' * AutomorphicForm.sigmaGL K L F σ x) = 0 := by
    intro hξ α' β' c hc hNc
    by_contra hne
    apply hξ
    rw [hx] at hne
    rw [show (nGL ξ : G) = AutomorphicForm.unipotentGL2 ξ from rfl,
      AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul K L F σ α' β' a₁ a₂ ξ k,
      unitsMap_toMonoidHom_eq] at hne
    set p : Eˣ := α' * Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₁ * a₁⁻¹ with hp
    set q : Eˣ := β' * Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₂ * a₂⁻¹ with hq
    have hB := hΩ'mem k hk (diagUnits2 p q * nGL (AutomorphicForm.sigmaTensor K L F σ ξ - ((q * p⁻¹ : Eˣ) : E) * ξ)) hne
    refine hΞ p q ξ c hc ?_ hB

    rw [NmU_mul, NmU_inv, hq, hp, NmU_mul_sigma_div, NmU_mul_sigma_div]
    exact hNc
  by_cases hξ : ξ ∈ Ξ
  ·
    have hsplit : x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2)) *
        AutomorphicForm.sigmaGL K L F σ x =
        (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) *
          ((AutomorphicForm.sigmaGL K L F σ x)⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2) *
            AutomorphicForm.sigmaGL K L F σ x) := by
      group
    rw [hsplit]
    have hT : (AutomorphicForm.sigmaGL K L F σ x)⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2) *
        AutomorphicForm.sigmaGL K L F σ x = Theta (K := K) (L := L) (v := v) σ ((d.1, d.2), (ξ, k)) := by
      rw [hx]; exact conj_shift_eq_Theta (K := K) (L := L) (v := v) σ a₁ a₂ ξ k d.1 d.2
    rw [hT]
    exact (hW _ _ (hΘ (d.1, d.2) hd₁ ξ hξ k hk)).1
  ·
    have h0 : φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) = 0 := by
      refine hvanish hξ α β (sc (ab, ((1 : Fˣ), (1 : Fˣ)))) (hc_mem _ h11) ?_
      rw [hNα, hNβ, ← map_inv, ← map_mul]
      congr 1
      simp [hsc]
    have h0' : φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d.1 d.2)) *
        AutomorphicForm.sigmaGL K L F σ x) = 0 := by
      rw [TwWindow.diagUnits2_mul_toTensorGL_diagUnits2]
      refine hvanish hξ _ _ (sc (ab, d)) (hc_mem _ hd₀) ?_
      rw [NmU_mul, NmU_mul, hNα, hNβ, NmU_iotaU, NmU_iotaU, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
    rw [h0, h0']

end TwShiftMain

section TwShiftQ

variable (σ : L ≃ₐ[K] L)

def ThetaQ (z : ((Fˣ × Fˣ) × E) × G) : G :=
  (AutomorphicForm.sigmaGL K L F σ z.2)⁻¹ *
    (AutomorphicForm.toTensorGL K L F (diagUnits2 z.1.1.1 z.1.1.2) * nGL (AutomorphicForm.sigmaTensor K L F σ z.1.2)) *
    AutomorphicForm.sigmaGL K L F σ z.2

theorem continuous_ThetaQ [FiniteDimensional K L] : Continuous (ThetaQ (K := K) (L := L) (v := v) σ) := by
  have hσG := TwShiftTop.continuous_sigmaGL K L F σ
  have hσE := TwShiftTop.continuous_sigmaTensor K L F σ
  unfold ThetaQ
  refine ((hσG.comp continuous_snd).inv.mul ?_).mul (hσG.comp continuous_snd)
  exact ((continuous_toTensorGL_diagUnits2 (K := K) (L := L) (v := v)).comp (continuous_fst.comp continuous_fst)).mul
    (continuous_nGL.comp (hσE.comp (continuous_snd.comp continuous_fst)))

theorem ThetaQ_one (k : G) : ThetaQ (K := K) (L := L) (v := v) σ ((((1 : Fˣ), (1 : Fˣ)), (0 : E)), k) = 1 := by
  unfold ThetaQ
  simp only [TwShiftDiag.diagUnits2_one, map_one, map_zero, nGL_zero, mul_one, inv_mul_cancel]

theorem exists_nhds_forall_ThetaQ_mem [FiniteDimensional K L] {W : Set G} (hWo : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ D ∈ nhds ((1 : Fˣ), (1 : Fˣ)), ∃ N ∈ nhds (0 : E), ∀ d ∈ D, ∀ m ∈ N, ∀ k ∈ 𝒦,
      ThetaQ (K := K) (L := L) (v := v) σ (((d, m)), k) ∈ W := by
  have hcont := continuous_ThetaQ (K := K) (L := L) (v := v) σ
  have hopen : IsOpen ((ThetaQ (K := K) (L := L) (v := v) σ) ⁻¹' W) := hWo.preimage hcont
  have hsub : ({(((1 : Fˣ), (1 : Fˣ)), (0 : E))} : Set ((Fˣ × Fˣ) × E)) ×ˢ (𝒦 : Set G) ⊆
      (ThetaQ (K := K) (L := L) (v := v) σ) ⁻¹' W := by
    intro z hz
    obtain ⟨hz1, -⟩ := hz
    have hz1' : z.1 = (((1 : Fˣ), (1 : Fˣ)), (0 : E)) := hz1
    show ThetaQ (K := K) (L := L) (v := v) σ z ∈ W
    have ez : z = ((((1 : Fˣ), (1 : Fˣ)), (0 : E)), z.2) := by rw [← hz1']
    rw [ez, ThetaQ_one]; exact h1W
  obtain ⟨u, w, hu, -, h1u, hsub2, huw⟩ := generalized_tube_lemma isCompact_singleton isCompact_K hopen hsub
  have hun : u ∈ nhds (((1 : Fˣ), (1 : Fˣ)), (0 : E)) := hu.mem_nhds (h1u (Set.mem_singleton _))
  obtain ⟨D, hD, N, hN, hDN⟩ := mem_nhds_prod_iff.1 hun
  refine ⟨D, hD, N, hN, fun d hd m hm k hk => ?_⟩
  exact huw (Set.mk_mem_prod (hDN (Set.mk_mem_prod hd hm)) (hsub2 hk))

theorem exists_pos_forall_iota_mul_mem {C : Set E} (hC : IsCompact C) {N : Set E} (hN : N ∈ nhds (0 : E)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ lam : F, ‖lam‖ ≤ ρ → ∀ c ∈ C,
      (Algebra.TensorProduct.includeRight (R := K) (A := L) lam : E) * c ∈ N := by
  have hι := continuous_iotaE (K := K) (L := L) (v := v)
  set Fm : F × E → E := fun z => (Algebra.TensorProduct.includeRight (R := K) (A := L) z.1 : E) * z.2 with hFm
  have hFc : Continuous Fm := (hι.comp continuous_fst).mul continuous_snd
  have hopen : IsOpen (Fm ⁻¹' interior N) := isOpen_interior.preimage hFc
  have hsub : ({(0 : F)} : Set F) ×ˢ C ⊆ Fm ⁻¹' interior N := by
    rintro ⟨l, c⟩ ⟨hl, -⟩
    have hl' : l = 0 := hl
    subst hl'
    show (Algebra.TensorProduct.includeRight (R := K) (A := L) (0 : F) : E) * c ∈ interior N
    rw [map_zero, zero_mul]
    exact mem_interior_iff_mem_nhds.2 hN
  obtain ⟨u, w, hu, -, h0u, hsub2, huw⟩ := generalized_tube_lemma isCompact_singleton hC hopen hsub
  have hun : u ∈ nhds (0 : F) := hu.mem_nhds (h0u (Set.mem_singleton _))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hun
  refine ⟨ρ / 2, by positivity, fun lam hlam c hc => interior_subset (huw (Set.mk_mem_prod (hball ?_) (hsub2 hc)))⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

theorem diagUnits2_inv_mul_nGL_mul_diagUnits2 (p q : Eˣ) (z : E) :
    (diagUnits2 p q)⁻¹ * nGL z * diagUnits2 p q = nGL (((p⁻¹ * q : Eˣ) : E) * z) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, TwShiftDiag.diagUnits2_inv, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2, coe_nGL, coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_assoc, mul_left_comm]

theorem nGL_inv_mul_diag_mul_nGL (p q : Eˣ) (z : E) :
    (nGL z)⁻¹ * diagUnits2 p q * nGL z = diagUnits2 p q * nGL (z * (1 - ((p⁻¹ * q : Eˣ) : E))) := by
  have h : (nGL z)⁻¹ * diagUnits2 p q * nGL z =
      diagUnits2 p q * ((diagUnits2 p q)⁻¹ * nGL (-z) * diagUnits2 p q) * nGL z := by
    rw [nGL_neg]; group
  rw [h, diagUnits2_inv_mul_nGL_mul_diagUnits2, mul_assoc, ← nGL_add]
  congr 2
  ring

theorem conj_shift_eq_ThetaQ (a₁ a₂ : Eˣ) (ξ : E) (k : G) (d₁ d₂ : Fˣ) :
    (AutomorphicForm.sigmaGL K L F σ (diagUnits2 a₁ a₂ * nGL ξ * k))⁻¹ *
        AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
        AutomorphicForm.sigmaGL K L F σ (diagUnits2 a₁ a₂ * nGL ξ * k) =
      ThetaQ (K := K) (L := L) (v := v) σ (((d₁, d₂),
        ξ * (1 - ((TwWindow.iotaU K L v (d₁⁻¹ * d₂) : Eˣ) : E))), k) := by
  rw [conj_shift_eq_Theta]
  unfold Theta ThetaQ
  have hfix : AutomorphicForm.sigmaTensor K L F σ ((TwWindow.iotaU K L v (d₁⁻¹ * d₂) : Eˣ) : E) =
      ((TwWindow.iotaU K L v (d₁⁻¹ * d₂) : Eˣ) : E) := by
    have h := congrArg Units.val (TwWindow.sigmaU_iotaU K L σ v (d₁⁻¹ * d₂))
    rwa [Units.coe_map] at h
  have hmid : (nGL (AutomorphicForm.sigmaTensor K L F σ ξ))⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
      nGL (AutomorphicForm.sigmaTensor K L F σ ξ) =
      AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
        nGL (AutomorphicForm.sigmaTensor K L F σ (ξ * (1 - ((TwWindow.iotaU K L v (d₁⁻¹ * d₂) : Eˣ) : E)))) := by
    rw [TwWindow.toTensorGL_diagUnits2_iotaU, nGL_inv_mul_diag_mul_nGL, map_mul, map_sub, map_one, hfix, map_mul,
      map_inv]
  simp only []
  rw [hmid]

end TwShiftQ

section TwShiftQMain

variable (σ : L ≃ₐ[K] L)

theorem norm_eq_of_norm_sub_lt' {A : Type*} [NormedField A] [IsUltrametricDist A] {a a' : A}
    (h : ‖a' - a‖ < ‖a‖) : ‖a'‖ = ‖a‖ := by
  apply le_antisymm
  · have h1 : ‖a'‖ = ‖(a' - a) + a‖ := by rw [sub_add_cancel]
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le le_rfl)
  · by_contra hlt
    push_neg at hlt
    have h2 : ‖a‖ = ‖(a - a') + a'‖ := by rw [sub_add_cancel]
    have h3 : ‖a - a'‖ < ‖a‖ := by rwa [norm_sub_rev]
    have := (IsUltrametricDist.norm_add_le_max (a - a') a')
    rw [← h2] at this
    exact absurd (this.trans_lt (max_lt h3 hlt)) (lt_irrefl _)

theorem norm_pow_sub_one_le {A : Type*} [NormedField A] [IsUltrametricDist A] {r : A} (hr : ‖r‖ ≤ 1) (n : ℕ) :
    ‖r ^ n - 1‖ ≤ ‖r - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : r ^ (n + 1) - 1 = r * (r ^ n - 1) + (r - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖r‖ * ‖r ^ n - 1‖ ≤ 1 * ‖r - 1‖ := mul_le_mul hr ih (norm_nonneg _) zero_le_one
      _ = ‖r - 1‖ := one_mul _

theorem norm_one_sub_mul_pow_eq {A : Type*} [NormedField A] [IsUltrametricDist A] {t r : A} {ρ : ℝ} (n : ℕ)
    (ht : ‖1 - t‖ < 1) (ht1 : t ≠ 1) (hρ : ρ < 1) (hr : ‖r - 1‖ ≤ ρ * ‖1 - t‖) :
    ‖1 - t * r ^ n‖ = ‖1 - t‖ := by
  have h1t : 0 < ‖1 - t‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ht1))
  have htn : ‖t‖ = 1 := by
    have : ‖t - 1‖ < ‖(1 : A)‖ := by rw [norm_sub_rev, norm_one]; exact ht
    rw [norm_eq_of_norm_sub_lt' this, norm_one]
  have hr1 : ‖r - 1‖ < 1 := by
    refine lt_of_le_of_lt hr ?_
    calc ρ * ‖1 - t‖ ≤ 1 * ‖1 - t‖ := by
          exact mul_le_mul_of_nonneg_right hρ.le (norm_nonneg _)
      _ = ‖1 - t‖ := one_mul _
      _ < 1 := ht
  have hrn : ‖r‖ = 1 := by
    have : ‖r - 1‖ < ‖(1 : A)‖ := by rw [norm_one]; exact hr1
    rw [norm_eq_of_norm_sub_lt' this, norm_one]
  apply norm_eq_of_norm_sub_lt'
  have e : 1 - t * r ^ n - (1 - t) = -(t * (r ^ n - 1)) := by ring
  rw [e, norm_neg, norm_mul, htn, one_mul]
  refine lt_of_le_of_lt (norm_pow_sub_one_le hrn.le n) (lt_of_le_of_lt hr ?_)
  calc ρ * ‖1 - t‖ < 1 * ‖1 - t‖ := mul_lt_mul_of_pos_right hρ h1t
    _ = ‖1 - t‖ := one_mul _

theorem xi_bound_q [FiniteDimensional K L] (Ω' : Set G) (hΩ' : IsCompact Ω') :
    ∃ C : Set E, IsCompact C ∧ ∀ (p q : Eˣ) (ξ : E),
      diagUnits2 p q * nGL (AutomorphicForm.sigmaTensor K L F σ ξ - ((q * p⁻¹ : Eˣ) : E) * ξ) ∈ Ω' →
      (1 - TwXi.Nm K L σ v ((q * p⁻¹ : Eˣ) : E)) * ξ ∈ C :=
  TwXi.exists_isCompact_forall_one_sub_Nm_mul_xi_mem K L σ v Ω' hΩ'

set_option maxHeartbeats 4000000 in

theorem twShiftQ_main [FiniteDimensional K L] (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ U₀ ∈ nhds (1 : Fˣ), ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ a t : Fˣ, t ∈ U₀ → t ≠ 1 → ∀ d₁ d₂ : Fˣ,
        ‖(d₁ : F) - 1‖ ≤ ρ₀ → ‖((d₁⁻¹ * d₂ : Fˣ) : F) - 1‖ ≤ ρ₀ * ‖(1 : F) - (t : F)‖ →
        ∀ α β : Eˣ,
          AutomorphicForm.normString K L F σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L F (diagUnits2 a (a * t)) →
          ∀ x : G, φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂)) *
              AutomorphicForm.sigmaGL K L F σ x) =
            φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) := by
  classical
  obtain ⟨hlc, hcs⟩ := hφ
  have hσG := TwShiftTop.continuous_sigmaGL K L F σ

  obtain ⟨W, hWo, h1W, hW⟩ := IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport φ hlc hcs

  set Ω' : Set G := (fun p : G × G => p.1 * p.2 * (AutomorphicForm.sigmaGL K L F σ p.1)⁻¹) '' ((𝒦 : Set G) ×ˢ tsupport φ)
    with hΩ'def
  have hΩ'c : IsCompact Ω' := by
    refine (isCompact_K.prod hcs).image ?_
    exact (continuous_fst.mul continuous_snd).mul (hσG.comp continuous_fst).inv
  have hΩ'mem : ∀ k ∈ (𝒦 : Set G), ∀ B : G,
      φ (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) ≠ 0 → B ∈ Ω' := by
    intro k hk B hB
    refine ⟨(k, k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k), Set.mk_mem_prod hk (subset_tsupport _ hB), ?_⟩
    show k * (k⁻¹ * B * AutomorphicForm.sigmaGL K L F σ k) * (AutomorphicForm.sigmaGL K L F σ k)⁻¹ = B
    group

  obtain ⟨C, hCc, hC⟩ := xi_bound_q (K := K) (L := L) (v := v) σ Ω' hΩ'c
  obtain ⟨D₁, hD₁, Nm, hNm, hΘ⟩ := exists_nhds_forall_ThetaQ_mem (K := K) (L := L) (v := v) σ hWo h1W
  obtain ⟨ρa, hρa, hscal⟩ := exists_pos_forall_iota_mul_mem (K := K) (L := L) (v := v) hCc hNm

  obtain ⟨A₁, hA₁, A₂, hA₂, hA⟩ := mem_nhds_prod_iff.1 hD₁
  obtain ⟨ρ₁, hρ₁, hball₁⟩ : ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ∀ d : Fˣ, ‖(d : F) - 1‖ < ρ₁ → d ∈ A₁ := by
    rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hA₁
    obtain ⟨V, hV, hsub⟩ := hA₁
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 (by simpa using hV)
    exact ⟨ε, hε, fun d hd => hsub (hεV (by rw [Metric.mem_ball, dist_eq_norm]; exact hd))⟩
  obtain ⟨ρ₂, hρ₂, hball₂⟩ : ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ∀ d : Fˣ, ‖(d : F) - 1‖ < ρ₂ → d ∈ A₂ := by
    rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hA₂
    obtain ⟨V, hV, hsub⟩ := hA₂
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 (by simpa using hV)
    exact ⟨ε, hε, fun d hd => hsub (hεV (by rw [Metric.mem_ball, dist_eq_norm]; exact hd))⟩
  set ρ₀ : ℝ := min (min ρa (min ρ₁ ρ₂ / 4)) (1 / 2) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀a : ρ₀ ≤ ρa := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀1 : ρ₀ ≤ min ρ₁ ρ₂ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀h : ρ₀ ≤ 1 / 2 := min_le_right _ _
  have hρ₀lt : ρ₀ < 1 := by linarith

  set U₀ : Set Fˣ := {t | ‖(1 : F) - (t : F)‖ < 1} with hU₀
  have hU₀n : U₀ ∈ nhds (1 : Fˣ) := by
    have hc : Continuous fun t : Fˣ => ‖(1 : F) - (t : F)‖ := continuous_norm.comp (continuous_const.sub Units.continuous_val)
    have ho : IsOpen U₀ := by rw [hU₀]; exact isOpen_lt hc continuous_const
    exact ho.mem_nhds (by show ‖(1 : F) - ((1 : Fˣ) : F)‖ < 1; simp)
  refine ⟨U₀, hU₀n, ρ₀, hρ₀pos, ?_⟩
  intro a t ht ht1 d₁ d₂ hd₁ hd₂ α β hN x
  have ht' : ‖(1 : F) - (t : F)‖ < 1 := ht
  have ht1' : (t : F) ≠ 1 := fun h => ht1 (Units.val_eq_one.1 h)
  have h1t : 0 < ‖(1 : F) - (t : F)‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ht1'))
  set r : Fˣ := d₁⁻¹ * d₂ with hr
  have hd₂' : d₂ = d₁ * r := by rw [hr, mul_inv_cancel_left]

  have hdD : (d₁, d₂) ∈ D₁ := by
    apply hA
    refine Set.mk_mem_prod (hball₁ d₁ ?_) (hball₂ d₂ ?_)
    · exact lt_of_le_of_lt hd₁ (by
        have : min ρ₁ ρ₂ / 4 < ρ₁ := by linarith [min_le_left ρ₁ ρ₂]
        linarith)
    · have hr1 : ‖(r : F) - 1‖ ≤ ρ₀ := by
        refine hd₂.trans ?_
        calc ρ₀ * ‖(1 : F) - (t : F)‖ ≤ ρ₀ * 1 := mul_le_mul_of_nonneg_left ht'.le hρ₀pos.le
          _ = ρ₀ := mul_one _
      have e : (d₂ : F) - 1 = (d₁ : F) * ((r : F) - 1) + ((d₁ : F) - 1) := by
        rw [hd₂', Units.val_mul]; ring
      have hd₁n : ‖(d₁ : F)‖ ≤ 2 := by
        calc ‖(d₁ : F)‖ = ‖((d₁ : F) - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖(d₁ : F) - 1‖ + ‖(1 : F)‖ := norm_add_le _ _
          _ ≤ ρ₀ + 1 := by rw [norm_one]; exact add_le_add hd₁ le_rfl
          _ ≤ 2 := by linarith
      calc ‖(d₂ : F) - 1‖ = ‖(d₁ : F) * ((r : F) - 1) + ((d₁ : F) - 1)‖ := by rw [e]
        _ ≤ ‖(d₁ : F)‖ * ‖(r : F) - 1‖ + ‖(d₁ : F) - 1‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ 2 * ρ₀ + ρ₀ := by
            exact add_le_add (mul_le_mul hd₁n hr1 (norm_nonneg _) (by norm_num)) hd₁
        _ < ρ₂ := by
            have : min ρ₁ ρ₂ / 4 ≤ ρ₂ / 4 := by linarith [min_le_right ρ₁ ρ₂]
            linarith

  obtain ⟨aq, haq, ξ, k, hk, hx⟩ := iwasawa x
  rw [uGL_eq_diagUnits2 haq] at hx
  set a₁ : Eˣ := ((mem_goodT_iff aq).1 haq).1.unit with ha₁
  set a₂ : Eˣ := ((mem_goodT_iff aq).1 haq).2.unit with ha₂
  obtain ⟨hNα, hNβ⟩ := NmU_of_normString_eq (K := K) (L := L) (v := v) σ α β a (a * t) hN

  set m : E := ξ * (1 - ((TwWindow.iotaU K L v (d₁⁻¹ * d₂) : Eˣ) : E)) with hm

  have hvanish : ∀ (α' β' : Eˣ) (s : Fˣ), s ≠ 1 → ‖((r : F) - 1)‖ ≤ ρ₀ * ‖(1 : F) - (s : F)‖ →
      NmU (K := K) (L := L) (v := v) σ β' * (NmU (K := K) (L := L) (v := v) σ α')⁻¹ = TwWindow.iotaU K L v s →
      m ∉ Nm → φ (x⁻¹ * diagUnits2 α' β' * AutomorphicForm.sigmaGL K L F σ x) = 0 := by
    intro α' β' s hs1 hrs hNs hmN
    by_contra hne
    apply hmN
    rw [hx] at hne
    rw [show (nGL ξ : G) = AutomorphicForm.unipotentGL2 ξ from rfl,
      AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul K L F σ α' β' a₁ a₂ ξ k,
      unitsMap_toMonoidHom_eq] at hne
    set p : Eˣ := α' * Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₁ * a₁⁻¹ with hp
    set q : Eˣ := β' * Units.map (AutomorphicForm.sigmaTensor K L F σ : E →* E) a₂ * a₂⁻¹ with hq
    have hB := hΩ'mem k hk (diagUnits2 p q * nGL (AutomorphicForm.sigmaTensor K L F σ ξ - ((q * p⁻¹ : Eˣ) : E) * ξ)) hne
    have hCmem := hC p q ξ hB

    have hNu : NmU (K := K) (L := L) (v := v) σ (q * p⁻¹) = TwWindow.iotaU K L v s := by
      rw [NmU_mul, NmU_inv, hq, hp, NmU_mul_sigma_div, NmU_mul_sigma_div]; exact hNs
    have hNuE : TwXi.Nm K L σ v ((q * p⁻¹ : Eˣ) : E) =
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (s : F) : E) := by
      rw [← TwXi.coe_NmU, ← NmU_eq_TwXi, hNu]; rfl
    rw [hNuE] at hCmem

    have hs1' : (1 : F) - (s : F) ≠ 0 := sub_ne_zero.2 (Ne.symm fun h => hs1 (Units.val_eq_one.1 h))
    have hmeq : m = (Algebra.TensorProduct.includeRight (R := K) (A := L)
        ((1 - ((r : F))) * ((1 : F) - (s : F))⁻¹) : E) *
        ((1 - (Algebra.TensorProduct.includeRight (R := K) (A := L) (s : F) : E)) * ξ) := by
      rw [hm, TwWindow.coe_iotaU, ← hr, map_mul, ← map_one (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)),
        ← map_sub, ← map_sub]
      rw [show ξ * (Algebra.TensorProduct.includeRight (R := K) (A := L)) (1 - (r : F)) =
        (Algebra.TensorProduct.includeRight (R := K) (A := L)) (1 - (r : F)) * ξ from mul_comm _ _]
      rw [mul_assoc, ← mul_assoc ((Algebra.TensorProduct.includeRight (R := K) (A := L)) (((1 : F) - (s : F))⁻¹)),
        ← map_mul, inv_mul_cancel₀ hs1', map_one, one_mul]
    rw [hmeq]
    refine hscal _ ?_ _ hCmem
    rw [norm_mul, norm_inv, norm_sub_rev]
    calc ‖(r : F) - 1‖ * ‖(1 : F) - (s : F)‖⁻¹ ≤ ρ₀ * ‖(1 : F) - (s : F)‖ * ‖(1 : F) - (s : F)‖⁻¹ :=
          mul_le_mul_of_nonneg_right hrs (inv_nonneg.2 (norm_nonneg _))
      _ = ρ₀ := by rw [mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hs1'), mul_one]
      _ ≤ ρa := hρ₀a
  by_cases hmN : m ∈ Nm
  ·
    have hsplit : x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂)) *
        AutomorphicForm.sigmaGL K L F σ x =
        (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) *
          ((AutomorphicForm.sigmaGL K L F σ x)⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
            AutomorphicForm.sigmaGL K L F σ x) := by
      group
    rw [hsplit]
    have hT : (AutomorphicForm.sigmaGL K L F σ x)⁻¹ * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂) *
        AutomorphicForm.sigmaGL K L F σ x = ThetaQ (K := K) (L := L) (v := v) σ (((d₁, d₂), m), k) := by
      rw [hx, hm]; exact conj_shift_eq_ThetaQ (K := K) (L := L) (v := v) σ a₁ a₂ ξ k d₁ d₂
    rw [hT]
    exact (hW _ _ (hΘ (d₁, d₂) hdD m hmN k hk)).1
  ·
    have h0 : φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L F σ x) = 0 := by
      refine hvanish α β t ht1 ?_ ?_ hmN
      · simpa [hr] using hd₂
      · rw [hNα, hNβ, ← map_inv, ← map_mul, mul_comm a t, mul_inv_cancel_right]
    have h0' : φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L F (diagUnits2 d₁ d₂)) *
        AutomorphicForm.sigmaGL K L F σ x) = 0 := by
      rw [TwWindow.diagUnits2_mul_toTensorGL_diagUnits2]
      have hcell : ‖(1 : F) - ((t * r ^ Module.finrank K L : Fˣ) : F)‖ = ‖(1 : F) - (t : F)‖ := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val]
        exact norm_one_sub_mul_pow_eq (Module.finrank K L) ht' ht1' hρ₀lt (by simpa [hr] using hd₂)
      have hs1 : t * r ^ Module.finrank K L ≠ 1 := by
        intro h
        have : ‖(1 : F) - ((t * r ^ Module.finrank K L : Fˣ) : F)‖ = 0 := by rw [h]; simp
        rw [hcell] at this; exact absurd this h1t.ne'
      refine hvanish _ _ (t * r ^ Module.finrank K L) hs1 ?_ ?_ hmN
      · rw [hcell]; simpa [hr] using hd₂
      · rw [NmU_mul, NmU_mul, hNα, hNβ, NmU_iotaU, NmU_iotaU, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
        congr 1
        rw [hr, mul_inv, mul_pow, inv_pow,
          show a * t * d₂ ^ Module.finrank K L * (a⁻¹ * (d₁ ^ Module.finrank K L)⁻¹) =
            (a * a⁻¹) * (t * ((d₁ ^ Module.finrank K L)⁻¹ * d₂ ^ Module.finrank K L)) by ac_rfl,
          mul_inv_cancel, one_mul]
    rw [h0, h0']

end TwShiftQMain

end KcSemiLocalIwasawaHaar

namespace TwWindowR2

open AutomorphicForm

section algebra
variable {R : Type*} [CommRing R]

theorem diag_eq_scalar_mul (a t : Rˣ) :
    diagUnits2 a (a * t) = Matrix.GeneralLinearGroup.scalar (Fin 2) (a * t) * diagUnits2 t⁻¹ 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem diag_offdiag (a b : Rˣ) :
    ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
    ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem trace_sq_sub_four_det_diag (a b : Rˣ) :
    Matrix.trace ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) ^ 2 -
      4 * Matrix.det ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ((a : R) - (b : R)) ^ 2 := by
  simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

end algebra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

theorem isUnit_sub_diag (a t : (v.adicCompletion K)ˣ) (ht : t ≠ 1) :
    IsUnit (((a : (v.adicCompletion K)ˣ) : v.adicCompletion K) - ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
  rw [Units.val_mul, ← mul_one_sub]
  refine (Units.isUnit a).mul (isUnit_iff_ne_zero.2 (sub_ne_zero.2 ?_))
  intro h
  exact ht (Units.val_eq_one.1 h.symm)

theorem isRegularSemisimple_diag (a t : (v.adicCompletion K)ˣ) (ht : t ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) := by
  rw [AutomorphicForm.isRegularSemisimple_iff, trace_sq_sub_four_det_diag]
  exact (isUnit_sub_diag K v a t ht).pow 2

theorem P_unique [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) {a t : (v.adicCompletion K)ˣ} (ht : t ≠ 1) {J₁ J₂ : ℂ}
    (h₁ : TwWindow.P K L σ v φ a t J₁) (h₂ : TwWindow.P K L σ v φ a t J₂) : J₁ = J₂ := by
  obtain ⟨α₁, β₁, hN₁, τ₁, hτ₁, hτ₁1, hJ₁⟩ := h₁
  obtain ⟨α₂, β₂, hN₂, τ₂, hτ₂, hτ₂1, hJ₂⟩ := h₂
  exact AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal K L σ hgen v (diagUnits2 a (a * t))
    (isRegularSemisimple_diag K v a t ht) (diag_offdiag a (a * t)).1 (diag_offdiag a (a * t)).2
    (diagUnits2 α₁ β₁) (diagUnits2 α₂ β₂) hN₁ hN₂ τ₁ hτ₁ hτ₁1 τ₂ hτ₂ hτ₂1 φ hφ J₁ J₂ hJ₁ hJ₂

end TwWindowR2

namespace TwCell

open AutomorphicForm Filter Topology Metric

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

private theorem _root_.TwCell.twShiftQ_main [FiniteDimensional K L]
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ U₀ ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ∈ U₀ → t ≠ 1 → ∀ d₁ d₂ : (v.adicCompletion K)ˣ,
        ‖(d₁ : v.adicCompletion K) - 1‖ ≤ ρ₀ → ‖((d₁⁻¹ * d₂ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ ≤ ρ₀ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
        ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
          AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d₁ d₂)) *
              AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
            φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) :=
  KcSemiLocalIwasawaHaar.twShiftQ_main (K := K) (L := L) (v := v) σ φ hφ

p2m_export "TwCell" "twShiftQ_main"

theorem P_shift2 [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a t a₂ t₂ d₁ d₂ : (v.adicCompletion K)ˣ) (ht : t ≠ 1) (ht₂ : t₂ ≠ 1)
    (h₁ : a * d₁ ^ Module.finrank K L = a₂) (h₂ : a * t * d₂ ^ Module.finrank K L = a₂ * t₂)
    (hpt : ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d₁ d₂)) *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
          φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x))
    (J : ℂ) (hP : TwWindow.P K L σ v φ a t J) : TwWindow.P K L σ v φ a₂ t₂ J := by
  obtain ⟨α, β, hN, τ', hτ', h1, hJ⟩ := hP
  have hshift := hpt α β hN
  have hL1 : diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d₁ d₂) =
      diagUnits2 (α * TwWindow.iotaU K L v d₁) (β * TwWindow.iotaU K L v d₂) :=
    TwWindow.diagUnits2_mul_toTensorGL_diagUnits2 K L v α β d₁ d₂
  have hN' : AutomorphicForm.normString K L (v.adicCompletion K) σ
      (diagUnits2 (α * TwWindow.iotaU K L v d₁) (β * TwWindow.iotaU K L v d₂)) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a₂ (a₂ * t₂)) := by
    have h := TwWindow.normString_diagUnits2_mul_iotaU K L σ v α β a (a * t) d₁ d₂ hN
    rw [h₁, h₂] at h
    exact h
  have hat : a ≠ a * t := by
    intro h; apply ht
    exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
  have hat₂ : a₂ ≠ a₂ * t₂ := by
    intro h; apply ht₂
    exact mul_left_cancel (a := a₂) (by rw [mul_one]; exact h.symm)
  have hT := TwWindow.twistedCentralizer_diagUnits2_eq K L σ v hgen α β (α * TwWindow.iotaU K L v d₁)
    (β * TwWindow.iotaU K L v d₂) a (a * t) a₂ (a₂ * t₂) hat hat₂ hN hN'
  obtain ⟨τ₂, hτ₂, h1₂, hint⟩ :=
    TwWindow.transport_of_subgroup_eq (AutomorphicForm.semiLocalIntegralSet K L v) hT τ' hτ'
  refine ⟨α * TwWindow.iotaU K L v d₁, β * TwWindow.iotaU K L v d₂, hN', τ₂, hτ₂, by rw [h1₂]; exact h1, ?_⟩
  obtain ⟨s, ⟨hs0, hsm, hsc, hs1⟩, hJs⟩ := hJ
  refine ⟨s, ⟨hs0, hsm, hsc, fun x hx => ?_⟩, ?_⟩
  · rw [hint]
    apply hs1 x
    rw [← hL1, hshift x] at hx
    exact hx
  · rw [hJs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hL1, hshift x]

omit σ φ L in
theorem norm_eq_of_norm_sub_lt {a a' : v.adicCompletion K} (h : ‖a' - a‖ < ‖a‖) : ‖a'‖ = ‖a‖ := by
  apply le_antisymm
  · have h1 : ‖a'‖ = ‖(a' - a) + a‖ := by rw [sub_add_cancel]
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le le_rfl)
  · by_contra hlt
    push_neg at hlt
    have h2 : ‖a‖ = ‖(a - a') + a'‖ := by rw [sub_add_cancel]
    have h3 : ‖a - a'‖ < ‖a‖ := by rwa [norm_sub_rev]
    have := (IsUltrametricDist.norm_add_le_max (a - a') a')
    rw [← h2] at this
    exact absurd (this.trans_lt (max_lt h3 hlt)) (lt_irrefl _)

omit σ φ L in
theorem exists_radius_of_mem_nhds_one {U : Set (v.adicCompletion K)ˣ} (hU : U ∈ 𝓝 (1 : (v.adicCompletion K)ˣ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : (v.adicCompletion K)ˣ, ‖(t : v.adicCompletion K) - 1‖ ≤ r → t ∈ U := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [Units.val_one, Metric.mem_nhds_iff] at hW
  obtain ⟨ε, hε, hεW⟩ := hW
  refine ⟨ε / 2, by positivity, fun t ht => hWU ?_⟩
  show (t : v.adicCompletion K) ∈ W
  apply hεW
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

omit σ φ L in

theorem norm_pow_sub_one (n : ℕ) (u : v.adicCompletion K) (hu : ‖u - 1‖ < ‖(n : v.adicCompletion K)‖) :
    ‖u ^ n - 1‖ = ‖(n : v.adicCompletion K)‖ * ‖u - 1‖ := by
  have hn1 : ‖(n : v.adicCompletion K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ n
  have hu1 : ‖u‖ = 1 := by
    have := norm_eq_of_norm_sub_lt K v (a := 1) (a' := u) (by rw [norm_one]; exact lt_of_lt_of_le hu hn1)
    rwa [norm_one] at this

  have hultra : ∀ (m : ℕ) (g : ℕ → v.adicCompletion K) (C : ℝ), 0 ≤ C → (∀ i, ‖g i‖ ≤ C) →
      ‖∑ i ∈ Finset.range m, g i‖ ≤ C := by
    intro m g C hC hg
    induction m with
    | zero => simp [hC]
    | succ m ih => rw [Finset.sum_range_succ]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (hg m))
  have hgeom : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, u ^ i‖ ≤ 1 := fun m =>
    hultra m (fun i => u ^ i) 1 zero_le_one (fun i => by rw [norm_pow, hu1, one_pow])
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← geom_sum_mul u i, norm_mul]
    calc ‖∑ j ∈ Finset.range i, u ^ j‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (hgeom i) (norm_nonneg _)
      _ = ‖u - 1‖ := one_mul _
  have hdiff : ‖∑ i ∈ Finset.range n, u ^ i - (n : v.adicCompletion K)‖ ≤ ‖u - 1‖ := by
    have : ∑ i ∈ Finset.range n, u ^ i - (n : v.adicCompletion K) = ∑ i ∈ Finset.range n, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact hultra n (fun i => u ^ i - 1) _ (norm_nonneg _) hpow
  have hS : ‖∑ i ∈ Finset.range n, u ^ i‖ = ‖(n : v.adicCompletion K)‖ :=
    norm_eq_of_norm_sub_lt K v (lt_of_le_of_lt hdiff hu)
  rw [← geom_sum_mul u n, norm_mul, hS]

omit σ φ L in

theorem exists_root_near_one (n : ℕ) (hn : 0 < n) :
    ∃ r : ℝ, 0 < r ∧ ∀ c : (v.adicCompletion K)ˣ, ‖(c : v.adicCompletion K) - 1‖ ≤ r →
      ∃ u : (v.adicCompletion K)ˣ, u ^ n = c ∧ ‖(u : v.adicCompletion K) - 1‖ ≤ ‖(n : v.adicCompletion K)‖⁻¹ * ‖(c : v.adicCompletion K) - 1‖ := by
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hnpos : 0 < ‖(n : v.adicCompletion K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hn.ne')
  set V : Set (v.adicCompletion K)ˣ := {u | ‖(u : v.adicCompletion K) - 1‖ < ‖(n : v.adicCompletion K)‖} with hV
  have hVn : V ∈ 𝓝 (1 : (v.adicCompletion K)ˣ) := by
    have hO : IsOpen V := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
    exact hO.mem_nhds (by show ‖((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ < _; simpa using hnpos)
  have himg := IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion K v n hn V hVn
  obtain ⟨r, hr, hrW⟩ := exists_radius_of_mem_nhds_one K v himg
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨u, huV, huc⟩ := hrW c hc
  refine ⟨u, huc, ?_⟩
  have hid := norm_pow_sub_one K v n (u : v.adicCompletion K) huV
  have hcu : ((c : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (u : v.adicCompletion K) ^ n := by rw [← huc, Units.val_pow_eq_pow_val]
  rw [hcu, hid, ← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul]

theorem ratio_mul_sqrtRatio_eq (a t : (v.adicCompletion K)ˣ) (ht1 : ‖(t : v.adicCompletion K)‖ = 1) :
    AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
      AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) =
      ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ := by
  have hprod : ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) * (((a)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = ((t : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    rw [← Units.val_mul, mul_comm a t, mul_assoc, mul_inv_cancel, mul_one]
  simp only [AutomorphicForm.LocalWeightedOrbital.ratio, AutomorphicForm.LocalWeightedOrbital.sqrtRatio]
  rw [hprod, Units.val_mul, norm_mul, ht1, mul_one, div_self (norm_pos_iff.2 (Units.ne_zero a)).ne', Real.sqrt_one,
    mul_one]

theorem cell_P [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ t ∈ U, ‖(t : v.adicCompletion K) - 1‖ < 1) ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤ ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
        t ≠ 1 → t' ≠ 1 → ∀ J : ℂ, TwWindow.P K L σ v φ a t J → TwWindow.P K L σ v φ a' t' J := by
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨U₀, hU₀, ρ₀, hρ₀, hQ⟩ := twShiftQ_main K L σ v φ hφ
  have hℓ : 0 < Module.finrank K L := Module.finrank_pos
  have hℓn : 0 < ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hℓ.ne')
  obtain ⟨r, hr, hroot⟩ := exists_root_near_one K v (Module.finrank K L) hℓ
  set B : Set (v.adicCompletion K)ˣ := {t | ‖(t : v.adicCompletion K) - 1‖ < 1} with hB
  have hBn : B ∈ 𝓝 (1 : (v.adicCompletion K)ˣ) := by
    have hO : IsOpen B := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
    exact hO.mem_nhds (by show ‖((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ < 1; simp)
  set ρ : ℝ := min (min r (ρ₀ * ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖)) 2⁻¹ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ₀ : ρ ≤ ρ₀ * ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨U₀ ∩ B, Filter.inter_mem hU₀ hBn, ρ, hρ0, hρ1, fun t ht => ht.2, ?_⟩
  intro a a' t t' ht ha' ht' ht1 ht'1 J hP
  have hapos : 0 < ‖(a : v.adicCompletion K)‖ := norm_pos_iff.2 (Units.ne_zero a)
  have htn : ‖(t : v.adicCompletion K)‖ = 1 := by
    have := norm_eq_of_norm_sub_lt K v (a := 1) (a' := (t : v.adicCompletion K)) (by rw [norm_one]; exact ht.2)
    rwa [norm_one] at this
  have h1t : 0 < ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h => ht1 (Units.val_eq_one.1 h.symm))
  have h1t1 : ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ < 1 := by rw [norm_sub_rev]; exact ht.2

  set c₁ : (v.adicCompletion K)ˣ := a⁻¹ * a' with hc₁
  set e : (v.adicCompletion K)ˣ := t⁻¹ * t' with he
  have hc₁n : ‖(c₁ : v.adicCompletion K) - 1‖ ≤ ρ := by
    have : (c₁ : v.adicCompletion K) - 1 = ((a : v.adicCompletion K))⁻¹ * ((a' : v.adicCompletion K) - (a : v.adicCompletion K)) := by
      rw [hc₁, Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ (Units.ne_zero a)]
    rw [this, norm_mul, norm_inv, inv_mul_le_iff₀ hapos]
    calc ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ := ha'
      _ = ‖(a : v.adicCompletion K)‖ * ρ := mul_comm _ _
  have hen : ‖(e : v.adicCompletion K) - 1‖ ≤ ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ := by
    have : (e : v.adicCompletion K) - 1 = ((t : v.adicCompletion K))⁻¹ * ((t' : v.adicCompletion K) - (t : v.adicCompletion K)) := by
      rw [he, Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ (Units.ne_zero t)]
    rw [this, norm_mul, norm_inv, htn, inv_one, one_mul]
    exact ht'
  have hen' : ‖(e : v.adicCompletion K) - 1‖ ≤ r :=
    hen.trans ((mul_le_of_le_one_right hρ0.le h1t1.le).trans hρr)
  obtain ⟨d₁, hd₁, hd₁n⟩ := hroot c₁ (hc₁n.trans hρr)
  obtain ⟨u, hu, hun⟩ := hroot e hen'

  have hb₁ : ‖(d₁ : v.adicCompletion K) - 1‖ ≤ ρ₀ := by
    refine hd₁n.trans ?_
    rw [inv_mul_le_iff₀ hℓn]
    exact hc₁n.trans (by rw [mul_comm]; exact hρρ₀)
  have hb₂ : ‖((d₁⁻¹ * (d₁ * u) : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ ≤ ρ₀ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ := by
    rw [inv_mul_cancel_left]
    refine hun.trans ?_
    rw [inv_mul_le_iff₀ hℓn]
    refine hen.trans ?_
    calc ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤ ρ₀ * ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ :=
          mul_le_mul_of_nonneg_right hρρ₀ (norm_nonneg _)
      _ = ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ * (ρ₀ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖) := by ring
  have h₁ : a * d₁ ^ Module.finrank K L = a' := by
    rw [hd₁, hc₁, mul_inv_cancel_left]
  have h₂ : a * t * (d₁ * u) ^ Module.finrank K L = a' * t' := by
    rw [mul_pow, hd₁, hu, hc₁, he, mul_mul_mul_comm, mul_inv_cancel_left, mul_inv_cancel_left]
  exact P_shift2 K L σ v φ hgen a t a' t' d₁ (d₁ * u) ht1 ht'1 h₁ h₂
    (fun α β hN => hQ a t ht.1 ht1 d₁ (d₁ * u) hb₁ hb₂ α β hN) J hP

end TwCell

open TwCell in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
        t ≠ 1 → t' ≠ 1 →
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ∀ α' β' : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')) →
            ∀ (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β'))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β'))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β')) τ'' →
              τ'' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J'' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α' β') τ'' φ J'' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') : ℝ) : ℂ) * J'') := by
  obtain ⟨U, hU, ρ, hρ, hρ1, hUB, hcell⟩ := TwCell.cell_P K L σ v φ hgen hφ
  refine ⟨U, hU, ρ, hρ, ?_⟩
  intro a a' t t' ht ha' htt ht1 ht'1 α β hN τ' hτ' h1 J' hJ' α' β' hN' τ'' hτ'' h1' J'' hJ''
  have hP : TwWindow.P K L σ v φ a t J' := ⟨α, β, hN, τ', hτ', h1, hJ'⟩
  have hP' : TwWindow.P K L σ v φ a' t' J' := hcell a a' t t' ht ha' htt ht1 ht'1 J' hP
  have hP'' : TwWindow.P K L σ v φ a' t' J'' := ⟨α', β', hN', τ'', hτ'', h1', hJ''⟩
  have hJ : J' = J'' := TwWindowR2.P_unique K L σ v φ hgen hφ ht'1 hP' hP''
  have htn : ‖(t : v.adicCompletion K)‖ = 1 := by
    have := TwCell.norm_eq_of_norm_sub_lt K v (a := 1) (a' := (t : v.adicCompletion K)) (by rw [norm_one]; exact hUB t ht)
    rwa [norm_one] at this
  have h1t : 0 < ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h => ht1 (Units.val_eq_one.1 h.symm))
  have h1t' : ‖(1 : v.adicCompletion K) - (t' : v.adicCompletion K)‖ = ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ := by
    apply TwCell.norm_eq_of_norm_sub_lt K v
    have e : ((1 : v.adicCompletion K) - (t' : v.adicCompletion K)) - ((1 : v.adicCompletion K) - (t : v.adicCompletion K)) = -((t' : v.adicCompletion K) - (t : v.adicCompletion K)) := by ring
    rw [e, norm_neg]
    exact lt_of_le_of_lt htt (by nlinarith)
  have ht'n : ‖(t' : v.adicCompletion K)‖ = 1 := by
    have hlt : ‖(t' : v.adicCompletion K) - 1‖ < ‖(1 : v.adicCompletion K)‖ := by
      rw [norm_sub_rev, h1t', norm_one, norm_sub_rev]; exact hUB t ht
    have := TwCell.norm_eq_of_norm_sub_lt K v hlt
    rwa [norm_one] at this
  rw [TwCell.ratio_mul_sqrtRatio_eq K v a t htn, TwCell.ratio_mul_sqrtRatio_eq K v a' t' ht'n, h1t', hJ]

end
end S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal (solution)
