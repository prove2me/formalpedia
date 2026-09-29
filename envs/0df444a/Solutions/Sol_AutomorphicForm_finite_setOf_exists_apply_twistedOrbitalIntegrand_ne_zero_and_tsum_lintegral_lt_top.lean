-- Prove2me | solution 1 for AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7788edd8-91d6-59c0-8776-c66293415c59

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar sigmaAdelicAct sigmaAdelicAct_one sigmaAdelicAct_mul continuous_sigmaAdelicAct sigmaAdelicAct_globalPoints mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives adelicKernelLocalFiniteness ideleNorm_det_globalPoints"
namespace C2A
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  ext i j
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, M4aHerbrand.IdeleGaloisDescent.unitsAct,
      Matrix.diagonal]

theorem globalPoints_eq_centralScalar_of_val_eq_scalar (ζ : GL (Fin 2) L) (u : Lˣ)
    (h : (ζ : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) (u : L)) :
    AutomorphicForm.globalPoints (𝓞 L) L ζ =
      AutomorphicForm.centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) := by
  ext i j
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar]
  have hij := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.scalar_apply] at hij ⊢ <;>
    simp [hij]

theorem centralScalar_mem_center (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L z ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨z, rfl⟩

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * y = y * AutomorphicForm.centralScalar (𝓞 L) L z :=
  ((Subgroup.mem_center_iff.mp (centralScalar_mem_center L z)) y).symm

theorem scalar_mem_center (ζ : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) ζ ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨ζ, rfl⟩

theorem continuous_toGL {X : Type*} [TopologicalSpace X] {f : X → AutomorphicForm.AdelicGL2 (𝓞 L) L}
    (h1 : ∀ i j : Fin 2, Continuous fun x => ((f x : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)
    (h2 : ∀ i j : Fin 2, Continuous fun x => (((f x)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :
    Continuous f :=
  Units.continuous_iff.mpr ⟨continuous_matrix h1, continuous_matrix h2⟩

theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 L) L) := by
  apply continuous_toGL
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp only [NumberField.AdelicVolume.centralScalar_apply_eq]
      exact Units.continuous_val
    · simp only [NumberField.AdelicVolume.centralScalar_apply_ne _ hij]
      exact continuous_const
  · intro i j
    simp only [← map_inv]
    by_cases hij : i = j
    · subst hij
      simp only [NumberField.AdelicVolume.centralScalar_apply_eq]
      exact Units.continuous_coe_inv
    · simp only [NumberField.AdelicVolume.centralScalar_apply_ne _ hij]
      exact continuous_const

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z * z := by
  apply Units.ext
  simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar]
  ring

theorem isCompact_preimage_centralScalar (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C) :
    IsCompact (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C) := by
  let π : AutomorphicForm.AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ := fun g =>
    (((g : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0,
      MulOpposite.op ((((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0))
  have hπ : Continuous π := by
    refine Continuous.prodMk ?_ ?_
    · exact (Units.continuous_val.matrix_elem 0 0)
    · exact MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_elem 0 0)
  have hsub : AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C ⊆ Units.embedProduct _ ⁻¹' (π '' C) := by
    intro z hz
    refine ⟨_, hz, ?_⟩
    simp only [π, Units.embedProduct_apply, ← map_inv, NumberField.AdelicVolume.centralScalar_apply_eq]
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hπ)).of_isClosed_subset
    (hC.isClosed.preimage (continuous_centralScalar L)) hsub

theorem continuous_det :
    Continuous (Matrix.GeneralLinearGroup.det : AutomorphicForm.AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ((g : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det
    exact Units.continuous_val.matrix_det
  · show Continuous fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det
    exact Units.continuous_coe_inv.matrix_det

theorem ideleNorm_inv' (w : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L w⁻¹ = (NumberField.TateGlobal.ideleNorm L w)⁻¹ := by
  have h1 : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
    have := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
    rw [mul_one] at this
    have hp := NumberField.TateGlobal.ideleNorm_pos (F := L) 1
    field_simp at this ⊢
    nlinarith [this, hp]
  have := NumberField.TateGlobal.ideleNorm_mul (F := L) w⁻¹ w
  rw [inv_mul_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem isCompact_setOf_coe_mem_Icc (a b : ℝ) (ha : 0 < a) :
    IsCompact {t : NNRealˣ | ((t : NNReal) : ℝ) ∈ Set.Icc a b} := by
  have hsub : {t : NNRealˣ | ((t : NNReal) : ℝ) ∈ Set.Icc a b} ⊆
      Units.embedProduct NNReal ⁻¹'
        ((Set.Icc ⟨a, ha.le⟩ ⟨max a b, ha.le.trans (le_max_left a b)⟩ : Set NNReal) ×ˢ
          (MulOpposite.op '' (Set.Icc ⟨(max a b)⁻¹, by positivity⟩ ⟨a⁻¹, by positivity⟩ : Set NNReal))) := by
    intro t ht
    simp only [Set.mem_setOf_eq, Set.mem_Icc] at ht
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_Icc, Set.mem_image]
    refine ⟨⟨?_, ?_⟩, ⟨((t⁻¹ : NNRealˣ) : NNReal), ⟨?_, ?_⟩, rfl⟩⟩
    · exact_mod_cast ht.1
    · exact_mod_cast ht.2.trans (le_max_right a b)
    · have h0 : (0 : ℝ) < ((t : NNReal) : ℝ) := ha.trans_le ht.1
      have : ((t⁻¹ : NNRealˣ) : NNReal) = ((t : NNReal))⁻¹ := Units.val_inv_eq_inv_val t
      rw [this, ← NNReal.coe_le_coe, NNReal.coe_inv]
      push_cast
      exact inv_anti₀ (by positivity) (ht.2.trans (le_max_right a b))
    · have h0 : (0 : ℝ) < ((t : NNReal) : ℝ) := ha.trans_le ht.1
      have : ((t⁻¹ : NNRealˣ) : NNReal) = ((t : NNReal))⁻¹ := Units.val_inv_eq_inv_val t
      rw [this, ← NNReal.coe_le_coe, NNReal.coe_inv]
      push_cast
      exact inv_anti₀ ha ht.1
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (isCompact_Icc.prod (isCompact_Icc.image MulOpposite.continuous_op))).of_isClosed_subset ?_ hsub
  exact isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)

end AutomorphicForm.C2A

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top.AutomorphicForm AutomorphicForm.C2A in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ,
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0}.Finite ∧
    (∀ i, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤) ∧
    (∑' i, ∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤ := by
  classical
  have hσAc : Continuous (sigmaAdelicAct K L D σ) := AutomorphicForm.continuous_sigmaAdelicAct K L D σ
  have hcc : Continuous (centralScalar (𝓞 L) L) := continuous_centralScalar L
  have L1 : ∀ ζ : Lˣ, globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) =
      centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ) := fun ζ =>
    globalPoints_eq_centralScalar_of_val_eq_scalar L _ ζ rfl
  have L2 : ∀ g : GL (Fin 2) L, globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) =
      sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) := fun g =>
    (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g).symm
  have L3 : ∀ w, sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L w) = centralScalar (𝓞 L) L (D.unitsAct σ w) :=
    fun w => sigmaAdelicAct_centralScalar K L D σ w
  have hcomm : ∀ (w : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
      g * centralScalar (𝓞 L) L w = centralScalar (𝓞 L) L w * g := fun w g => (centralScalar_comm L w g).symm
  have hScomm : ∀ (ζ : Lˣ) (g : GL (Fin 2) L),
      g * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * g := fun ζ g =>
    Subgroup.mem_center_iff.mp (scalar_mem_center L ζ) g

  set γ : ι → GL (Fin 2) L := fun i => r i * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i))⁻¹ with hγ

  have harg : ∀ (i : ι) (z : (AdeleRing (𝓞 L) L)ˣ),
      ((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x)) = x⁻¹ * (globalPoints (𝓞 L) L (γ i) * centralScalar (𝓞 L) L (D.unitsAct σ z)) * sigmaAdelicAct K L D σ x := by
    intro i z
    simp only [hγ, map_mul, map_inv, L2, L3]
    calc (((globalPoints (𝓞 L) L) (r i))⁻¹ * x)⁻¹ * (globalPoints (𝓞 L) L) δ₀ *
          ((centralScalar (𝓞 L) L) ((D.unitsAct σ) z) *
            (((sigmaAdelicAct K L D σ) ((globalPoints (𝓞 L) L) (r i)))⁻¹ * (sigmaAdelicAct K L D σ) x))
        = x⁻¹ * ((globalPoints (𝓞 L) L) (r i) * (globalPoints (𝓞 L) L) δ₀ *
            ((centralScalar (𝓞 L) L) ((D.unitsAct σ) z) * ((sigmaAdelicAct K L D σ) ((globalPoints (𝓞 L) L) (r i)))⁻¹)) *
          (sigmaAdelicAct K L D σ) x := by group
      _ = x⁻¹ * ((globalPoints (𝓞 L) L) (r i) * (globalPoints (𝓞 L) L) δ₀ *
            (((sigmaAdelicAct K L D σ) ((globalPoints (𝓞 L) L) (r i)))⁻¹ * (centralScalar (𝓞 L) L) ((D.unitsAct σ) z))) *
          (sigmaAdelicAct K L D σ) x := by
            rw [← hcomm ((D.unitsAct σ) z) (((sigmaAdelicAct K L D σ) ((globalPoints (𝓞 L) L) (r i)))⁻¹)]
      _ = x⁻¹ * ((globalPoints (𝓞 L) L) (r i) * (globalPoints (𝓞 L) L) δ₀ *
            ((sigmaAdelicAct K L D σ) ((globalPoints (𝓞 L) L) (r i)))⁻¹ * (centralScalar (𝓞 L) L) ((D.unitsAct σ) z)) *
          (sigmaAdelicAct K L D σ) x := by group

  have hSφc : IsCompact (tsupport φ) := hφs
  set C : Set (AdelicGL2 (𝓞 L) L) := (fun g => x * g * (sigmaAdelicAct K L D σ x)⁻¹) '' tsupport φ with hC
  have hCc : IsCompact C := hSφc.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hmemC : ∀ (i : ι) (z : (AdeleRing (𝓞 L) L)ˣ), φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0 →
      globalPoints (𝓞 L) L (γ i) * centralScalar (𝓞 L) L (D.unitsAct σ z) ∈ C := by
    intro i z hne
    have hmem : ((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x)) ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hne)
    refine ⟨_, hmem, ?_⟩
    show x * (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) * (sigmaAdelicAct K L D σ x)⁻¹ = _
    rw [harg]; group

  have hper : ∀ i, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤ := by
    intro i
    set y : AdelicGL2 (𝓞 L) L := ((globalPoints (𝓞 L) L (r i))⁻¹ * x) with hy
    set C' : Set (AdelicGL2 (𝓞 L) L) :=
      (fun s => (globalPoints (𝓞 L) L δ₀)⁻¹ * y * s * (sigmaAdelicAct K L D σ y)⁻¹) '' tsupport φ with hC'
    have hC'c : IsCompact C' := hSφc.image ((continuous_const.mul continuous_id).mul continuous_const)
    set Z : Set (AdeleRing (𝓞 L) L)ˣ := centralScalar (𝓞 L) L ⁻¹' (sigmaAdelicAct K L D σ⁻¹ '' C') with hZ
    have hZc : IsCompact Z :=
      isCompact_preimage_centralScalar L _ (hC'c.image (AutomorphicForm.continuous_sigmaAdelicAct K L D σ⁻¹))
    have hsupp : ∀ z, φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ≠ 0 → z ∈ Z := by
      intro z hz
      have hmem : y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y) ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hz)
      refine ⟨sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z), ⟨_, hmem, ?_⟩, ?_⟩
      · simp only [hy, map_mul, map_inv]; group
      · rw [← MonoidHom.comp_apply, ← AutomorphicForm.sigmaAdelicAct_mul, inv_mul_cancel,
          AutomorphicForm.sigmaAdelicAct_one, MonoidHom.id_apply]
    have hAc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y) :=
      continuous_const.mul (hσAc.comp (hcc.mul continuous_const))
    have hgc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) := hξc.mul (hφc.comp hAc)
    obtain ⟨B, hB⟩ := hZc.exists_bound_of_continuousOn hgc.continuousOn
    have hle : ∀ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))‖ₑ ≤ Z.indicator (fun _ => ENNReal.ofReal B) z := by
      intro z
      by_cases hz : z ∈ Z
      · rw [Set.indicator_of_mem hz, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hB z hz)
      · have h0 : φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) = 0 := by
          by_contra h
          exact hz (hsupp z h)
        rw [h0, mul_zero, enorm_zero]
        exact bot_le
    calc (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))‖ₑ ∂νZL)
        ≤ ∫⁻ z, Z.indicator (fun _ => ENNReal.ofReal B) z ∂νZL := lintegral_mono hle
      _ = ENNReal.ofReal B * νZL Z := lintegral_indicator_const hZc.isClosed.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZc.measure_lt_top

  have hFinite : {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ, φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0}.Finite := by
    rcases Set.eq_empty_or_nonempty C with hCe | hCne
    · have : {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ, φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro i ⟨z, hz⟩
        have := hmemC i z hz
        rw [hCe] at this
        exact this
      rw [this]
      exact Set.finite_empty

    have hdetn : Continuous fun g : AdelicGL2 (𝓞 L) L =>
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) :=
      (NumberField.TateGlobal.continuous_ideleNorm L).comp (continuous_det L)
    obtain ⟨M, hM⟩ := hCc.bddAbove_image hdetn.continuousOn
    obtain ⟨g₀, hg₀C, hg₀⟩ := hCc.exists_isMinOn hCne hdetn.continuousOn
    set m : ℝ := NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g₀) with hm
    have hm0 : 0 < m := NumberField.TateGlobal.ideleNorm_pos (F := L) _
    have hbounds : ∀ g ∈ C, m ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∧
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤ M :=
      fun g hg => ⟨(isMinOn_iff.mp hg₀) g hg, hM ⟨g, hg, rfl⟩⟩

    obtain ⟨Kc, hKc, -, hKrep⟩ :=
      NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
    obtain ⟨sN, hsNc, hsN, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
    set a : ℝ := Real.sqrt m with ha
    set b : ℝ := Real.sqrt M with hb
    have ha0 : 0 < a := Real.sqrt_pos.mpr hm0
    set T : Set NNRealˣ := {t : NNRealˣ | ((t : NNReal) : ℝ) ∈ Set.Icc a b} with hT
    have hTc : IsCompact T := isCompact_setOf_coe_mem_Icc a b ha0
    set C₂ : Set (AdeleRing (𝓞 L) L)ˣ :=
      (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 L) L)ˣ => p.1 * p.2) '' (Kc ×ˢ (sN '' T)) with hC₂
    have hC₂c : IsCompact C₂ := (hKc.prod (hTc.image hsNc)).image (continuous_fst.mul continuous_snd)
    have hdecomp : ∀ w : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L w ∈ Set.Icc a b →
        ∃ (η : Lˣ) (k : (AdeleRing (𝓞 L) L)ˣ), k ∈ C₂ ∧
          w = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * k := by
      intro w hw
      have hpos : 0 < NumberField.TateGlobal.ideleNorm L w := NumberField.TateGlobal.ideleNorm_pos (F := L) w
      have hne : (⟨NumberField.TateGlobal.ideleNorm L w, hpos.le⟩ : NNReal) ≠ 0 := by
        intro h
        have := congrArg (fun u : NNReal => (u : ℝ)) h
        exact hpos.ne' this
      set t : NNRealˣ := Units.mk0 _ hne with ht
      have htT : t ∈ T := by
        show ((t : NNReal) : ℝ) ∈ Set.Icc a b
        rw [ht, Units.val_mk0]
        exact hw
      have hn : NumberField.TateGlobal.ideleNorm L (sN t) = NumberField.TateGlobal.ideleNorm L w := by
        rw [hsN, ht, Units.val_mk0]; rfl
      have h1 : w * (sN t)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
        rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv', hn,
          mul_inv_cancel₀ hpos.ne']
      obtain ⟨η, κ, hκ, hηκ⟩ := hKrep _ h1
      refine ⟨η, κ * sN t, ⟨(κ, sN t), ⟨hκ, t, htT, rfl⟩, rfl⟩, ?_⟩
      calc w = w * (sN t)⁻¹ * sN t := by group
        _ = Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η * κ * sN t := by rw [hηκ]
        _ = _ := by rw [mul_assoc]; rfl

    set C₃ : Set (AdelicGL2 (𝓞 L) L) :=
      (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1 * (centralScalar (𝓞 L) L p.2)⁻¹) '' (C ×ˢ C₂) with hC₃
    have hC₃c : IsCompact C₃ := (hCc.prod hC₂c).image (continuous_fst.mul ((hcc.comp continuous_snd).inv))
    have hFinSet : {δ : GL (Fin 2) L | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ C₃}.Finite :=
      AutomorphicForm.adelicKernelLocalFiniteness L C₃ hC₃c 1 1
    have hkey : ∀ i ∈ {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ, φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0}, ∃ ζ : Lˣ,
        γ i * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ ∈
          {δ : GL (Fin 2) L | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ C₃} := by
      rintro i ⟨z, hz⟩
      have hgC := hmemC i z hz
      have hnorm : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
          (globalPoints (𝓞 L) L (γ i) * centralScalar (𝓞 L) L (D.unitsAct σ z))) =
          NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) * NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) := by
        rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul,
          det_centralScalar, NumberField.TateGlobal.ideleNorm_mul]
      obtain ⟨hlo, hhi⟩ := hbounds _ hgC
      rw [hnorm] at hlo hhi
      have hwpos : 0 ≤ NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) :=
        (NumberField.TateGlobal.ideleNorm_pos (F := L) _).le
      have hwI : NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) ∈ Set.Icc a b := by
        constructor
        · rw [ha, ← Real.sqrt_mul_self hwpos]; exact Real.sqrt_le_sqrt hlo
        · rw [hb, ← Real.sqrt_mul_self hwpos]; exact Real.sqrt_le_sqrt hhi
      obtain ⟨η, k, hk, hwk⟩ := hdecomp _ hwI
      refine ⟨η, ?_⟩
      show (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L (γ i * Matrix.GeneralLinearGroup.scalar (Fin 2) η) * 1 ∈ C₃
      rw [inv_one, one_mul, mul_one, map_mul, L1]
      refine ⟨(globalPoints (𝓞 L) L (γ i) * centralScalar (𝓞 L) L (D.unitsAct σ z), k), ⟨hgC, hk⟩, ?_⟩
      show globalPoints (𝓞 L) L (γ i) * centralScalar (𝓞 L) L (D.unitsAct σ z) * (centralScalar (𝓞 L) L k)⁻¹ = _
      rw [hwk, map_mul (centralScalar (𝓞 L) L)]; group
    choose ζf hζf using hkey
    obtain ⟨hmemI, huniq, -⟩ :=
      AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
        K L D σ δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr
    refine Set.Finite.of_finite_image (f := fun i => if h : i ∈ {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ, φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0}
        then γ i * Matrix.GeneralLinearGroup.scalar (Fin 2) (ζf i h) else 1) ?_ ?_
    · refine hFinSet.subset ?_
      rintro δ ⟨i, hi, rfl⟩
      simp only [dif_pos hi]
      exact hζf i hi
    · intro i hi j hj hij
      simp only [dif_pos hi, dif_pos hj] at hij
      have e : ∀ (k : ι) (ζ : Lˣ), γ k * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ =
          r k * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r k))⁻¹ := by
        intro k ζ
        simp only [hγ]
        calc r k * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r k))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ
            = r k * δ₀ * ((Matrix.GeneralLinearGroup.map (σ : L →+* L) (r k))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) := by group
          _ = r k * δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r k))⁻¹) := by rw [hScomm]
          _ = _ := by group
      rw [e, e] at hij
      obtain ⟨p, -, hpu⟩ := huniq _ (hmemI i (ζf i hi))
      have hi' : (i, ζf i hi) = p := hpu (i, ζf i hi) rfl
      have hj' : (j, ζf j hj) = p := hpu (j, ζf j hj) hij
      exact congrArg Prod.fst (hi'.trans hj'.symm)

  refine ⟨hFinite, hper, ?_⟩
  have hzero : ∀ i ∉ hFinite.toFinset, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) = 0 := by
    intro i hi
    rw [Set.Finite.mem_toFinset] at hi
    have h0 : ∀ z, φ (((globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((globalPoints (𝓞 L) L (r i))⁻¹ * x))) = 0 := fun z => by
      by_contra h
      exact hi ⟨z, h⟩
    simp only [h0, mul_zero, enorm_zero, lintegral_zero]
  rw [tsum_eq_sum hzero]
  exact ENNReal.sum_lt_top.mpr fun i _ => hper i

end S_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
end P2MW
export P2MW.S_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top (solution)
