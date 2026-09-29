-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/79bcbe97-983a-5e1e-b261-545cccaf2368

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace KcTwAdmissibleExists

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (L ⊗[K] HeightOneSpectrum.adicCompletion K v)
local notation "GF" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] HeightOneSpectrum.adicCompletion K v)

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

theorem isReduced_E : IsReduced E := Algebra.isReduced_tensorProduct_of_perfectField K F L

theorem t2Space_GL : T2Space G := AutomorphicForm.t2Space_tensorGL K L F
theorem locallyCompactSpace_GL : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F
theorem isTopologicalGroup_GL : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] t2Space_GL locallyCompactSpace_GL isTopologicalGroup_GL measurableSpace_GL

theorem t1Space_GL : T1Space G := @T2Space.t1Space G _ t2Space_GL

attribute [local instance] t1Space_GL

theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

attribute [local instance] borelSpace_GL

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) E) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

section Sigma
variable (σ : L ≃ₐ[K] L)
local notation "σE" => AutomorphicForm.sigmaTensor K L (HeightOneSpectrum.adicCompletion K v) σ
local notation "σG" => AutomorphicForm.sigmaGL K L (HeightOneSpectrum.adicCompletion K v) σ

theorem sigmaTensor_tmul (l : L) (c : F) : σE (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c
  rw [Algebra.TensorProduct.map_tmul]; rfl

def sigmaLin : E →ₗ[F] E where
  toFun := σE
  map_add' x y := map_add _ x y
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp

theorem continuous_sigmaTensor : Continuous (σE : E → E) :=
  IsModuleTopology.continuous_of_linearMap (sigmaLin (v := v) σ)

theorem coe_sigmaGL (g : G) :
    ((σG g : G) : M2) = (g : M2).map σE := rfl

theorem continuous_sigmaGL : Continuous (σG : G → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_sigmaGL, Matrix.map_apply]
    exact (continuous_sigmaTensor σ).comp (Units.continuous_val.matrix_elem i j)
  · have : ∀ x : G, (((σG x)⁻¹ : G) : M2) i j = σE (((x⁻¹ : G) : M2) i j) := by
      intro x
      rw [← map_inv, coe_sigmaGL, Matrix.map_apply]
    simp_rw [this]
    exact (continuous_sigmaTensor σ).comp (Units.continuous_coe_inv.matrix_elem i j)

theorem isClosed_twistedCentralizer (δ : G) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L F σ δ : Subgroup G) : Set G) := by
  have : ((AutomorphicForm.twistedCentralizer K L F σ δ : Subgroup G) : Set G) =
      (fun t : G => t * δ * (σG t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff]
  rw [this]
  have hc : Continuous fun t : G => t * δ * (σG t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL σ).inv
  exact (@isClosed_singleton G _ t1Space_GL δ).preimage hc

theorem exists_isHaarMeasure_twistedCentralizer (δ : G) :
    ∃ τ' : @Measure (AutomorphicForm.twistedCentralizer K L F σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L F σ δ),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L F σ δ) τ' ∧
      τ' {x | (x : G) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 := by
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L F σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L F σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L F σ δ) := ⟨rfl⟩
  have hce : Topology.IsClosedEmbedding
      (Subtype.val : AutomorphicForm.twistedCentralizer K L F σ δ → G) :=
    (isClosed_twistedCentralizer σ δ).isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace (AutomorphicForm.twistedCentralizer K L F σ δ) := hce.locallyCompactSpace

  set S : Set (AutomorphicForm.twistedCentralizer K L F σ δ) :=
    {x | (x : G) ∈ AutomorphicForm.semiLocalIntegralSet K L v} with hS
  have hSpre : S = Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v := rfl
  have hSc : IsCompact S := by
    rw [hSpre]
    exact hce.isCompact_preimage (AutomorphicForm.isCompact_semiLocalIntegralSet K L v)
  have hSo : IsOpen S := by
    rw [hSpre]
    exact (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val
  have h1S : (1 : AutomorphicForm.twistedCentralizer K L F σ δ) ∈ S :=
    AutomorphicForm.one_mem_semiLocalIntegralSet K L v
  let K₀ : TopologicalSpace.PositiveCompacts (AutomorphicForm.twistedCentralizer K L F σ δ) :=
    { carrier := S
      isCompact' := hSc
      interior_nonempty' := by
        rw [hSo.interior_eq]
        exact ⟨1, h1S⟩ }
  refine ⟨Measure.haarMeasure K₀, Measure.isHaarMeasure_haarMeasure K₀, ?_⟩
  exact Measure.haarMeasure_self
end Sigma

theorem toTensorGL_apply (t : GF) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L F t : G) : M2) i j = (1 : L) ⊗ₜ[K] ((t : Matrix (Fin 2) (Fin 2) F) i j) :=
  rfl

theorem isRegularSemisimple_diagUnits2 (a t : Fˣ) (ht : t ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t) : GF) := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero]
  have ha : (a : F) ≠ 0 := a.ne_zero
  have ht' : (1 : F) - (t : F) ≠ 0 := by
    intro h
    apply ht
    apply Units.ext
    have : (t : F) = 1 := (sub_eq_zero.1 h).symm
    simpa using this
  have hcalc : Matrix.trace ((diagUnits2 a (a * t) : GF) : Matrix (Fin 2) (Fin 2) F) ^ 2 -
      4 * Matrix.det ((diagUnits2 a (a * t) : GF) : Matrix (Fin 2) (Fin 2) F) =
      ((a : F) * ((1 : F) - (t : F))) ^ 2 := by
    simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val', Units.val_mul]
    ring
  rw [hcalc]
  exact pow_ne_zero 2 (mul_ne_zero ha ht')

theorem isRegularSemisimple_toTensorGL {t : GF} (ht : AutomorphicForm.IsRegularSemisimple t) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.toTensorGL K L F t) := by
  unfold AutomorphicForm.IsRegularSemisimple at ht ⊢
  have htr : ((AutomorphicForm.toTensorGL K L F t : G) : M2).trace =
      algebraMap F E (t : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two, toTensorGL_apply, toTensorGL_apply, map_add]; rfl
  have hdet : ((AutomorphicForm.toTensorGL K L F t : G) : M2).det =
      algebraMap F E (t : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, toTensorGL_apply, toTensorGL_apply, toTensorGL_apply,
      toTensorGL_apply, map_sub, map_mul, map_mul]; rfl
  rw [htr, hdet]
  have : algebraMap F E (t : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * algebraMap F E (t : Matrix (Fin 2) (Fin 2) F).det =
      algebraMap F E ((t : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (t : Matrix (Fin 2) (Fin 2) F).det) := by
    rw [map_sub, map_pow, map_mul, map_ofNat]
  rw [this]
  exact ht.map _

theorem main (σ : L ≃ₐ[K] L)
    (φ : G → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (a t : Fˣ) (ht : t ≠ 1) (α β : (L ⊗[K] (v.adicCompletion K))ˣ)
    (hN : AutomorphicForm.normString K L F σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L F (diagUnits2 a (a * t))) :
    ∃ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β))
        (AutomorphicForm.twistedCentralizerBorel K L F σ (diagUnits2 α β))),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L F σ (diagUnits2 α β)) τ' ∧
      τ' {x | (x : G) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 ∧
      ∃ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' := by
  obtain ⟨τ', hτ', h1⟩ := exists_isHaarMeasure_twistedCentralizer (K := K) (L := L) (v := v) σ (diagUnits2 α β)
  refine ⟨τ', hτ', h1, ?_⟩

  have hδreg : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L F σ (diagUnits2 α β)) := by
    rw [hN]
    exact isRegularSemisimple_toTensorGL (isRegularSemisimple_diagUnits2 a t ht)
  haveI : IsReduced E := isReduced_E
  obtain ⟨w, hw, -⟩ :=
    AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing
      K L F σ (diagUnits2 α β) hδreg τ' hτ' φ hφ.2
  exact ⟨_, w, hw, rfl⟩

end KcTwAdmissibleExists

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → ∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
      ∃ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' ∧
        τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 ∧
        ∃ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' := by
  intro a t ht α β hN
  exact KcTwAdmissibleExists.main σ φ hφ a t ht α β hN

end S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq (solution)
