-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ecf7cd9b-9406-53fd-a3cf-636c76f3df6c

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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K42P1C

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm Topology TopologicalSpace
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] in
theorem continuous_sigmaTensor (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  have h : Continuous
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  exact h

omit [NumberField K] [NumberField L] in
theorem continuous_sigmaGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact Continuous.units_map _ ((continuous_id.matrix_map (continuous_sigmaTensor K L σ A)) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => m.map (sigmaTensor K L A σ))

omit [NumberField K] [NumberField L] in
theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hσ := continuous_sigmaGL K L σ A
  have hset : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [hset]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul (hσ.inv)) continuous_const

theorem perPlace (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ τ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ))
        (twistedCentralizerBorel K L (v.adicCompletion K) σ (tensorPlace K L v δ)),
      @Measure.IsHaarMeasure _ _ _
        (twistedCentralizerBorel K L (v.adicCompletion K) σ (tensorPlace K L v δ)) τ ∧
      τ (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 := by
  letI : MeasurableSpace (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)) :=
    twistedCentralizerBorel K L (v.adicCompletion K) σ (tensorPlace K L v δ)
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)) := ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  have hcl := isClosed_twistedCentralizer K L σ (v.adicCompletion K) (tensorPlace K L v δ)
  have hemb : IsClosedEmbedding
      (Subtype.val : twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ) →
        GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)) :=
    hemb.locallyCompactSpace
  let K₀ : PositiveCompacts (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)) :=
    { carrier := Subtype.val ⁻¹' semiLocalIntegralSet K L v
      isCompact' := hemb.isCompact_preimage (isCompact_semiLocalIntegralSet K L v)
      interior_nonempty' := by
        rw [((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).interior_eq]
        exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩ }
  exact ⟨Measure.haarMeasure K₀, Measure.isHaarMeasure_haarMeasure K₀, Measure.haarMeasure_self⟩

end K42P1C

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    ∃ (τf : ∀ v : HeightOneSpectrum (𝓞 K),
        @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))),
      (∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) (τf v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) := by
  exact ⟨fun v => (K42P1C.perPlace K L σ δ v).choose,
    fun v => (K42P1C.perPlace K L σ δ v).choose_spec.1,
    fun v => (K42P1C.perPlace K L σ δ v).choose_spec.2⟩

end S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one (solution)
