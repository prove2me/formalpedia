-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7f1a484f-45a0-59b1-a917-8469433fa3d0

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

namespace P2MW.S_AutomorphicForm_exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K42CMU

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology"

theorem eq_smul_of_sigmaCompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s _hs
  have hcov : s = ⋃ n : ℕ, s ∩ compactCovering G n := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have hmono : Monotone fun n : ℕ => s ∩ compactCovering G n := fun m n hmn =>
    Set.inter_subset_inter_right _ (compactCovering_subset G hmn)
  rw [hcov, hmono.measure_iUnion, hmono.measure_iUnion]
  congr 1
  ext n
  rw [Measure.smul_apply]
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
    ((isCompact_compactCovering G n).closure_of_subset Set.inter_subset_right)

theorem sigmaCompactSpace_gl {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [SigmaCompactSpace R] (n : Type*) [Fintype n] [DecidableEq n] :
    SigmaCompactSpace (GL n R) := by
  haveI : T2Space (Matrix n n R) := inferInstanceAs (T2Space (n → n → R))
  haveI : SigmaCompactSpace (Matrix n n R) := inferInstanceAs (SigmaCompactSpace (n → n → R))
  haveI : SigmaCompactSpace (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

end K42CMU

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ) :
    ∃ cμ : ℝ, 0 < cμ ∧
      ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
        ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 L) L)) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : Measure.IsHaarMeasure μ := hμ
  haveI : Measure.IsHaarMeasure (adelicGLHaar (Fin 2) (𝓞 L) L) := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (GL (Fin 2) (AdeleRing (𝓞 L) L)) := K42CMU.sigmaCompactSpace_gl (Fin 2)
  set e := AutomorphicForm.baseChangeGLEquiv K L with he
  haveI : Measure.IsHaarMeasure (μ.map e) := ContinuousMulEquiv.isHaarMeasure_map μ e
  set c := Measure.haarScalarFactor (μ.map e) (adelicGLHaar (Fin 2) (𝓞 L) L) with hc
  have hμ' : μ.map e = c • adelicGLHaar (Fin 2) (𝓞 L) L := K42CMU.eq_smul_of_sigmaCompact _ _
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨(c : ℝ), NNReal.coe_pos.mpr hcpos, fun F => ?_⟩
  have h1 : ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = ∫ g, F g ∂(μ.map e) := by
    have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F
    exact this.symm
  rw [h1, hμ', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end S_AutomorphicForm_exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_integral_comp_baseChangeGL_eq_mul_integral_adelicGLHaar (solution)
