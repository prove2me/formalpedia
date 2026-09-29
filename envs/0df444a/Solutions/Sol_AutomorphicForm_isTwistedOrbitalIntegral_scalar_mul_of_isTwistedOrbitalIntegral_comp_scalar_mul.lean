-- Prove2me | solution 1 for AutomorphicForm.isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6dee015a-a516-52ef-970e-9be33eb246b1

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

namespace P2MW.S_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K42CTFIN

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology NumberField AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem integral_eq_of_hasCompactSupport {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    {U : Set G} (hU : IsCompact U) (hμU : μ U = 1) (hμ'U : μ' U = 1)
    {f : G → ℝ} (hf : HasCompactSupport f) :
    ∫ x, f x ∂μ' = ∫ x, f x ∂μ := by
  have hc : haarScalarFactor μ' μ = 1 := by
    have h := measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ (s := U)
      (by rwa [hU.isClosed.closure_eq])
    rw [hμU, hμ'U, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact_mod_cast h.symm
  have hres : μ'.restrict (tsupport f) = μ.restrict (tsupport f) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
      measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
        (hf.isCompact.closure_of_subset Set.inter_subset_right), hc, one_smul]
  have h1 : ∫ x in tsupport f, f x ∂μ' = ∫ x, f x ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have h2 : ∫ x in tsupport f, f x ∂μ = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  rw [← h1, ← h2, hres]

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem scalar_comm (c : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (c : L ⊗[K] A) * (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * Matrix.scalar (Fin 2) (c : L ⊗[K] A)
  exact (Matrix.scalar_commute (c : L ⊗[K] A) (fun r => Commute.all _ r) _).eq

theorem scalar_central (c : (L ⊗[K] A)ˣ) (x δ y : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * (x * δ * y) =
      x * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) * y := by
  simp only [← mul_assoc]
  rw [scalar_comm]

theorem twistedCentralizer_scalar_mul (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      twistedCentralizer K L A σ δ := by
  ext t
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, ← scalar_central]
  exact mul_left_cancel_iff

end Algebra

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

noncomputable def congrEquiv (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≃ₜ*
      twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) :=
  { MulEquiv.subgroupCongr (twistedCentralizer_scalar_mul K L A σ c δ).symm with
    continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
    continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }

theorem congrEquiv_apply_val (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (t : twistedCentralizer K L A σ δ) :
    ((congrEquiv K L A σ c δ t : twistedCentralizer K L A σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) : GL (Fin 2) (L ⊗[K] A)) = (t : GL (Fin 2) (L ⊗[K] A)) :=
  rfl

variable [IsTopologicalRing A]

theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  have h : Continuous
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  exact h

theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact Continuous.units_map _ ((continuous_id.matrix_map (continuous_sigmaTensor K L A σ)) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => m.map (sigmaTensor K L A σ))

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hσ := continuous_sigmaGL K L A σ
  have hset : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [hset]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul (hσ.inv)) continuous_const

end Topology

end K42CTFIN

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : (L ⊗[K] v.adicCompletion K)ˣ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)))
    (hτ'' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) τ'')
    (hτ''1 : τ'' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
      (fun x => φv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I) :
    AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) τ'' φv I := by

  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.borelSpace_glBorelOf _
  letI m1 : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  letI m2 : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) :=
    AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  have hcl := K42CTFIN.isClosed_twistedCentralizer K L (v.adicCompletion K) σ
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) → GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) := hemb.locallyCompactSpace
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI : Measure.IsHaarMeasure τ'' := hτ''

  set e := K42CTFIN.congrEquiv K L (v.adicCompletion K) σ c δ with he
  haveI : Measure.IsHaarMeasure (τ'.map e) := ContinuousMulEquiv.isHaarMeasure_map τ' e
  have hUmeas : MeasurableSet (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v :
      Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))) :=
    ((AutomorphicForm.isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).measurableSet
  have hem : Measurable (e : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ →
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) := e.continuous.measurable
  have hU1 : (τ'.map e) (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 := by
    rw [Measure.map_apply hem hUmeas]
    exact hτ'1
  have hUc : IsCompact (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v :
      Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))) :=
    hemb.isCompact_preimage (AutomorphicForm.isCompact_semiLocalIntegralSet K L v)

  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, hIeq⟩ := hI
  refine ⟨w, ⟨hw0, hwm, hws, fun x hx => ?_⟩, ?_⟩
  · have hx' : (fun y => φv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * y))
        (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 := by
      simp only
      rwa [K42CTFIN.scalar_central]
    have h1 := hw1 x hx'
    have hfx : HasCompactSupport (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) => w ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x)) :=
      (hws.comp_homeomorph (Homeomorph.mulRight x)).comp_isClosedEmbedding hemb
    rw [K42CTFIN.integral_eq_of_hasCompactSupport τ'' (τ'.map e) hUc hU1 hτ''1 hfx]
    have h2 := integral_map_equiv (μ := τ') e.toHomeomorph.toMeasurableEquiv
      (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) => w ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x))
    exact h2.trans h1
  · rw [hIeq]
    congr 1
    ext x
    simp only
    rw [K42CTFIN.scalar_central]

end S_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
end P2MW
export P2MW.S_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul (solution)
