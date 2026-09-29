-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/44edb224-615b-5aac-aa7c-66bee2f91ac4

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub
p2m_attr_erase "instance" "instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt"
p2m_attr_erase "simp" "LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace G4CDIL

open NumberField.TateGlobal

section Haar

variable (K : Type) [Field K] [NumberField K]

theorem ideleNorm_inv (y : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K y⁻¹ = (ideleNorm K y)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← ideleNorm_mul, inv_mul_cancel]; simp [ideleNorm])

theorem integral_comp_inv_mul [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] (y : (AdeleRing (𝓞 K) K)ˣ) (f : AdeleRing (𝓞 K) K → ℂ) :
    ∫ r, f (((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * r) ∂μK = ((ideleNorm K y : ℝ) : ℂ) * ∫ u, f u ∂μK := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  have h1 : ∫ r, f (((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * r) ∂μK = ∫ x, f x ∂(DomMulAct.mk y • μK) := by
    rw [integral_domSMul]
    rfl
  have h2 : (DomMulAct.mk y • μK) = distribHaarChar (AdeleRing (𝓞 K) K) y • μK := by
    have h := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk y • μK) μK
    rwa [addHaarScalarFactor_smul_eq_distribHaarChar] at h
  rw [h1, h2, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

end Haar

end G4CDIL

open NumberField.TateGlobal in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]

    (hDbc : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
        AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) :
    ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) *
        ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
              (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) *
                  ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK else 0)) ∂νZL) ∂(maximalCompactHaar L) := by
  intro t y
  have hℓ : 0 < Module.finrank K L := Module.finrank_pos
  have hy0 : 0 < ideleNorm K y := ideleNorm_pos y
  have ht0 : 0 < ideleNorm L t := ideleNorm_pos t

  have hG : ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ),
      (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) =
      (fun x : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (M4aHerbrand.Bridge.genuineβ K L ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) := by
    intro k ζ
    funext x
    have h1 : x * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
        M4aHerbrand.Bridge.genuineβ K L ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
      rw [mul_inv, Units.val_mul, ← map_inv,
        show ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L y⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = M4aHerbrand.Bridge.genuineβ K L ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) from rfl]
      ring
    have h2 : M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ =
        M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹ := by
      rw [map_mul, hDbc, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rw [h1, h2]

  have hdil : ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (r : AdeleRing (𝓞 K) K),
      tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r =
      ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * r) := by
    intro k ζ r
    rw [hG k ζ]
    exact (TraceFibrePushforward.lintegral_traceFibre_mul_and_tracePushforward_mul K L y⁻¹).2
      (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r

  have hCT : ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ),
      ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK =
      ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * (((ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK) := by
    intro k ζ
    simp_rw [hdil k ζ]
    rw [integral_const_mul, G4CDIL.integral_comp_inv_mul K μK y]

  have hFS : ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ),
      (∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) =
      ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * ∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) := by
    intro k ζ
    simp_rw [hdil k ζ]
    rw [← mul_finsum]
    exact congrArg (fun s : ℂ => ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * s)
      (finsum_congr fun η => by rw [mul_comm (((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))])

  have hC : ((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ) = ideleNorm K y ^ (Module.finrank K L - 1) := by
    rw [G4CDIL.ideleNorm_inv, inv_pow, inv_inv]
  have hN : ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) = ideleNorm L t * ideleNorm K y ^ Module.finrank K L := by
    rw [ideleNorm_mul, NumberField.TateGlobal.ideleNorm_idelesBaseChange]
  have hreal : ideleNorm K y ^ (Module.finrank K L - 1) * (ideleNorm L t * ideleNorm K y ^ Module.finrank K L)⁻¹ =
      (ideleNorm L t)⁻¹ * (ideleNorm K y)⁻¹ := by
    obtain ⟨m, hm⟩ : ∃ m, Module.finrank K L = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hℓ).symm⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    field_simp

  have hk : ∀ k : adelicMaximalCompact L,
      (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y))⁻¹ : ℝ) : ℂ) =
      (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) *
        ∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL := by
    intro k
    have hζ : ∀ ζ : (AdeleRing (𝓞 L) L)ˣ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) =
        ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * (((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0))) := by
      intro ζ
      rw [hFS k ζ, hCT k ζ]
      split_ifs <;> ring
    have hI : (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) =
        ∫ ζ, ((((NumberField.TateGlobal.ideleNorm K y⁻¹ ^ (Module.finrank K L - 1))⁻¹ : ℝ)) : ℂ) * (((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0))) ∂νZL := integral_congr_ae (ae_of_all _ hζ)
    rw [hI, integral_const_mul, hN, hC, ← hreal]
    push_cast
    ring
  calc (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))
      = ∫ k, (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) *
        ∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL ∂(maximalCompactHaar L) := integral_congr_ae (ae_of_all _ hk)
    _ = _ := integral_const_mul _ _

end S_AutomorphicForm_TwistedBruhat_unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub (solution)
