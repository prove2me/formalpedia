-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_09
-- name    : InfoLossLAR_NativeBundle_09
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T16:36:48.141502+00:00
-- url     : https://prove2.me/theorems/53c928a6-d269-4529-a321-90453d113354
-- title:
--   Gaussian affine transport and rational current-family programs
-- statement:
--   This package defines current hidden-source and affine transport laws, Gaussian window data, local rational approximation programs, current cycle and profile evaluators, and the rational background-population program together with its explicit bound and error constants.
--
--   A numerical evaluation returns a rational value $r$ whose real interpretation is
--   $$\operatorname{val}(r)\in\mathbb R,$$
--   while the corresponding ideal finite response remains a separately defined real coefficient family. The stored inputs include the fixed order, precision, queue and palette coordinates required by each program.
--
--   This separation lets later theorems compare the actual rational computation with its ideal Gaussian and coefficient semantics. No numerical error estimate is asserted merely by defining its error constants.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/CurrentAFT/CurrentHiddenSourceTransport.lean, lean/CurrentAFT/CurrentPublicAffineSample.lean, lean/CurrentAFT/CurrentZeroFiber.lean, lean/CurrentAFT/CurrentAffineTransport.lean, lean/CurrentAFT/CurrentAffineSampleAgreement.lean, lean/CurrentAFT/CurrentProtectedSourceParts.lean, lean/CurrentAFT/CurrentProtectedAffineLaw.lean, lean/CurrentAFT/CurrentProtectedSampleFubini.lean, lean/CurrentAFT/ActualGaussianAffine.lean, lean/CurrentAFT/ActualGaussianAccuracy.lean, lean/CurrentAFT/BinaryTrimmedPair.lean, lean/CurrentAFT/WindowGaussianSampler.lean, lean/CurrentAFT/CurrentGaussianBits.lean, lean/CurrentAFT/CyclePatternProgram.lean, lean/CurrentAFT/PublicParameterProgram.lean, lean/CurrentAFT/LocalDiffuseProgram.lean, lean/CurrentAFT/BinaryDiffuseProgram.lean, lean/CurrentAFT/BinaryDiffuseCurrent.lean, lean/CurrentAFT/BinaryProposalMetadata.lean, lean/CurrentAFT/ActualCoordinateBounds.lean, lean/CurrentAFT/CalibrationPointCoordinates.lean, lean/CurrentAFT/CalibrationCoordinateError.lean, lean/CurrentAFT/LocalMarkedProgram.lean, lean/CurrentAFT/LocalPairProgram.lean, lean/CurrentAFT/RationalFamilyProductProgram.lean, lean/CurrentAFT/RationalBackgroundTable.lean, lean/CurrentAFT/BinaryActivationProgram.lean, lean/CurrentAFT/BinaryGaussianAverage.lean, lean/CurrentAFT/BinaryMarkedKernel.lean, lean/CurrentAFT/BinaryMarkedCurrent.lean, lean/CurrentAFT/BinaryPairProgram.lean, lean/CurrentAFT/RationalProposalProgram.lean, lean/CurrentAFT/RationalFirstResponseProgram.lean, lean/CurrentAFT/RationalDensityInverseProgram.lean, lean/CurrentAFT/RationalTensorInverseProgram.lean, lean/CurrentAFT/RationalMassLiftProgram.lean, lean/CurrentAFT/RationalMassCertificateTable.lean, lean/CurrentAFT/RationalConditionalPairProgram.lean, lean/CurrentAFT/RationalBackgroundProfiles.lean, lean/CurrentAFT/RationalBackgroundDensities.lean, lean/CurrentAFT/RationalPairedLiftProgram.lean, lean/CurrentAFT/CurrentCycleEntryProgram.lean, lean/CurrentAFT/RootSignedMassProgram.lean, lean/CurrentAFT/RootMassColumns.lean, lean/CurrentAFT/RationalRootMassProgram.lean, lean/CurrentAFT/ActualRootProjectionData.lean, lean/CurrentAFT/RootReferenceColumns.lean, lean/CurrentAFT/RationalRootProfileProgram.lean, lean/CurrentAFT/RationalDiffuseResidualProgram.lean, lean/CurrentAFT/RationalDiffuseCertificateProgram.lean, lean/CurrentAFT/RationalMassLiftTensorProgram.lean, lean/CurrentAFT/RationalDiffuseFamilyProgram.lean, lean/CurrentAFT/RationalFamilyPowerProgram.lean, lean/CurrentAFT/RationalFamilyPullback.lean, lean/CurrentAFT/RationalActualFamilyApproximation.lean, lean/CurrentAFT/RationalBackgroundProgram.lean, lean/CurrentAFT/RationalMarkedSeedProgram.lean, lean/CurrentAFT/RationalMarkedSeedBounds.lean, lean/CurrentAFT/RationalMarkedCertificateProgram.lean, lean/CurrentAFT/RationalPrimaryDeviationProgram.lean, lean/CurrentAFT/RationalMarkedPairProgram.lean, lean/CurrentAFT/RationalPairQuadraticProgram.lean, lean/CurrentAFT/RationalBackgroundLinearProgram.lean, lean/CurrentAFT/RationalScalarFamilyAverage.lean, lean/CurrentAFT/RationalLegBackgroundProgram.lean, lean/CurrentAFT/RationalFamilyPowerBounds.lean, lean/CurrentAFT/RationalPopulationApproximation.lean, lean/CurrentAFT/RationalBackgroundPopulationProgram.lean, lean/CurrentAFT/BinaryBackgroundPopulationCounts.lean, lean/CurrentAFT/CalibrationTableNorm.lean, lean/CurrentAFT/CalibrationMatrixApproximation.lean, lean/CurrentAFT/BinaryCalibrationIteration.lean, lean/CurrentAFT/BinaryFixedScalarProgram.lean, lean/CurrentAFT/FamilyProductSyntax.lean, lean/CurrentAFT/BinaryFamilyProduct.lean, lean/CurrentAFT/FixedFamilyPrograms.lean, lean/CurrentAFT/BinaryFamilyArithmetic.lean, lean/CurrentAFT/BinaryMassLiftFormula.lean, lean/CurrentAFT/BinaryRankOneFunctional.lean, lean/CurrentAFT/BinaryRationalCompare.lean, lean/CurrentAFT/BinaryMassLiftKernel.lean, lean/CurrentAFT/BinaryWindowAverage.lean, lean/CurrentAFT/BinaryAnchorProgram.lean, lean/CurrentAFT/BinaryProfileKernel.lean, lean/CurrentAFT/BinarySeedAverage.lean, lean/CurrentAFT/BinaryProfileProgram.lean, lean/CurrentAFT/BinaryProfileTables.lean, lean/CurrentAFT/BinaryAnchorTable.lean, lean/CurrentAFT/BinaryCenterFormula.lean, lean/CurrentAFT/BinaryCenterKernel.lean, lean/CurrentAFT/BinaryBodyKernel.lean, lean/CurrentAFT/BinaryBodyProgram.lean, lean/CurrentAFT/BinaryPrimaryRaw.lean, lean/CurrentAFT/BinaryProposalGuard.lean, lean/CurrentAFT/BinaryPrimaryTable.lean, lean/CurrentAFT/BinaryReferenceTables.lean, lean/CurrentAFT/BinaryFirstInverseProgram.lean, lean/CurrentAFT/BinaryMassLiftResources.lean, lean/CurrentAFT/BinaryFirstInverseResources.lean, lean/CurrentAFT/BinaryMassLiftInput.lean, lean/CurrentAFT/BinaryPaletteLookup.lean, lean/CurrentAFT/BinaryRootConvolutionKernel.lean, lean/CurrentAFT/BinaryRootConvolution.lean, lean/CurrentAFT/BinaryRootConvolutionResources.lean, lean/CurrentAFT/BinarySafeProfile.lean, lean/CurrentAFT/BinaryUnsafeProfile.lean, lean/CurrentAFT/BinaryShiftedSafeProfile.lean, lean/CurrentAFT/BinaryRootProfile.lean, lean/CurrentAFT/BinaryRootPreProfileResources.lean, lean/CurrentAFT/BinaryCoefficientScalarAverage.lean, lean/CurrentAFT/BinaryBinomialCoefficient.lean, lean/CurrentAFT/BinaryFamilyPower.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 b0faddd7ba62db308a4069a56f01cc873874910e29f66db5e23d0929cf7fc715. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 b0faddd7ba62db308a4069a56f01cc873874910e29f66db5e23d0929cf7fc715. Two same-type proposition proofs, countsWorkPolynomial_eval and center_value, were shortened relative to this source; every algorithm definition is unchanged. Exact9429native+2099runtime publictypes andrecursive standard-three-axiom audits passed. OriginalsourceSHA256 b0faddd7ba62db308a4069a56f01cc873874910e29f66db5e23d0929cf7fc715;optimizedsourceSHA256 2b81ae82409fd1e0e6ff5c3fb42c02c8fff03d5a045b0cb95f8e143a78d275f1. Optimizationreceipt native09_proof_optimized/optimization.json.

import Definitions.Def_InfoLossLAR_NativeBundle_08


























section













/-! # Gaussian replacement with the finite public closure retained

Only the dimension-many hidden Gaussian coordinates are unbounded here.
The public closing edge is already drawn from its finite clipped law.
The protected product is exactly the complete-source protected law under
the proved source numbering.
-/
namespace CurrentAFT.CurrentHiddenSourceTransport

open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.dimension Parameters.legCount
  sourceCount cutoff sourceNumbering

abbrev HiddenWord (security : ℕ) := ProtectedWord (hiddenCutoff security)
abbrev Closure (security : ℕ) := Window (DiffuseProfiles.edgeCutoff security)

def hiddenLaw (security : ℕ) : FiniteDist (HiddenWord security) :=
  GaussianProductProtection.protectedLaw (width security) (hiddenCutoff security)

def closureLaw (security : ℕ) : FiniteDist (Closure security) :=
  windowGaussian (width security) (DiffuseProfiles.edgeCutoff security)

def joinProtected (security : ℕ) (pair : HiddenWord security × Closure security) :
    ProtectedWord (cutoff security) := fun index =>
  ⟨(splitWord security).symm
    (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val) index, by
    obtain ⟨hidden | point, rfl⟩ := (sourceNumbering security).surjective index
    · simpa only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inl,
        sourceEmbedding, hiddenCutoff, Function.Embedding.coeFn_mk] using (pair.1 hidden).property
    · cases point
      simpa only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inr, cutoff_closure]
        using pair.2.property⟩

def splitProtected (security : ℕ) : ProtectedWord (cutoff security) ≃
    HiddenWord security × Closure security where
  toFun word := (hiddenProtectedWord security word, protectedClosure security word)
  invFun := joinProtected security
  left_inv word := by
    apply (sourceEmbedding (cutoff security)).injective
    exact (splitWord security).symm_apply_apply (sourceEmbedding (cutoff security) word)
  right_inv pair := by
    apply Prod.ext
    · apply (sourceEmbedding (hiddenCutoff security)).injective
      funext index
      change (splitWord security).symm
        (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val)
          (sourceNumbering security (.inl index)) = _
      simp only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inl]
    · apply Subtype.ext
      change (splitWord security).symm
        (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val)
          (sourceNumbering security (.inr ())) = _
      simp only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inr]





def hiddenBudget (security : ℕ) : ℝ :=
  ∑ index : Fin (Parameters.dimension security),
    clippingProbability (width security) (hiddenCutoff security index + 1 : ℕ) (width_pos security)





def hiddenGaussianOutput {Output : Type*} [Fintype Output] (security : ℕ)
    (channel : (Fin (Parameters.dimension security) → ℤ) → FiniteDist Output) : FiniteDist Output :=
  FiniteDist.countableMix (fullMass (width security) (Parameters.dimension security))
    (fullMass_nonneg (width security) (width_pos security) (Parameters.dimension security))
    (fullMass_summable (width security) (width_pos security) (Parameters.dimension security))
    (fullMass_sum (width security) (width_pos security) (Parameters.dimension security)) channel



end
end CurrentAFT.CurrentHiddenSourceTransport

end

section



















/-! # A complete positive source-independent public affine experiment

The core, all complete charts, and the finite closing Gaussian edge are
sampled before any hidden source coordinate.  The constructor always
returns integral invertible affine data, including on zero-probability
invalid records through its identity fallback.
-/
namespace CurrentAFT.CurrentPublicAffineSample
open AFT CurrentAffineData CurrentAffineLegCarry AffineFlagCalibration ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean CurrentPublicSupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

def chartsLaw (security : ℕ) (core : Core security) : FiniteDist (Charts security) :=
  FiniteDist.independent (fun leg => completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)

abbrev Sample (security : ℕ) := (Core security × Charts security) × Edge security

def law (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist (Sample security) :=
  (FiniteDist.joint (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
    (chartsLaw security)).prod (DiffuseProfiles.edgeLaw security)

def realize (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (sample : Sample security) :
    Data security := assemble security layout sample.1.1 sample.1.2 sample.2.val









end
end CurrentAFT.CurrentPublicAffineSample

end

section















/-! # The actual fixed rounding label and its uniform zero fiber -/
namespace CurrentAFT.CurrentZeroFiber
open AFT CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

abbrev Word (security : ℕ) := Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)

def coordinates (security : ℕ) : Word security ≃
    (Fin (edgeCount security) → ZMod (Parameters.modulus security)) × ZMod (Parameters.modulus security) where
  toFun word := (fun edge => word (coordinateNumbering security (.inl edge)),
    word (coordinateNumbering security (.inr ())))
  invFun pair index := Sum.elim pair.1 (fun _ : Unit => pair.2) ((coordinateNumbering security).symm index)
  left_inv word := by
    funext index
    obtain ⟨edge | point, rfl⟩ := (coordinateNumbering security).surjective index
    · simp
    · cases point; simp
  right_inv pair := by simp

theorem column_charge (security : ℕ) :
    totalCharge (injectionColumn (edgeCount security) (Parameters.modulus security)) =
      (Parameters.modulus security : ℤ) := by
  apply totalCharge_injectionColumn
  have hb : Parameters.modulus security ≤ Parameters.bodySize security := by
    rw [Parameters.bodySize_eq]
    exact Nat.le_mul_of_pos_right _ (pow_pos (Parameters.base_pos security) _)
  have hp := LobsterCoordinates.current_body_positive security
  dsimp only [edgeCount, bodyEdges]
  omega

/-- This is the carry label of the manuscript's fixed matrix with the
path columns first and the injection column last. -/
def label (security : ℕ) (word : Word security) : ZMod (Parameters.modulus security) :=
  fiberLabel (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (coordinates security word)

def ZeroFiber (security : ℕ) := {word : Word security // label security word = 0}

instance fiberFintype (security : ℕ) : Fintype (ZeroFiber security) := by
  unfold ZeroFiber
  infer_instance

def fiberEquiv (security : ℕ) : ZeroFiber security ≃
    AFT.ZeroFiber (edgeCount security) (Parameters.modulus security)
      (injectionColumn _ (Parameters.modulus security)) where
  toFun word := ⟨coordinates security word.val, word.property⟩
  invFun word := ⟨(coordinates security).symm word.val, by simpa [label] using word.property⟩
  left_inv word := by apply Subtype.ext; exact (coordinates security).symm_apply_apply word.val
  right_inv word := by apply Subtype.ext; exact (coordinates security).apply_symm_apply word.val

instance fiberNonempty (security : ℕ) : Nonempty (ZeroFiber security) := by
  obtain ⟨word⟩ : Nonempty (AFT.ZeroFiber (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security))) := inferInstance
  exact ⟨(fiberEquiv security).symm word⟩

def uniformFiber (security : ℕ) : FiniteDist (Word security) :=
  (FiniteDist.uniform (ZeroFiber security)).map Subtype.val



def endpointCoordinates (security : ℕ) : Word security ≃
    (Fin (edgeCount security + 1) → ZMod (Parameters.modulus security)) :=
  Equiv.arrowCongr (dimensionEquiv security).symm (Equiv.refl _)





def rawPullback (n q : ℕ) [NeZero q] (column : Fin (n + 1) → ℤ)
    (hcolumn : totalCharge column = (q : ℤ)) (endpoint : Fin (n + 1) → ZMod q) :
    (Fin n → ZMod q) × ZMod q :=
  if hzero : ∑ index, endpoint index = 0 then
    (canonicalEndpointEquiv n q column hcolumn ⟨endpoint, hzero⟩).val else 0



def pullback (security : ℕ) (endpoint : Word security) : Word security :=
  (coordinates security).symm (rawPullback (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (column_charge security)
      (endpointCoordinates security endpoint))









end
end CurrentAFT.CurrentZeroFiber

end

section





















/-! # Actual Gaussian and protected affine output laws

The complete finite public law is independent of the dimension-many hidden
Gaussian inputs. The protected experiment uses the identical affine data.
-/
namespace CurrentAFT.CurrentAffineTransport
open AFT CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport
  CurrentSourceProtection CurrentSourceLayout CurrentAffineProtectedCarry CurrentZeroFiber
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

def output (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : Fin (Parameters.dimension security) → ℤ) : Word security :=
  fun index => ((realize security layout sample).eval input index : ZMod (Parameters.modulus security))

def endpoint (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : Fin (Parameters.dimension security) → ℤ) : Word security :=
  fun vertex => (CurrentAffineLoad.rounding security ((realize security layout sample).eval input) vertex :
    ZMod (Parameters.modulus security))

def gaussianLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => hiddenGaussianOutput security
    (fun input => (FiniteDist.uniform Unit).map (fun _ => output security layout sample input)))

def protectedLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => (hiddenLaw security).map
    (fun input => output security layout sample (sourceEmbedding (hiddenCutoff security) input)))

def protectedEndpointLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => (hiddenLaw security).map
    (fun input => endpoint security layout sample (sourceEmbedding (hiddenCutoff security) input)))













end
end CurrentAFT.CurrentAffineTransport

end

section

















/-! # The actual public sample realizes the completed physical endpoint

The public closing edge is the same finite sampled edge in both
descriptions. The protected hidden word is not resampled for the carry or
physical endpoint conclusions.
-/
namespace CurrentAFT.CurrentAffineSampleAgreement

open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def sourceWord (security : ℕ) (sample : Sample security) (input : HiddenWord security) :
    ProtectedWord (cutoff security) := joinProtected security (input, sample.2)

def physicalWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : HiddenWord security) : CurrentZeroFiber.Word security :=
  fun index => RefinedPublicOutput.embed security
    (outputWord security layout sample.1.1 sample.1.2 (sourceWord security sample input) index)





end
end CurrentAFT.CurrentAffineSampleAgreement

end

section

















/-! # Exact protected body, first-leg, second-leg and shared-queue product

This is a reindexing of the actual clipped latent scalars. It retains the
entire closed-cycle latent word, both inputs at every leg, and one queue.
-/
namespace CurrentAFT.CurrentProtectedSourceParts

open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout
  CurrentAffineProtectedCarry GaussianProductProtection ActualCycleMeanMGF
  AffineFlagCalibration DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Parts (security : ℕ) := (BodyIndex security → Edge security) ×
  ((Fin (Parameters.legCount security) → Scalar security) ×
    ((Fin (Parameters.legCount security) → Scalar security) × Scalar security))

abbrev PartIndex (security : ℕ) := BodyIndex security ⊕
  ((Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit)

def partsNumbering (security : ℕ) : PartIndex security ≃ Fin (sourceCount security) :=
  (Equiv.sumCongr (Equiv.refl _) (auxNumbering security)).trans finSumFinEquiv

theorem partsNumbering_body (security : ℕ) (body : BodyIndex security) :
    partsNumbering security (.inl body) = bodyPosition security body := rfl

theorem partsNumbering_aux (security : ℕ)
    (index : (Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit) :
    partsNumbering security (.inr index) = auxPosition security (auxNumbering security index) := rfl

theorem auxNumbering_queue (security : ℕ) :
    auxNumbering security (.inr ()) = Fin.last (Parameters.legCount security * 2) := by
  apply Fin.ext
  simp [auxNumbering, CurrentAffineGeometry.unitToFinOne]

def partValue (security : ℕ) (parts : Parts security) : PartIndex security → ℤ
  | .inl body => (parts.1 body).val
  | .inr (.inl (.inl leg)) => (parts.2.1 leg).val
  | .inr (.inl (.inr leg)) => (parts.2.2.1 leg).val
  | .inr (.inr _) => parts.2.2.2.val

def joinParts (security : ℕ) (parts : Parts security) : ProtectedWord (cutoff security) :=
  fun index => ⟨partValue security parts ((partsNumbering security).symm index), by
    obtain ⟨body | ((first | second) | point), rfl⟩ := (partsNumbering security).surjective index
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_body, cutoff_body] using (parts.1 body).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using (parts.2.1 first).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using (parts.2.2.1 second).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using parts.2.2.2.property⟩

def splitParts (security : ℕ) : ProtectedWord (cutoff security) ≃ Parts security where
  toFun word := (protectedBody security word,
    (protectedFirst security word, (protectedSecond security word,
      protectedAux security word (Fin.last (Parameters.legCount security * 2)))))
  invFun := joinParts security
  left_inv word := by
    apply (sourceEmbedding (cutoff security)).injective
    funext index
    obtain ⟨body | ((first | second) | point), rfl⟩ := (partsNumbering security).surjective index
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_body]
      rfl
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux]
      rfl
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux]
      rfl
    · cases point
      simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux, auxNumbering_queue]
      rfl
  right_inv parts := by
    apply Prod.ext
    · funext index
      apply Subtype.ext
      change partValue security parts ((partsNumbering security).symm (bodyPosition security index)) = _
      rw [← partsNumbering_body, Equiv.symm_apply_apply]
      rfl
    · apply Prod.ext
      · funext index
        apply Subtype.ext
        change partValue security parts ((partsNumbering security).symm
          (auxPosition security (auxNumbering security (.inl (.inl index))))) = _
        rw [← partsNumbering_aux, Equiv.symm_apply_apply]
        rfl
      · apply Prod.ext
        · funext index
          apply Subtype.ext
          change partValue security parts ((partsNumbering security).symm
            (auxPosition security (auxNumbering security (.inl (.inr index))))) = _
          rw [← partsNumbering_aux, Equiv.symm_apply_apply]
          rfl
        · apply Subtype.ext
          change partValue security parts ((partsNumbering security).symm
            (auxPosition security (Fin.last (Parameters.legCount security * 2)))) = _
          rw [← auxNumbering_queue, ← partsNumbering_aux, Equiv.symm_apply_apply]
          rfl

def legInputLaw (security : ℕ) : FiniteDist (Fin (Parameters.legCount security) → Scalar security) :=
  FiniteDist.independent (fun _ => scalarLaw security)

def partsLaw (security : ℕ) : FiniteDist (Parts security) :=
  (FiniteDist.retype (ActualFockBound.latentLaw security)).prod
    ((legInputLaw security).prod ((legInputLaw security).prod (scalarLaw security)))





end
end CurrentAFT.CurrentProtectedSourceParts

end

section


















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.FiniteProductFubini
end CurrentAFT.FiniteProductFubini






/-!
# The protected source law of the actual public affine sample

The local calculation keeps the complete public chart draw outside both
hidden source coordinates, and keeps the entire cycle latent and shared
queue fixed until the final mixture.
-/

namespace CurrentAFT.CurrentProtectedAffineLaw

open AFT AffineFlagCalibration ActualAffineCompletedOutput ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock ActualBlockMean
  ProposalPrimary DiffuseProfiles PublicAuxiliaryFubini FiniteProductFubini PublicCoefficientOutput
open HistogramNormalization PhysicalSynthesis
open CurrentSourceProtection CurrentProtectedSourceParts GaussianProductProtection
open scoped BigOperators Classical

noncomputable section

local instance protectedLawFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance protectedLawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev ChartWord (security : ℕ) :=
  Fin (Parameters.legCount security) → Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))
abbrev ScalarWord (security : ℕ) := Fin (Parameters.legCount security) → AffineFlagCalibration.Scalar security

def chartProduct (security : ℕ) (core : Core security) : FiniteDist (ChartWord security) :=
  FiniteDist.independent (fun leg => completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)

def scalarProduct (security : ℕ) : FiniteDist (ScalarWord security) :=
  FiniteDist.independent (fun _ => scalarLaw security)

def rawBlockWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) (charts : ChartWord security)
    (first second : ScalarWord security) : Sigma (Slots security) → RefinedPublicOutput.Palette security
  | ⟨.inl leg, slot⟩ => evaluateTriple security
      (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg) (charts leg) (first leg) (second leg) slot
  | ⟨.inr (.inl center), _⟩ => shiftEquiv security
      (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | ⟨.inr (.inr point), _⟩ => shiftEquiv security
      (queueRoots security layout core.bodyPermutation latent point + queue.val) (core.queueBaselines point)

def conditionalChartOutput (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → RefinedPublicOutput.Palette security) :=
  (chartProduct security core).mix (fun charts => (scalarProduct security).mix (fun first =>
    (scalarProduct security).map (rawBlockWord security layout core queue latent charts first)))

def delta {State : Type*} (first second : State) : ℝ := if first = second then 1 else 0











def completedPartsLaw (security : ℕ) : FiniteDist (Parts security) :=
  (FiniteDist.retype (ActualFockBound.latentLaw security)).prod
    ((scalarProduct security).prod ((scalarProduct security).prod (scalarLaw security)))



def rawOutputWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : ChartWord security) (parts : Parts security) :
    Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security :=
  AFT.relabel (renameWord (flatten security)
    (rawBlockWord security layout core parts.2.2.2 parts.1 charts parts.2.1 parts.2.2.1)) core.endpointPermutation



def protectedChartPalette (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :=
  (chartProduct security core).mix (fun charts => (FiniteDist.retype (protectedSourceLaw security)).map
    (CurrentAffinePhysicalEndpoint.outputWord security layout core charts))











def protectedChartMapped (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Residue security) :=
  (protectedChartPalette security layout core).map
    (fun word index => RefinedPublicOutput.embed security (word index))



end
end CurrentAFT.CurrentProtectedAffineLaw

end

section

















/-! # Regrouping the actual finite public and protected source draws -/
namespace CurrentAFT.CurrentProtectedSampleFubini
open AFT CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint CurrentAffineSampleAgreement
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



def corePhysicalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (CurrentZeroFiber.Word security) :=
  (chartsLaw security core).mix (fun charts => (protectedSourceLaw security).map
    (fun word index => RefinedPublicOutput.embed security (outputWord security layout core charts word index)))







end
end CurrentAFT.CurrentProtectedSampleFubini

end

section



















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.FiniteEnumeration
end CurrentAFT.FiniteEnumeration






/-! # Actual Gaussian affine transport under the complete positive public law

All physical, calibration, source-protection, carry and zero-fiber premises
are discharged here. This analytic finite public law is not yet the full
finite-bit polynomial-time sampler required by the constructive theorem.
-/
namespace CurrentAFT.ActualGaussianAffine
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber CurrentProtectedSampleFubini
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩







end
end CurrentAFT.ActualGaussianAffine

end

section















/-! # Fixed-order accuracy of the actual ideal affine law

The calibration order is exactly `4 * accuracyOrder + 267`. All analytical
premises are discharged. This ideal finite law still requires the separately
developed finite-bit implementation before it is a uniform PPT sampler.
-/
namespace CurrentAFT.ActualGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAffine
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩







end
end CurrentAFT.ActualGaussianAccuracy

end

section






















/-! # Boolean-list evaluation of one genuine averaged trimmed pair

No rational probability is encoded as advice: the anchor membership,
shifted slice, actual slice denominator and final product are computed
by binary operations on the supplied integer representations.
-/
namespace CurrentAFT.BinaryTrimmedPair
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem signed_negate (sign : Bool) (digits : List Bool) :
    signedValue (!sign) digits = -signedValue sign digits := by
  cases sign <;> simp [signedValue]

def pairShift (colors first second : List Bool) : SignedResult :=
  let total := add false first second
  let last := signedAdd false true colors [true]
  let result := signedAdd false (!last.negative) total.digits last.digits
  ⟨result.negative, result.digits, total.work + last.work + result.work + 3⟩





def pair (startSign sourceSign : Bool) (colors width start source first second : List Bool) : RationalResult :=
  let shift := pairShift colors first second
  let argument := signedAdd shift.negative sourceSign shift.digits source
  let anchor := binaryIntervalProbability startSign argument.negative start width argument.digits
  let slice := binarySliceProbability false false shift.negative false colors [true] shift.digits first
  let result := RationalBits.multiply anchor.data slice.data
  ⟨result.data, shift.work + argument.work + anchor.work + slice.work + result.work + 4⟩



def pairWork (bits : ℕ) : ℕ :=
  60*(bits+1) + 20*(bits+2)+8 + binaryIntervalProbabilityWork (bits+3) +
    binarySliceProbabilityWork (bits+2) + RationalBits.primitiveWorkBound (bits+5) + 4





noncomputable def pairWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(bits+1) + 20*(bits+2)+8 +
    (200*(bits+5) + RationalBits.primitiveWorkPolynomial (bits+3)) +
    (100*(bits+4) + 20*(bits+4)+11 + 200*(bits+7) + RationalBits.primitiveWorkPolynomial (bits+5)) +
    RationalBits.primitiveWorkPolynomial (bits+5) + 4



end CurrentAFT.BinaryTrimmedPair

end

section








/-! # Executable fair-bit sampling of the current Gaussian windows

The finite rational pi/exponential programs and integer ticket rounding
are instantiated at the current squared width. These are actual functions
of finite bit tapes, with exact window support and a proved whole-law
error. This module alone does not give the full affine sampler's runtime.
-/
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def squaredWidth (security : ℕ) : ℚ := (security + 2 : ℚ)^2





/-- The precision input changes a single finite rational program, rather
than choosing an arbitrary finite real law by existence. -/
def draw (security cutoff bits : ℕ) : (Fin (windowTicketBits cutoff bits) → Fin 2) → Window cutoff :=
  windowGaussianDraw (squaredWidth security) cutoff bits



noncomputable section









end
end CurrentAFT.WindowGaussianSampler

end

section






















/-! # Current Gaussian tables computed by Boolean-list arithmetic

The squared width is constructed by actual counter and binary encoding
programs. Every Gaussian series, rational normalization and array entry
is computed by the existing binary implementation. The cost is the
repository's explicit Boolean/list/counter work, not a TM compilation.
-/
namespace CurrentAFT.CurrentGaussianBits
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits Polynomial
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def widthCode (security : ℕ) : RationalResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let encoded := ofCounter square.count
  ⟨encoded.data, base.work + square.work + encoded.work + 3⟩

theorem widthCode_value (security : ℕ) : (widthCode security).data.decode = (security + 2 : ℚ)^2 := by
  simp only [widthCode, ofCounter_value, powerCounter_value, addCounter_value,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

def widthWork (security : ℕ) : ℕ :=
  2*security + 1 + powerCounterWork (security+2) 2 + 60*((security+2)^2+1)^2 + 3



def table (security cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let width := widthCode security
  let values := binaryWindowWeights width.data cutoff bits
  ⟨values.data, width.work + values.work + 2⟩

theorem table_value (security cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((table security cutoff bits).data.get index).decode =
      windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits index := by
  simp only [table, binaryWindowWeights_value, widthCode_value, WindowGaussianSampler.squaredWidth]

def budget (security bits : ℕ) : ℕ := (security+2)^2 + bits + 2

noncomputable section
open scoped Classical
attribute [local irreducible] widthCode table







def tableWork (security bits : ℕ) : ℕ := widthWork security + binaryWindowWork (budget security bits) + 2







noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  2*X + 1 + 3*(6*(X+3)^4+4) + 60*((X+2)^2+1)^2 + 3 +
    binaryWindowPolynomial ((X+2)^2+precision+2) + 2





end
end CurrentAFT.CurrentGaussianBits

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentGaussianBits.workPolynomial
  pure ()

end

section



















namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
namespace AFT.MixedKernel
end AFT.MixedKernel








/-! # Fixed-order sparse cycle programs

Only latent edges touched by the supplied root positions are enumerated.
Adjacent selected roots read the same stored edge and the predecessor of
the first body position is still the closing edge. The program is a
finite rational sum, with its exact whole-body semantics proved below.
This is not yet the complete local physical-response evaluator.
-/
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def touched {body order : ℕ} (sites : Fin order → Fin body) : Finset (Fin body) :=
  Finset.univ.image sites ∪ Finset.univ.image (fun slot => (finRotate body).symm (sites slot))

def currentEdge {body order : ℕ} (sites : Fin order → Fin body) (slot : Fin order) : touched sites :=
  ⟨sites slot, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩)⟩

def previousEdge {body order : ℕ} (sites : Fin order → Fin body) (slot : Fin order) : touched sites :=
  ⟨(finRotate body).symm (sites slot), Finset.mem_union_right _ (Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩)⟩

def roots {Scalar Group : Type*} [AddGroup Group] {body order : ℕ}
    (sites : Fin order → Fin body) (value : Scalar → Group) (latent : touched sites → Scalar) : Fin order → Group :=
  fun slot => value (latent (currentEdge sites slot)) - value (latent (previousEdge sites slot))

/-- This program uses actual rational multiplication and finite sums on
the active edge alphabet. It never iterates over all body-edge words. -/
def evaluate {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group] {body order : ℕ}
    (sites : Fin order → Fin body) (weight : Scalar → ℚ) (value : Scalar → Group)
    (test : (Fin order → Group) → ℚ) : ℚ :=
  ∑ latent : touched sites → Scalar, (∏ edge, weight (latent edge)) * test (roots sites value latent)







def gaussianEvaluate {body order : ℕ} (security cutoff bits : ℕ) (sites : Fin order → Fin body)
    (test : (Fin order → ℤ) → ℚ) : ℚ :=
  letI : Fintype (Window cutoff) := Fintype.ofEquiv (Fin (2*cutoff+1))
    (FiniteConvolutionProgram.windowIndexEquiv cutoff)
  evaluate sites (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
    (fun point : Window cutoff => point.val) test



/-- Genuine distinct selections are enumerated at fixed order. The
normalizer is computed from their finite count, rather than supplied. -/
def selectionEquiv (body order : ℕ) :
    (Fin order ↪ Fin body) ≃ {sites : Fin order → Fin body // Function.Injective sites} where
  toFun sites := ⟨sites, sites.injective⟩
  invFun sites := ⟨sites.val, sites.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def selectionFintype (body order : ℕ) : Fintype (Fin order ↪ Fin body) := by
  letI : DecidablePred (Function.Injective (α := Fin order) (β := Fin body)) :=
    fun sites => by unfold Function.Injective; infer_instance
  exact Fintype.ofEquiv {sites : Fin order → Fin body // Function.Injective sites} (selectionEquiv body order).symm

def averagedEvaluate (security cutoff bits body order : ℕ)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) : ℚ :=
  letI := selectionFintype body order
  (Fintype.card (Fin order ↪ Fin body) : ℚ)⁻¹ *
    ∑ sites : Fin order ↪ Fin body, gaussianEvaluate security cutoff bits sites (test sites)



noncomputable section
open scoped Classical



















end
end CurrentAFT.CyclePatternProgram

end

section




















/-! # Executable current-parameter prime generation

The scan uses the existing explicit unary loop control and Boolean-list
long division. Its defining value is the current least prime, including
the factor `65536` and the non-strict threshold. The work theorem is in
the repository's explicit counter/list-operation model; it is not a
compilation theorem for a Turing machine or for the complete sampler.
-/
namespace CurrentAFT.PublicParameterProgram
open AFT.BinaryArithmetic AFT.ParameterProgram Polynomial
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.primeThreshold
attribute [local irreducible] addCounter powerCounter multiplyCounter doubleCounter boundedLeast

def primeTest (threshold candidate : ℕ) : CountedDecision :=
  let prime := binaryPrimeTest candidate
  let below := lessCounter candidate threshold
  ⟨prime.value && !below.value, prime.work + below.work + 3⟩

theorem primeTest_value (threshold candidate : ℕ) :
    (primeTest threshold candidate).value = true ↔ threshold ≤ candidate ∧ candidate.Prime := by
  simp only [primeTest, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, binaryPrimeTest_value,
    AFT.ParameterProgram.primeTest_value]
  have hbelow : (lessCounter candidate threshold).value = false ↔ threshold ≤ candidate := by
    constructor
    · intro hfalse
      by_contra hsmall
      have htrue := (lessCounter_value candidate threshold).mpr (Nat.lt_of_not_ge hsmall)
      rw [hfalse] at htrue
      cases htrue
    · intro hlower
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt := (lessCounter_value candidate threshold).mp htrue
      omega
  rw [hbelow, and_comm]

def testWork (threshold candidate : ℕ) : ℕ :=
  binaryPrimeWork candidate + 3 * (candidate + threshold) + 5

theorem primeTest_work (threshold candidate : ℕ) :
    (primeTest threshold candidate).work ≤ testWork threshold candidate := by
  have hp := binaryPrimeTest_work candidate
  have hl := lessCounter_work candidate threshold
  unfold primeTest testWork
  dsimp only
  omega

theorem testWork_mono {threshold candidate larger : ℕ} (h : candidate ≤ larger) :
    testWork threshold candidate ≤ testWork threshold larger := by
  unfold testWork binaryPrimeWork
  gcongr

/- These checked executable packages keep kernel conversion from running
the very large counter loops while it checks the program's correctness.
Their bodies are the actual previously verified counter algorithms. -/
 opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

 opaque checkedProduct (first second : ℕ) :
    {result : UnaryCounterResult // result.count = first*second ∧ result.work = first*(2*second+3)+1} :=
  ⟨multiplyCounter first second, multiplyCounter_value first second, multiplyCounter_work first second⟩

 opaque checkedScan (test : ℕ → CountedDecision) (bound : ℕ) :
    {result : AFT.BetaReference.CountedNatural // result = boundedLeast test bound} :=
  ⟨boundedLeast test bound, rfl⟩





 theorem checkedScan_value (test : ℕ → CountedDecision) (bound : ℕ) :
    (checkedScan test bound).val.value = (boundedLeast test bound).value :=
  congrArg AFT.BetaReference.CountedNatural.value (checkedScan test bound).property

theorem scan_exact (security cutoff bound : ℕ) (hcutoff : cutoff = Parameters.primeThreshold security)
    (hbound : Parameters.modulus security ≤ bound) :
    (boundedLeast (primeTest cutoff) bound).value = Parameters.modulus security := by
  apply boundedLeast_exact (primeTest cutoff) (Parameters.modulus security) bound
  · apply (primeTest_value _ _).mpr
    rw [hcutoff]
    exact Parameters.modulus_spec security
  · intro candidate hsmall
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hc := (primeTest_value _ _).mp htrue
    have hthreshold : Parameters.primeThreshold security ≤ candidate := hcutoff ▸ hc.1
    exact (not_le_of_gt hsmall) (Parameters.modulus_least security candidate hthreshold hc.2)
  · exact hbound

/-- All numeric loop bounds are computed by actual counter programs.
The scan itself is structurally recursive on its computed unary bound. -/
def modulus (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let threshold := (checkedProduct 65536 power.count).val
  let upper := doubleCounter threshold.count
  let found := (checkedScan (primeTest threshold.count) upper.count).val
  ⟨found.value, base.work + power.work + threshold.work + upper.work + found.work + 6⟩

theorem modulus_value (security : ℕ) : (modulus security).count = Parameters.modulus security := by
  have hthreshold : 65536 * (security + 2)^64 = Parameters.primeThreshold security := by
    simp only [Parameters.primeThreshold_eq, Parameters.base]
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let cutoff := (checkedProduct 65536 power.count).val
  let upper := doubleCounter cutoff.count
  have hc : cutoff.count = Parameters.primeThreshold security := by
    exact ((checkedProduct 65536 power.count).property.1).trans
      ((congrArg (fun value => 65536 * value) ((checkedPower base.count 64).property.1)).trans
        ((congrArg (fun value => 65536 * value^64) (addCounter_value security 2)).trans hthreshold))
  have hu : Parameters.modulus security ≤ upper.count := by
    change _ ≤ (doubleCounter cutoff.count).count
    rw [doubleCounter_value, hc]
    exact Parameters.modulus_upper security
  change (checkedScan (primeTest cutoff.count) upper.count).val.value = _
  exact (checkedScan_value _ _).trans (scan_exact security cutoff.count upper.count hc hu)

def workBound (security : ℕ) : ℕ :=
  let base := security + 2
  let threshold := 65536 * base^64
  2 * security + 1 + powerCounterWork base 64 +
    (65536 * (2 * base^64 + 3) + 1) + (3 * threshold + 1) +
      2 * threshold * (testWork threshold (2 * threshold) + 1) + 6

theorem modulus_work (security : ℕ) : (modulus security).work ≤ workBound security := by
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let cutoff := (checkedProduct 65536 power.count).val
  let upper := doubleCounter cutoff.count
  let found := (checkedScan (primeTest cutoff.count) upper.count).val
  have hb : base.count = security + 2 := addCounter_value security 2
  have hp : power.count = (security + 2)^64 := ((checkedPower base.count 64).property.1).trans (congrArg (·^64) hb)
  have hc : cutoff.count = 65536 * (security+2)^64 := ((checkedProduct 65536 power.count).property.1).trans (congrArg (65536 * ·) hp)
  have hu : upper.count = 2 * (65536 * (security+2)^64) := (doubleCounter_value cutoff.count).trans (congrArg (2 * ·) hc)
  have hbase : base.work = 2*security+1 := addCounter_work security 2
  have hpower : power.work ≤ powerCounterWork (security+2) 64 := by
    exact ((checkedPower base.count 64).property.2).trans_eq (congrArg (fun value => powerCounterWork value 64) hb)
  have hcutoff : cutoff.work = 65536 * (2*(security+2)^64+3)+1 := by
    exact ((checkedProduct 65536 power.count).property.2).trans (congrArg (fun value => 65536*(2*value+3)+1) hp)
  have hupper : upper.work = 3*(65536*(security+2)^64)+1 :=
    (doubleCounter_work cutoff.count).trans (congrArg (fun value => 3*value+1) hc)
  have hscan : found.work ≤ upper.count * (testWork cutoff.count upper.count + 1) := by
    dsimp only [found]
    rw [(checkedScan _ _).property]
    exact boundedLeast_work_le _ _ _ (fun candidate hcandidate =>
      (primeTest_work cutoff.count candidate).trans (testWork_mono hcandidate))
  rw [hc, hu] at hscan
  change base.work + power.work + cutoff.work + upper.work + found.work + 6 ≤ _
  unfold workBound
  dsimp only
  omega

noncomputable def workPolynomial : Polynomial ℕ :=
  let base := X + 2
  let threshold := 65536 * base^64
  2 * X + 1 + 65 * (6 * (base + 1)^66 + 4) +
    (65536 * (2 * base^64 + 3) + 1) + (3 * threshold + 1) +
      2 * threshold * (binaryPrimeWorkPolynomial (2 * threshold) +
        3 * (2 * threshold + threshold) + 6) + 6

theorem workPolynomial_eval (security : ℕ) : workPolynomial.eval security = workBound security := by
  simp only [workPolynomial, workBound, testWork, binaryPrimeWorkPolynomial,
    binaryPrimeWork, powerCounterWork, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  norm_num
  omega

/-- A single executable program works at every security parameter. The
polynomial is a proved cost bound, not an input certificate or oracle. -/
theorem modulus_polynomial_work (security : ℕ) :
    (modulus security).work ≤ workPolynomial.eval security := by
  rw [workPolynomial_eval]
  exact modulus_work security

end CurrentAFT.PublicParameterProgram

end

section
























/-! # A current conditional diffuse-pair entry program

The protected scalar is retained as an input throughout. Only the two
independent public blur edges are rationally approximated. This program
uses the actual integer trimmed-slice formula, including its varying
denominator, rather than a circular uniform replacement.
-/
namespace CurrentAFT.LocalDiffuseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def direction (colors primary : ℕ) (coin : Bool) : Bool :=
  if 2 * primary < colors - 1 then false else if colors - 1 < 2 * primary then true else coin

def coinEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) : ℚ :=
  AFT.V7Calibration.averagedPairProgram colors 1
    ((if direction colors primary coin then (width : ℤ) else -2 * (width : ℤ) + 1) + blur)
    source width first second

def blurEntry (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) : ℚ :=
  (coinEntry colors width primary source blur true first second +
    coinEntry colors width primary source blur false first second) / 2

def evaluate (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  ∑ left : Fin (2*cutoff+1), ∑ right : Fin (2*cutoff+1),
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits
      (FiniteConvolutionProgram.windowIndexEquiv cutoff left) *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits
        (FiniteConvolutionProgram.windowIndexEquiv cutoff right) *
        blurEntry colors width primary source first second
          ((FiniteConvolutionProgram.windowIndexEquiv cutoff left).val -
            (FiniteConvolutionProgram.windowIndexEquiv cutoff right).val)

/-- All public parameters used by the evaluator are computed. The later
bit-work accounting for this entry evaluator is a separate obligation. -/
def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits primary source first second

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw















end
end CurrentAFT.LocalDiffuseProgram

end

section

























/-! # The diffuse local leaf evaluated on actual binary data

The Gaussian table is materialized once. Every access scans its stored
list, and the two-dimensional average uses actual binary rational sums.
The protected scalar and the two output colors remain retained inputs.
-/
namespace CurrentAFT.BinaryDiffuseProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def coin (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let baseline := binaryBaselineStart colors width primary (!choice)
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let start := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  let widthCode := canonicalCounter width
  let result := BinaryTrimmedPair.pair start.negative sourceSign colorCode.digits widthCode.digits
    start.digits source first second
  ⟨result.data, baseline.work + leftCode.work + rightCode.work + blur.work + start.work +
    colorCode.work + widthCode.work + result.work + 8⟩

attribute [local irreducible] binaryBaselineStart canonicalCounter signedAdd BinaryTrimmedPair.pair coin

theorem baseline_value (colors width primary : ℕ) (choice : Bool) :
    signedValue (binaryBaselineStart colors width primary (!choice)).negative
      (binaryBaselineStart colors width primary (!choice)).digits =
      if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1 := by
  rw [binaryBaselineStart_value]
  by_cases hl : 2*primary < colors-1
  · simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction, if_pos hl,
      Bool.false_eq_true, if_false]
    ring
  · by_cases hu : colors-1 < 2*primary
    · simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction, if_neg hl, if_pos hu, if_true]
      ring
    · cases choice <;> simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction,
        if_neg hl, if_neg hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] <;> ring



def coinIntegerBound (bound : ℕ) : ℕ := 4*bound+10
def coinWork (bound : ℕ) : ℕ :=
  1000*(3*bound+2)^2 + 4*(50*(bound+1)^2) +
    (20*bound+8) + (20*(2*bound+2)+8) + BinaryTrimmedPair.pairWork (coinIntegerBound bound) + 8



def average (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let positive := coin colors width primary left right true sourceSign source first second
  let negative := coin colors width primary left right false sourceSign source first second
  let total := RationalBits.add positive.data negative.data
  let result := RationalBits.multiply total.data half
  ⟨result.data, positive.work + negative.work + total.work + result.work + 4⟩



def averageHeight (bound : ℕ) : ℕ := 2*(2*coinIntegerBound bound+8)+3
def averageWork (bound : ℕ) : ℕ := 2*coinWork bound +
  primitiveWorkBound (2*coinIntegerBound bound+8) +
  primitiveWorkBound (2*(2*coinIntegerBound bound+8)+2) + 4



def term (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool)
    (left right : Fin (2*cutoff+1)) : RationalResult :=
  let firstWeight := readVector zero weights left
  let secondWeight := readVector zero weights right
  let response := average colors width primary left.val right.val sourceSign source first second
  let probability := RationalBits.multiply firstWeight.value secondWeight.value
  let result := RationalBits.multiply probability.data response.data
  ⟨result.data, firstWeight.work + secondWeight.work + response.work + probability.work + result.work + 5⟩



def termHeight (bound gaussianHeight : ℕ) : ℕ := 2*gaussianHeight + averageHeight bound
def termWork (count bound gaussianHeight : ℕ) : ℕ :=
  2*(3*count+3) + averageWork bound + 2*primitiveWorkBound (termHeight bound gaussianHeight) + 5



def sum (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  sumFin (2*cutoff+1) (fun left => sumFin (2*cutoff+1)
    (fun right => term colors width primary cutoff weights sourceSign source first second left right))

def sumHeight (count bound gaussianHeight : ℕ) : ℕ :=
  count*(count*(termHeight bound gaussianHeight+1)+1)
def sumWork (count bound gaussianHeight : ℕ) : ℕ :=
  count*(count*(termWork count bound gaussianHeight +
    primitiveWorkBound ((count+1)*(termHeight bound gaussianHeight+1))+2)+2 +
    primitiveWorkBound ((count+1)*(count*(termHeight bound gaussianHeight+1)+1))+2)+2



def evaluate (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum colors width primary cutoff weights.data sourceSign source first second
  ⟨result.data, weights.work + result.work + 2⟩



def inputBound (colors width primary cutoff : ℕ) (source first second : List Bool) : ℕ :=
  colors + width + primary + 2*cutoff + source.length + first.length + second.length + 1
def gaussianHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6
def evaluateWork (security cutoff bits bound : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits + sumWork (2*cutoff+1) bound (gaussianHeight security bits) + 2







noncomputable def coinIntegerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 4*bound+10
noncomputable def averageHeightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  2*(2*coinIntegerPolynomial bound+8)+3
noncomputable def coinWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  1000*(3*bound+2)^2 + 4*(50*(bound+1)^2) +
    (20*bound+8) + (20*(2*bound+2)+8) + BinaryTrimmedPair.pairWorkPolynomial (coinIntegerPolynomial bound) + 8
noncomputable def averageWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  2*coinWorkPolynomial bound + primitiveWorkPolynomial (2*coinIntegerPolynomial bound+8) +
    primitiveWorkPolynomial (2*(2*coinIntegerPolynomial bound+8)+2) + 4
noncomputable def termHeightPolynomial (bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  2*gaussianHeight + averageHeightPolynomial bound
noncomputable def termWorkPolynomial (count bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  2*(3*count+3) + averageWorkPolynomial bound +
    2*primitiveWorkPolynomial (termHeightPolynomial bound gaussianHeight) + 5
noncomputable def sumWorkPolynomial (count bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(termWorkPolynomial count bound gaussianHeight +
    primitiveWorkPolynomial ((count+1)*(termHeightPolynomial bound gaussianHeight+1))+2)+2 +
    primitiveWorkPolynomial ((count+1)*(count*(termHeightPolynomial bound gaussianHeight+1)+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision bound : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) bound (500000000*((Polynomial.X+2)^2+precision+2)^6) + 2





end CurrentAFT.BinaryDiffuseProgram

end

section



















/-! # Self-generated current parameters for the binary diffuse leaf

The least prime, anchor width and edge window are calculated by genuine
counter/list programs before evaluating the local Gaussian average.
-/
namespace CurrentAFT.BinaryDiffuseCurrent
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  addCounter powerCounter differenceCounter divideCounter PublicParameterProgram.modulus

 opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

structure Metadata where
  colors : ℕ
  width : ℕ
  cutoff : ℕ
  work : ℕ

def metadata (security : ℕ) : Metadata :=
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := (checkedPower base.count 48).val
  let square := (checkedPower base.count 2).val
  let last := differenceCounter square.count 1
  let half := divideCounter last.count 2
  ⟨colors.count, width.count, half.quotient,
    colors.work + base.work + width.work + square.work + last.work + half.work + 6⟩

theorem metadata_value (security : ℕ) :
    (metadata security).colors = Parameters.modulus security ∧
      (metadata security).width = (security+2)^48 ∧
      (metadata security).cutoff = ((security+2)^2-1)/2 := by
  let base := addCounter security 2
  let width := (checkedPower base.count 48).val
  let square := (checkedPower base.count 2).val
  let last := differenceCounter square.count 1
  have hb : base.count = security+2 := addCounter_value security 2
  have hw : width.count = (security+2)^48 :=
    (checkedPower base.count 48).property.1.trans (congrArg (·^48) hb)
  have hs : square.count = (security+2)^2 :=
    (checkedPower base.count 2).property.1.trans (congrArg (·^2) hb)
  have hl : last.count = (security+2)^2-1 :=
    (differenceCounter_value square.count 1).trans (congrArg (·-1) hs)
  exact ⟨PublicParameterProgram.modulus_value security, hw,
    (divideCounter_value last.count 2 (by omega)).1.trans (congrArg (·/2) hl)⟩

def metadataWork (security : ℕ) : ℕ :=
  PublicParameterProgram.workBound security + 2*security+1 + powerCounterWork (security+2) 48 +
    powerCounterWork (security+2) 2 + (2*(security+2)^2+1) +
    500*((security+2)^2+4)^2 + 6



def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let parameters := metadata security
  let result := BinaryDiffuseProgram.evaluate security parameters.colors parameters.width parameters.cutoff bits primary
    sourceSign source first second
  ⟨result.data, parameters.work + result.work + 2⟩



noncomputable section
open scoped Classical





def parameterBound (security inputBits : ℕ) : ℕ :=
  2*131072*(security+2)^64 + (security+2)^48 + 2*(security+2)^2 + 3*inputBits + 1



def currentHeight (security bits inputBits : ℕ) : ℕ :=
  BinaryDiffuseProgram.sumHeight (2*(security+2)^2+1) (parameterBound security inputBits)
    (BinaryDiffuseProgram.gaussianHeight security bits)



noncomputable def metadataWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + 2*Polynomial.X+1 + 49*(6*(Polynomial.X+3)^50+4) +
    3*(6*(Polynomial.X+3)^4+4) + (2*(Polynomial.X+2)^2+1) +
    500*((Polynomial.X+2)^2+4)^2 + 6



noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*131072*(Polynomial.X+2)^64 + (Polynomial.X+2)^48 + 2*(Polynomial.X+2)^2 + 3*inputBits + 1



noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial + BinaryDiffuseProgram.evaluateWorkPolynomial ((Polynomial.X+2)^2) precision
    (parameterPolynomial inputBits) + 2





end
end CurrentAFT.BinaryDiffuseCurrent

end

section



















/-! # Executed sizes used by the current proposal formula

The prime search and the two fixed powers are executed before their binary
encodings are produced.  None of these rational inputs is stored advice.
-/
namespace CurrentAFT.BinaryProposalMetadata
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter powerCounter ofCounter PublicParameterProgram.modulus

 opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

 opaque checkedProduct (first second : ℕ) :
    {result : UnaryCounterResult // result.count = first*second ∧ result.work = first*(2*second+3)+1} :=
  ⟨multiplyCounter first second, multiplyCounter_value first second, multiplyCounter_work first second⟩

structure Counts where
  colors : ℕ
  legs : ℕ
  population : ℕ
  work : ℕ

def counts (security : ℕ) : Counts :=
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let legs := (checkedPower base.count 128).val
  let factor := (checkedPower base.count 96).val
  let population := (checkedProduct colors.count factor.count).val
  ⟨colors.count, legs.count, population.count,
    colors.work + base.work + legs.work + factor.work + population.work + 5⟩

theorem counts_value (security : ℕ) :
    (counts security).colors = Parameters.modulus security ∧
    (counts security).legs = (security+2)^128 ∧
    (counts security).population = Parameters.modulus security*(security+2)^96 := by
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let factor := (checkedPower base.count 96).val
  have hq : colors.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  have hb : base.count = security+2 := addCounter_value security 2
  have hf : factor.count = (security+2)^96 :=
    (checkedPower base.count 96).property.1.trans (congrArg (·^96) hb)
  exact ⟨hq, (checkedPower base.count 128).property.1.trans (congrArg (·^128) hb),
    (checkedProduct colors.count factor.count).property.1.trans (by rw [hq, hf])⟩

def sizeBound (security : ℕ) : ℕ := 131072*(security+2)^160

theorem counts_bounds (security : ℕ) :
    (counts security).colors ≤ sizeBound security ∧
    (counts security).legs ≤ sizeBound security ∧
    (counts security).population ≤ sizeBound security := by
  rcases counts_value security with ⟨hq, hl, hp⟩
  have hb : 1 ≤ security+2 := by omega
  have hq' : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hc : Parameters.modulus security ≤ sizeBound security := hq'.trans
    (Nat.mul_le_mul_left 131072 (Nat.pow_le_pow_right hb (by decide : 64 ≤ 160)))
  have hlegs : (security+2)^128 ≤ sizeBound security :=
    (Nat.pow_le_pow_right hb (by decide : 128 ≤ 160)).trans (Nat.le_mul_of_pos_left _ (by decide))
  have hpop : Parameters.modulus security*(security+2)^96 ≤ sizeBound security := by
    apply (Nat.mul_le_mul_right ((security+2)^96) hq').trans_eq
    simp only [sizeBound, mul_assoc, ← pow_add]
  exact ⟨hq ▸ hc, hl ▸ hlegs, hp ▸ hpop⟩

def countsWork (security : ℕ) : ℕ := PublicParameterProgram.workBound security + 2*security+1 +
  powerCounterWork (security+2) 128 + powerCounterWork (security+2) 96 +
  (131072*(security+2)^64)*(2*(security+2)^96+3)+1 + 5

theorem counts_work (security : ℕ) : (counts security).work ≤ countsWork security := by
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let legs := (checkedPower base.count 128).val
  let factor := (checkedPower base.count 96).val
  let population := (checkedProduct colors.count factor.count).val
  have hb : base.count = security+2 := addCounter_value security 2
  have hf : factor.count = (security+2)^96 :=
    (checkedPower base.count 96).property.1.trans (congrArg (·^96) hb)
  have hq : colors.count ≤ 131072*(security+2)^64 := by
    rw [PublicParameterProgram.modulus_value]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have wc : colors.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have wb : base.work = 2*security+1 := addCounter_work security 2
  have wl : legs.work ≤ powerCounterWork (security+2) 128 :=
    (checkedPower base.count 128).property.2.trans_eq (congrArg (fun b => powerCounterWork b 128) hb)
  have wf : factor.work ≤ powerCounterWork (security+2) 96 :=
    (checkedPower base.count 96).property.2.trans_eq (congrArg (fun b => powerCounterWork b 96) hb)
  have wp : population.work ≤ (131072*(security+2)^64)*(2*(security+2)^96+3)+1 := by
    rw [(checkedProduct colors.count factor.count).property.2, hf]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 1
  change colors.work+base.work+legs.work+factor.work+population.work+5 ≤ _
  unfold countsWork
  omega

structure Encoded where
  colors : RationalBits
  legs : RationalBits
  population : RationalBits
  work : ℕ

def current (security : ℕ) : Encoded :=
  let sizes := counts security
  let colors := ofCounter sizes.colors
  let legs := ofCounter sizes.legs
  let population := ofCounter sizes.population
  ⟨colors.data, legs.data, population.data, sizes.work+colors.work+legs.work+population.work+4⟩

theorem current_value (security : ℕ) :
    (current security).colors.decode = (Parameters.modulus security:ℚ) ∧
    (current security).legs.decode = ((security+2:ℕ)^128:ℚ) ∧
    (current security).population.decode = (Parameters.modulus security*(security+2)^96:ℕ) := by
  rcases counts_value security with ⟨hq, hl, hp⟩
  simp only [current, ofCounter_value, hq, hl, hp, Nat.cast_pow, and_self]



def currentWork (security : ℕ) : ℕ := countsWork security + 3*(60*(sizeBound security+1)^2)+4



noncomputable def sizePolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^160
noncomputable def countsWorkPolynomial : Polynomial ℕ := PublicParameterProgram.workPolynomial+2*Polynomial.X+1+
  129*(6*(Polynomial.X+3)^130+4)+97*(6*(Polynomial.X+3)^98+4)+
  (131072*(Polynomial.X+2)^64)*(2*(Polynomial.X+2)^96+3)+1+5
noncomputable def currentWorkPolynomial : Polynomial ℕ := countsWorkPolynomial+3*(60*(sizePolynomial+1)^2)+4

theorem sizePolynomial_eval (security : ℕ) : sizePolynomial.eval security = sizeBound security := by
  simp only [sizePolynomial, sizeBound, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem countsWorkPolynomial_eval (security : ℕ) : countsWorkPolynomial.eval security = countsWork security := by
  simp only [countsWorkPolynomial, countsWork, PublicParameterProgram.workPolynomial_eval, powerCounterWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one, Nat.add_assoc]
  norm_num only



end CurrentAFT.BinaryProposalMetadata

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProposalMetadata.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProposalMetadata.sizePolynomial
  pure ()

end

section












namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualCalibrationIteration
end CurrentAFT.ActualCalibrationIteration
namespace CurrentAFT.ActualCalibrationIteration.iterate
end CurrentAFT.ActualCalibrationIteration.iterate
namespace CurrentAFT.ActualCalibrationIteration.iterate.match_1
end CurrentAFT.ActualCalibrationIteration.iterate.match_1
namespace CurrentAFT.ActualCalibrationIteration.step
end CurrentAFT.ActualCalibrationIteration.step


/-! # Polynomial coordinate bounds in the actual calibrated norm

The coordinate condition number is derived from the genuine reference atoms
and population weights. No inverse-atom or coordinate-norm oracle is assumed.
-/
namespace CurrentAFT.ActualCoordinateBounds
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundRates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



















end
end CurrentAFT.ActualCoordinateBounds

end

section















/-! # Explicit point coordinates for the full current calibration

All joint kernel entries are retained. The redundant ambient table is
projected by the exact centered point reconstruction, avoiding a chosen real
basis. Extending the response by the identity on the projection kernel gives
an invertible finite matrix with the same unique calibrated solution.
This identifies the matrix; rational approximation and bit costs are separate.
-/
namespace CurrentAFT.CalibrationPointCoordinates
open AFT ControlCoordinates ControlProduct CanonicalReconstruction
  GradedControlAlgebra ActualControls ProposalPrimary LocalCoefficientFamily
  ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev PointIndex (Primary Body : Type*) (order : ℕ) :=
  (arity : TruncatedArity order) ×
    ((Fin arity.val.1.val → Primary) × (Fin arity.val.2.val → Body))

abbrev PointTable (Primary Body : Type*) (order : ℕ) := PointIndex Primary Body order → ℝ

def encode (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] PointTable Primary Body order where
  toFun family point := (family point.1).val point.2.1 point.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def decode (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) (order : ℕ) :
    PointTable Primary Body order →ₗ[ℝ] KernelFamily primary body order where
  toFun table arity := ∑ colors, ∑ centers,
    ((∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
      table ⟨arity, colors, centers⟩) • pointKernel primary body hp hb colors centers
  map_add' first second := by
    funext arity
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar table := by
    funext arity
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    congr 1
    funext colors
    congr 1
    funext centers
    congr 1
    ring







def extend (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (response : Module.End ℝ (KernelFamily primary body order)) :
    Module.End ℝ (PointTable Primary Body order) :=
  LinearMap.id - (encode primary body order).comp
    ((LinearMap.id - response).comp (decode primary body hp hb order))







def currentMatrix (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Matrix (PointIndex (ActualControls.Palette security) (SafePalette security) order)
      (PointIndex (ActualControls.Palette security) (SafePalette security) order) ℝ :=
  LinearMap.toMatrix' (extend (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) order
    (fullResponse security order horder (room security order horder hsecurity) layout))











end
end CurrentAFT.CalibrationPointCoordinates

end

section













/-! # Error propagation for finite calibration tables

Uniform errors in the complete point table are converted to the actual
graded coefficient norm using the proved reference atom bounds. No coordinate
condition number is supplied as an assumption for the current construction.
-/
namespace CurrentAFT.CalibrationCoordinateError
open AFT ControlCoordinates ControlProduct ControlNorm CanonicalReconstruction
  GradedControlAlgebra GradedControlNorm CalibrationPointCoordinates
  ActualControls ProposalPrimary BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]





















end
end CurrentAFT.CalibrationCoordinateError

end

section




















/-!
# Rational entries of the actual marked pair channel

The two public blur edges are approximated by the current Gaussian window
program.  The fair direction coin and uniform anchor index are averaged
exactly.  The retained protected scalar is an input throughout.
-/

namespace CurrentAFT.LocalMarkedProgram

open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy ActualPublicLegCharge
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def companionValue (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (index : Fin width) : ℤ :=
  (colors : ℤ) - 1 - primary +
    (if LocalDiffuseProgram.direction colors primary coin then
      (width : ℤ) + index.val else -((width : ℤ) + index.val)) + blur - source

def pointEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool)
    (index : Fin width) (first second : ℕ) : ℚ :=
  if primary = first ∧ (companionValue colors width primary source blur coin index).toNat = second then 1 else 0

def coinEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) : ℚ :=
  (width : ℚ)⁻¹ * ∑ index : Fin width, pointEntry colors width primary source blur coin index first second

def blurEntry (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) : ℚ :=
  (coinEntry colors width primary source blur true first second +
    coinEntry colors width primary source blur false first second) / 2

def evaluate (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  ∑ left : Fin (2*cutoff+1), ∑ right : Fin (2*cutoff+1),
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits
      (FiniteConvolutionProgram.windowIndexEquiv cutoff left) *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits
        (FiniteConvolutionProgram.windowIndexEquiv cutoff right) *
        blurEntry colors width primary source first second
          ((FiniteConvolutionProgram.windowIndexEquiv cutoff left).val -
            (FiniteConvolutionProgram.windowIndexEquiv cutoff right).val)

def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits primary source first second

noncomputable section
open scoped Classical
local instance markedIndexNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff





















end
end CurrentAFT.LocalMarkedProgram

end

section




















/-! # The actual current pair entry, including its computed activation

The protected scalar remains one retained argument. Both branches use
the same current public Gaussian approximation; activation is computed
from the current scalar window's zero atom. The error is simultaneous
in the public primary and both physical endpoint colors.
-/
namespace CurrentAFT.LocalPairProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def activationApprox (security bits : ℕ) : ℚ :=
  (1 / 2 : ℚ) * windowApproxWeight (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits (windowZero (Parameters.sourceCutoff security - 1))

def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  let rate := activationApprox security bits
  (1-rate) * LocalDiffuseProgram.current security bits primary source first second +
    rate * LocalMarkedProgram.current security bits primary source first second

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

theorem activationApprox_bounds (security bits : ℕ) :
    0 ≤ (activationApprox security bits : ℝ) ∧ (activationApprox security bits : ℝ) ≤ 1/2 := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hp := law.nonneg (windowZero (Parameters.sourceCutoff security - 1))
  have hu := law.atom_le_one (windowZero (Parameters.sourceCutoff security - 1))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  change 0 ≤ (1/2:ℝ) * law.weight (windowZero _) ∧ (1/2:ℝ) * law.weight (windowZero _) ≤ 1/2
  constructor <;> linarith





end
end CurrentAFT.LocalPairProgram

end

section













/-! # Literal rational truncated products of joint coefficient tables

All ordered slot permutations and their factorial normalizers are retained.
The finite arity convolution agrees with the actual canonical family product.
The input arrays need not themselves be centered or symmetric.
-/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

abbrev Kernel (Scalar Primary Body : Type*) (r s : ℕ) := (Fin r → Primary) → (Fin s → Body) → Scalar
abbrev Table (Scalar Primary Body : Type*) (order : ℕ) :=
  (arity : TruncatedArity order) → Kernel Scalar Primary Body arity.val.1.val arity.val.2.val

def average {Scalar : Type*} [Field Scalar] (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → Scalar) : Scalar :=
  (r.factorial : Scalar)⁻¹ * (s.factorial : Scalar)⁻¹ * ∑ first, ∑ second, value first second

def tensor {Scalar Primary Body : Type*} [Mul Scalar] {r s r' s' : ℕ}
    (first : Kernel Scalar Primary Body r s) (second : Kernel Scalar Primary Body r' s') :
    Kernel Scalar Primary Body (r+r') (s+s') :=
  fun colors centers =>
    first (fun index => colors (finSumFinEquiv (Sum.inl index)))
      (fun index => centers (finSumFinEquiv (Sum.inl index))) *
    second (fun index => colors (finSumFinEquiv (Sum.inr index)))
      (fun index => centers (finSumFinEquiv (Sum.inr index)))

def homogeneous {Scalar Primary Body : Type*} [Field Scalar] {r s r' s' : ℕ}
    (first : Kernel Scalar Primary Body r s) (second : Kernel Scalar Primary Body r' s') :
    Kernel Scalar Primary Body (r+r') (s+s') :=
  fun colors centers => average (r+r') (s+s')
    (fun primaryOrder bodyOrder => tensor first second (colors ∘ primaryOrder) (centers ∘ bodyOrder))

def product {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (first second : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun output colors centers => ∑ left : TruncatedArity order, ∑ right : TruncatedArity order,
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      homogeneous (first left) (second right) (colors ∘ finCongr hmatch.1) (centers ∘ finCongr hmatch.2)
    else 0

def realTable {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) :
    Table ℝ Primary Body order := fun arity colors centers => table arity colors centers

noncomputable section
open scoped Classical
local instance productFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _























end
end CurrentAFT.RationalFamilyProductProgram

end

section















/-! # Literal degree-one data of a mixed primary/body certificate -/
namespace CurrentAFT.RationalBackgroundTable
open AFT ControlCoordinates ControlProduct GradedControlAlgebra BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def firstTable {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (primary : Primary → Scalar) (body : Body → Scalar) : RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors centers =>
    if h : arity.val.1.val = 1 ∧ arity.val.2.val = 0 then primary (colors ⟨0, by omega⟩)
    else if h : arity.val.1.val = 0 ∧ arity.val.2.val = 1 then body (centers ⟨0, by omega⟩) else 0

noncomputable section
open scoped Classical
local instance tableFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _











end
end CurrentAFT.RationalBackgroundTable

end

section




















/-! # The actual activation computed from a stored scalar Gaussian table -/
namespace CurrentAFT.BinaryActivationProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter powerCounter differenceCounter
  Parameters.base Parameters.sourceCutoff

def cutoff (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let last := differenceCounter square.count 1
  ⟨last.count, base.work + square.work + last.work + 3⟩

theorem cutoff_value (security : ℕ) : (cutoff security).count = (security+2)^2-1 := by
  simp only [cutoff, differenceCounter_value, powerCounter_value, addCounter_value]

def cutoffWork (security : ℕ) : ℕ := 2*security+1 + powerCounterWork (security+2) 2 + (2*(security+2)^2+1) + 3

theorem cutoff_work (security : ℕ) : (cutoff security).work ≤ cutoffWork security := by
  have hp := powerCounter_work (security+2) 2
  have hd := differenceCounter_work ((security+2)^2) 1
  simp only [cutoff, addCounter_value, powerCounter_value, addCounter_work, cutoffWork]
  omega

def current (security bits : ℕ) : RationalResult :=
  let window := cutoff security
  let table := CurrentGaussianBits.table security window.count bits
  let zeroAtom := readVector zero table.data ⟨window.count, by omega⟩
  let result := RationalBits.multiply half zeroAtom.value
  ⟨result.data, window.work + table.work + zeroAtom.work + result.work + 4⟩

theorem zero_index (window : ℕ) : windowIndexEquiv window ⟨window, by omega⟩ = windowZero window := by
  apply Subtype.ext
  simp only [windowIndexEquiv, Equiv.coe_fn_mk, windowZero]
  omega

theorem current_value (security bits : ℕ) :
    (current security bits).data.decode = LocalPairProgram.activationApprox security bits := by
  simp only [current, RationalBits.multiply_value, half_value, readVector_value,
    CurrentGaussianBits.table_value, windowGaussianWeights, zero_index]
  have hc : (cutoff security).count = Parameters.sourceCutoff security-1 := by
    simp only [cutoff_value, Parameters.sourceCutoff, Parameters.base]
  rw [hc]
  rfl

def currentHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6+2
def currentWork (security bits : ℕ) : ℕ := cutoffWork security + CurrentGaussianBits.tableWork security bits +
  (3*(2*(security+2)^2+1)+3) + primitiveWorkBound (currentHeight security bits) + 4



noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  500000000*((Polynomial.X+2)^2+precision+2)^6+2
noncomputable def cutoffWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1 + 3*(6*(Polynomial.X+3)^4+4) + (2*(Polynomial.X+2)^2+1) + 3
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  cutoffWorkPolynomial + CurrentGaussianBits.workPolynomial precision +
    (3*(2*(Polynomial.X+2)^2+1)+3) + primitiveWorkPolynomial (currentHeightPolynomial precision) + 4

theorem cutoffWorkPolynomial_eval (security : ℕ) : cutoffWorkPolynomial.eval security = cutoffWork security := by
  simp only [cutoffWorkPolynomial, cutoffWork, powerCounterWork, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  norm_num
  omega







end CurrentAFT.BinaryActivationProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryActivationProgram.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryActivationProgram.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryActivationProgram.cutoffWorkPolynomial
  pure ()

end

section


















/-! # Materialized binary averaging against two current Gaussian edges -/
namespace CurrentAFT.BinaryGaussianAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def term {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult)
    (left right : Fin count) : RationalResult :=
  let first := readVector zero weights left
  let second := readVector zero weights right
  let response := kernel left right
  let probability := RationalBits.multiply first.value second.value
  let result := RationalBits.multiply probability.data response.data
  ⟨result.data, first.work + second.work + response.work + probability.work + result.work + 5⟩

theorem term_value {count : ℕ} (weights : Vector RationalBits count)
    (kernel : Fin count → Fin count → RationalResult) (left right : Fin count) :
    (term weights kernel left right).data.decode =
      (weights.get left).decode*(weights.get right).decode*(kernel left right).data.decode := by
  simp only [term, RationalBits.multiply_value, readVector_value]

def termHeight (gaussianHeight kernelHeight : ℕ) : ℕ := 2*gaussianHeight+kernelHeight
def termWork (count gaussianHeight kernelHeight kernelWork : ℕ) : ℕ :=
  2*(3*count+3) + kernelWork + 2*primitiveWorkBound (termHeight gaussianHeight kernelHeight)+5



def sum {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult) : RationalResult :=
  sumFin count (fun left => sumFin count (fun right => term weights kernel left right))

theorem sum_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult) :
    (sum weights kernel).data.decode =
      ∑ left, ∑ right, (weights.get left).decode*(weights.get right).decode*(kernel left right).data.decode := by
  simp only [sum, sumFin_value, term_value]

def sumHeight (count gaussianHeight kernelHeight : ℕ) : ℕ := count*(count*(termHeight gaussianHeight kernelHeight+1)+1)
def sumWork (count gaussianHeight kernelHeight kernelWork : ℕ) : ℕ :=
  count*(count*(termWork count gaussianHeight kernelHeight kernelWork +
    primitiveWorkBound ((count+1)*(termHeight gaussianHeight kernelHeight+1))+2)+2 +
    primitiveWorkBound ((count+1)*(count*(termHeight gaussianHeight kernelHeight+1)+1))+2)+2



def evaluate (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → Fin (2*cutoff+1) → RationalResult) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum weights.data kernel
  ⟨result.data, weights.work + result.work + 2⟩

theorem evaluate_value (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → Fin (2*cutoff+1) → RationalResult) :
    (evaluate security cutoff bits kernel).data.decode =
      ∑ left, ∑ right, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits left *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        (kernel left right).data.decode := by
  simp only [evaluate, sum_value, CurrentGaussianBits.table_value]

def gaussianHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6
def evaluateWork (security cutoff bits kernelHeight kernelWork : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits + sumWork (2*cutoff+1) (gaussianHeight security bits) kernelHeight kernelWork + 2





noncomputable def termHeightPolynomial (gh kh : Polynomial ℕ) : Polynomial ℕ := 2*gh+kh
noncomputable def termWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  2*(3*count+3)+kw+2*primitiveWorkPolynomial (termHeightPolynomial gh kh)+5
noncomputable def sumWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(termWorkPolynomial count gh kh kw +
    primitiveWorkPolynomial ((count+1)*(termHeightPolynomial gh kh+1))+2)+2 +
    primitiveWorkPolynomial ((count+1)*(count*(termHeightPolynomial gh kh+1)+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) (500000000*((Polynomial.X+2)^2+precision+2)^6) kh kw + 2



end CurrentAFT.BinaryGaussianAverage

end

section























/-! # The actual marked anchor on Boolean-list operands

The negative anchor is traversed in reverse order. This preserves its
uniform index law and allows both directions to use the same increasing
integer interval, including the genuine `toNat` output convention.
-/
namespace CurrentAFT.BinaryMarkedKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] binaryBaselineStart canonicalCounter signedAdd

def companion (colors width primary left right index : ℕ) (choice sourceSign : Bool)
    (source : List Bool) : SignedResult :=
  let baseline := binaryBaselineStart colors width primary (!choice)
  let colorCode := canonicalCounter colors
  let primaryCode := canonicalCounter primary
  let indexCode := canonicalCounter index
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let last := signedAdd false true colorCode.digits [true]
  let anchor := signedAdd last.negative true last.digits primaryCode.digits
  let start := signedAdd anchor.negative baseline.negative anchor.digits baseline.digits
  let point := signedAdd start.negative false start.digits indexCode.digits
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let shifted := signedAdd point.negative blur.negative point.digits blur.digits
  let result := signedAdd shifted.negative (!sourceSign) shifted.digits source
  ⟨result.negative, result.digits, baseline.work + colorCode.work + primaryCode.work + indexCode.work +
    leftCode.work + rightCode.work + last.work + anchor.work + start.work + point.work +
    blur.work + shifted.work + result.work + 13⟩

theorem companion_value (colors width primary left right index : ℕ) (choice sourceSign : Bool)
    (source : List Bool) :
    signedValue (companion colors width primary left right index choice sourceSign source).negative
      (companion colors width primary left right index choice sourceSign source).digits =
      (colors : ℤ)-1-primary +
        (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
        index + ((left : ℤ)-right) - signedValue sourceSign source := by
  unfold companion
  rw [signedAdd_value, BinaryTrimmedPair.signed_negate, signedAdd_value, signedAdd_value,
    signedAdd_value, signedAdd_value, BinaryDiffuseProgram.baseline_value, signedAdd_value, signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, canonicalCounter_value]
  norm_num [value]
  ring

def companionWork (bound : ℕ) : ℕ := 1000*(3*bound+2)^2 + 5*(50*(bound+1)^2) + 300*(bound+10)



def point (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) : RationalResult :=
  let color := canonicalCounter primary
  let output := companion colors width primary left right index.val choice sourceSign source
  let primaryMatch := signedEqual false false color.digits first
  let companionMatch := signedEqual false false (nonnegativeDigits output.negative output.digits) second
  ⟨if primaryMatch.value && companionMatch.value then one else zero,
    color.work + output.work + primaryMatch.work + companionMatch.work + 6⟩

theorem point_value (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) :
    (point colors width primary left right choice sourceSign source first second index).data.decode =
      if primary = value first ∧
        ((colors : ℤ)-1-primary +
          (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
          index.val + ((left : ℤ)-right) - signedValue sourceSign source).toNat = value second
      then 1 else 0 := by
  have h1 : (signedEqual false false (canonicalCounter primary).digits first).value = true ↔ primary = value first := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value, Int.natCast_inj]
  have h2 : (signedEqual false false
      (nonnegativeDigits (companion colors width primary left right index.val choice sourceSign source).negative
        (companion colors width primary left right index.val choice sourceSign source).digits) second).value = true ↔
      ((colors : ℤ)-1-primary +
        (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
        index.val + ((left : ℤ)-right) - signedValue sourceSign source).toNat = value second := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false, Int.natCast_inj]
    rw [nonnegativeDigits_value, companion_value]
    rfl
  simp only [point, Bool.and_eq_true, h1, h2]
  split_ifs <;> simp only [one_value, zero_value]

def pointWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + companionWork bound + (48*bound+39) + (48*(2*bound+7)+39) + 6



def coin (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let total := sumFin width (point colors width primary left right choice sourceSign source first second)
  let denominator := ofCounter width
  let result := quotient total.data denominator.data
  ⟨result.data, total.work + denominator.work + result.work + 3⟩

theorem point_reindex (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) :
    (point colors width primary left right choice sourceSign source first second index).data.decode =
      LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source) ((left : ℤ)-right) choice
        (if LocalDiffuseProgram.direction colors primary choice then index else index.rev) (value first) (value second) := by
  rw [point_value]
  unfold LocalMarkedProgram.pointEntry LocalMarkedProgram.companionValue
  have hv : (colors : ℤ)-1-primary +
      (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
      index.val + ((left : ℤ)-right) - signedValue sourceSign source =
    (colors : ℤ)-1-primary +
      (if LocalDiffuseProgram.direction colors primary choice then
        (width : ℤ)+(if LocalDiffuseProgram.direction colors primary choice then index else index.rev).val
        else -((width : ℤ)+(if LocalDiffuseProgram.direction colors primary choice then index else index.rev).val)) +
      ((left : ℤ)-right) - signedValue sourceSign source := by
    by_cases hd : LocalDiffuseProgram.direction colors primary choice = true
    · simp only [hd, if_true]
      ring
    · simp only [hd, Bool.false_eq_true, if_false, Fin.val_rev]
      have hi := index.isLt
      omega
  rw [hv]

theorem coin_value (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) :
    (coin colors width primary left right choice sourceSign source first second).data.decode =
      LocalMarkedProgram.coinEntry colors width primary (signedValue sourceSign source) ((left : ℤ)-right) choice
        (value first) (value second) := by
  have hsum : (∑ index : Fin width,
      (point colors width primary left right choice sourceSign source first second index).data.decode) =
      ∑ index : Fin width, LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source)
        ((left : ℤ)-right) choice index (value first) (value second) := by
    simp only [point_reindex]
    by_cases hd : LocalDiffuseProgram.direction colors primary choice = true
    · simp only [hd, if_true]
    · simp only [hd, Bool.false_eq_true, if_false]
      exact Equiv.sum_comp (Fin.revPerm (n := width)) (fun index =>
        LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source)
          ((left : ℤ)-right) choice index (value first) (value second))
  simp only [coin, quotient_value, sumFin_value, ofCounter_value, LocalMarkedProgram.coinEntry]
  rw [hsum]
  ring

def coinWork (width bound : ℕ) : ℕ :=
  width*(pointWork bound + primitiveWorkBound (width+1)+2)+2 +
    60*(width+1)^2 + (2*primitiveWorkBound width+2) + 3



def average (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let positive := coin colors width primary left right true sourceSign source first second
  let negative := coin colors width primary left right false sourceSign source first second
  let total := RationalBits.add positive.data negative.data
  let result := RationalBits.multiply total.data half
  ⟨result.data, positive.work + negative.work + total.work + result.work + 4⟩

theorem average_value (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) :
    (average colors width primary left right sourceSign source first second).data.decode =
      LocalMarkedProgram.blurEntry colors width primary (signedValue sourceSign source)
        (value first) (value second) ((left : ℤ)-right) := by
  simp only [average, RationalBits.multiply_value, RationalBits.add_value, coin_value, half_value,
    LocalMarkedProgram.blurEntry]
  ring

def averageHeight (width : ℕ) : ℕ := 4*width+3
def averageWork (width bound : ℕ) : ℕ := 2*coinWork width bound +
  primitiveWorkBound (2*width) + primitiveWorkBound (4*width+2) + 4



end CurrentAFT.BinaryMarkedKernel

end

section























/-! # Self-generated current binary marked-pair entries -/
namespace CurrentAFT.BinaryMarkedCurrent
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata

def evaluate (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  BinaryGaussianAverage.evaluate security cutoff bits (fun left right =>
    BinaryMarkedKernel.average colors width primary left.val right.val sourceSign source first second)





def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let result := evaluate security parameters.colors parameters.width parameters.cutoff bits primary sourceSign source first second
  ⟨result.data, parameters.work + result.work + 2⟩



noncomputable section
open scoped Classical



def currentHeight (security bits : ℕ) : ℕ :=
  BinaryGaussianAverage.sumHeight (2*(security+2)^2+1) (BinaryGaussianAverage.gaussianHeight security bits)
    (BinaryMarkedKernel.averageHeight ((security+2)^48))





noncomputable def averageHeightPolynomial (width : Polynomial ℕ) : Polynomial ℕ := 4*width+3
noncomputable def companionWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  1000*(3*bound+2)^2 + 5*(50*(bound+1)^2) + 300*(bound+10)
noncomputable def pointWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2 + companionWorkPolynomial bound + (48*bound+39) + (48*(2*bound+7)+39) + 6
noncomputable def coinWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  width*(pointWorkPolynomial bound+primitiveWorkPolynomial (width+1)+2)+2 +
    60*(width+1)^2+(2*primitiveWorkPolynomial width+2)+3
noncomputable def averageWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  2*coinWorkPolynomial width bound+primitiveWorkPolynomial (2*width)+primitiveWorkPolynomial (4*width+2)+4



noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryGaussianAverage.evaluateWorkPolynomial ((Polynomial.X+2)^2)
    precision (averageHeightPolynomial ((Polynomial.X+2)^48))
    (averageWorkPolynomial ((Polynomial.X+2)^48) (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 2



end
end CurrentAFT.BinaryMarkedCurrent

end

section





















/-! # The complete actual pair entry on binary rational data

This executes activation, both physical branches and all rational mixing
operations. Its semantic error is the already proved simultaneous error
for the true current pair law; its work is derived from actual operands.
-/
namespace CurrentAFT.BinaryPairProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let rate := BinaryActivationProgram.current security bits
  let diffuse := BinaryDiffuseCurrent.current security bits primary sourceSign source first second
  let marked := BinaryMarkedCurrent.current security bits primary sourceSign source first second
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let diffuseTerm := RationalBits.multiply remaining.data diffuse.data
  let markedTerm := RationalBits.multiply rate.data marked.data
  let result := RationalBits.add diffuseTerm.data markedTerm.data
  ⟨result.data, rate.work + diffuse.work + marked.work + negativeRate.work + remaining.work +
    diffuseTerm.work + markedTerm.work + result.work + 8⟩



noncomputable section
open scoped Classical



noncomputable def diffuseHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  count*(count*(BinaryDiffuseProgram.termHeightPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits)
    (500000000*((Polynomial.X+2)^2+precision+2)^6)+1)+1)
noncomputable def markedHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  count*(count*(2*(500000000*((Polynomial.X+2)^2+precision+2)^6)+4*(Polynomial.X+2)^48+3+1)+1)
noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryActivationProgram.currentHeightPolynomial precision + diffuseHeightPolynomial precision inputBits +
    markedHeightPolynomial precision + 10





noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision + BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits +
    BinaryMarkedCurrent.currentWorkPolynomial precision inputBits +
    5*primitiveWorkPolynomial (currentHeightPolynomial precision inputBits) + 8



end
end CurrentAFT.BinaryPairProgram

end

section

























/-! # Rational tables for the actual current proposal

Gaussian entries are read from the checked Boolean/list table. The inward
anchor uses the real midpoint coin, uniform index and integer point; its
smoothed table is a finite rational sum. No real inverse is queried.
-/
namespace CurrentAFT.RationalProposalProgram

open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def gaussianWeight (security cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  ((CurrentGaussianBits.table security cutoff bits).data.get
    ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).symm point)).decode

theorem gaussianWeight_eq (security cutoff bits : ℕ) (point : Window cutoff) :
    gaussianWeight security cutoff bits point =
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits point := by
  rw [gaussianWeight, CurrentGaussianBits.table_value]
  change windowApproxWeight _ _ _
    ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff)
      ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).symm point)) = _
  rw [Equiv.apply_symm_apply]

def anchorKernel (colors width primary : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  LocalMarkedProgram.blurEntry colors width primary (-shift) primary output 0

def anchorEvaluate (security colors width cutoff bits primary output : ℕ) : ℚ :=
  ∑ index : Fin (2*cutoff+1),
    let scalar := AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff index
    gaussianWeight security cutoff bits scalar * anchorKernel colors width primary scalar.val output

def anchor (security bits primary output : ℕ) : ℚ :=
  anchorEvaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    ((security + 2)^2 - 1) bits primary output

def seedWeight (security bits : ℕ) (seed : ActualSeed security) : ℚ :=
  gaussianWeight security (edgeCutoff security) bits seed.1.1 *
    gaussianWeight security (edgeCutoff security) bits seed.1.2 *
      gaussianWeight security (Parameters.sourceCutoff security - 1) bits seed.2

/-- Computable product indices for the actual three independent protected scalars. -/
 def seedIndexEquiv (security : ℕ) :
    ((Fin (2*edgeCutoff security+1) × Fin (2*edgeCutoff security+1)) ×
      Fin (2*(Parameters.sourceCutoff security-1)+1)) ≃ ActualSeed security :=
  ((AFT.FiniteConvolutionProgram.windowIndexEquiv (edgeCutoff security)).prodCongr
    (AFT.FiniteConvolutionProgram.windowIndexEquiv (edgeCutoff security))).prodCongr
      (AFT.FiniteConvolutionProgram.windowIndexEquiv (Parameters.sourceCutoff security-1))

def seedEvaluate (security bits : ℕ) (kernel : ActualSeed security → ℚ) : ℚ :=
  ∑ index : (Fin (2*edgeCutoff security+1) × Fin (2*edgeCutoff security+1)) ×
      Fin (2*(Parameters.sourceCutoff security-1)+1),
    let seed := seedIndexEquiv security index
    seedWeight security bits seed * kernel seed

def safeEntry (colors margin output : ℕ) : ℚ :=
  AFT.V7Calibration.sliceProbabilityProgram colors margin 0 output

def bodyKernel (colors margin : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  ∑ baseline : Fin colors,
    if ((baseline.val : ℤ) + shift) % colors = (output : ℤ) then safeEntry colors margin baseline.val else 0

def body (security bits : ℕ) (includeScalar : Bool) (output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed =>
    bodyKernel (PublicParameterProgram.modulus security).count (3 * (security + 2)^2)
      (seed.1.1.val - seed.1.2.val + if includeScalar then seed.2.val else 0) output)

def diffuseKernel (colors width : ℕ) (blur second : ℤ) (output : ℕ) : ℚ :=
  (AFT.V7Calibration.averagedSliceProgram colors 1 ((width : ℤ) + blur) second width output +
    AFT.V7Calibration.averagedSliceProgram colors 1 (-2 * (width : ℤ) + 1 + blur) second width output) / 2

def diffuse (security bits output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed => diffuseKernel (PublicParameterProgram.modulus security).count
    ((security + 2)^48) (seed.1.1.val - seed.1.2.val) seed.2.val output)

/-- The same explicit balancing numerator as the current primary profile,
with every Gaussian entry and the activation rationally computed. -/
def primaryRaw (security bits output : ℕ) : ℚ :=
  let colors := (PublicParameterProgram.modulus security).count
  let legs : ℕ := (security + 2)^128
  let bodyCount : ℕ := colors * (security + 2)^96
  let free : ℚ := (bodyCount : ℚ) - legs - colors
  let rate := LocalPairProgram.activationApprox security bits
  let marked : ℚ := (legs : ℚ) * rate
  (((bodyCount + 2 * legs : ℕ) : ℚ) / colors - (free + marked) * body security bits false output -
    ((legs + colors : ℕ) : ℚ) * body security bits true output -
      2 * (legs : ℚ) * (1 - rate) * diffuse security bits output) / marked

def primaryGood (security bits : ℕ) : Prop :=
  ∀ output : Fin (PublicParameterProgram.modulus security).count,
    (1 : ℚ) / (4 * (PublicParameterProgram.modulus security).count) ≤ primaryRaw security bits output.val

instance primaryGoodDecidable (security bits : ℕ) : Decidable (primaryGood security bits) := by
  unfold primaryGood
  infer_instance

/-- An exact rational positivity check has a uniform positive fallback.
At certified precision the check succeeds and this is `primaryRaw`. -/
def primary (security bits output : ℕ) : ℚ :=
  if primaryGood security bits then primaryRaw security bits output
  else 1 / ((PublicParameterProgram.modulus security).count : ℚ)

def anchorPrimary (security bits output : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    primary security bits color.val * anchor security bits color.val output

def compensationApprox (security bits : ℕ) : ℚ :=
  let colors := (PublicParameterProgram.modulus security).count
  let legs : ℕ := (security + 2)^128
  let bodyCount : ℕ := colors * (security + 2)^96
  (legs : ℚ) * LocalPairProgram.activationApprox security bits / ((bodyCount : ℚ) - legs - colors)

def center (security bits output : ℕ) : ℚ :=
  (1 + compensationApprox security bits) *
    safeEntry (PublicParameterProgram.modulus security).count (3 * (security + 2)^2) output -
      compensationApprox security bits * anchorPrimary security bits output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff

/-- Explicit indices compute the original finite anchor expectation exactly. -/
theorem anchorEvaluate_eq_window_sum (security colors width cutoff bits primary output : ℕ) :
    anchorEvaluate security colors width cutoff bits primary output =
      ∑ scalar : Window cutoff,gaussianWeight security cutoff bits scalar*
        anchorKernel colors width primary scalar.val output := by
  unfold anchorEvaluate
  exact (AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp
    (fun scalar => gaussianWeight security cutoff bits scalar*anchorKernel colors width primary scalar.val output)

/-- Explicit product indices compute the original full shared-seed expectation exactly. -/
theorem seedEvaluate_eq_window_sum (security bits : ℕ) (kernel : ActualSeed security → ℚ) :
    seedEvaluate security bits kernel = ∑ seed,seedWeight security bits seed*kernel seed := by
  unfold seedEvaluate
  exact (seedIndexEquiv security).sum_comp (fun seed => seedWeight security bits seed*kernel seed)



theorem anchor_point_cast (security : ℕ) (primary output : FirstHistogram.Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (coin : Bool) (index : InwardAnchor.Index security) :
    (LocalMarkedProgram.pointEntry (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val (-shift) 0 coin index primary.val output.val : ℝ) =
      if InwardAnchor.point security primary coin index shift hshift = output then 1 else 0 := by
  have hvalue : LocalMarkedProgram.companionValue (Parameters.modulus security)
      (Parameters.anchorWidth security) primary.val (-shift) 0 coin index =
        InwardAnchor.integerPoint security primary coin index shift := by
    unfold LocalMarkedProgram.companionValue InwardAnchor.integerPoint InwardAnchor.offset
    change (Parameters.modulus security : ℤ) - 1 - primary.val +
      (if InwardAnchor.positiveDirection security primary coin then
        (Parameters.anchorWidth security : ℤ) + index.val else -((Parameters.anchorWidth security : ℤ) + index.val)) +
      0 - -shift = _
    ring
  simp only [LocalMarkedProgram.pointEntry, hvalue, true_and, Fin.ext_iff, InwardAnchor.point]
  split_ifs <;> norm_num

theorem anchorKernel_cast (security : ℕ) (primary output : FirstHistogram.Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    (anchorKernel (Parameters.modulus security) (Parameters.anchorWidth security) primary.val shift output.val : ℝ) =
      (InwardAnchor.shiftedAnchorLaw security primary shift hshift).weight output := by
  simp only [anchorKernel, LocalMarkedProgram.blurEntry, LocalMarkedProgram.coinEntry,
    Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_sum, InwardAnchor.shiftedAnchorLaw, InwardAnchor.fixedCoinLaw,
    FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.uniform_weight,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool, Finset.mul_sum]
  simp_rw [anchor_point_cast security primary output shift hshift]
  simp only [mul_ite, mul_one, mul_zero]
  rw [div_eq_mul_inv, add_mul]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  simp only [mul_comm]

def approximateAnchorLaw (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    FiniteDist (FirstHistogram.Palette security) :=
  (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits).mix
      (fun scalar => InwardAnchor.shiftedAnchorLaw security primary scalar.val (InwardAnchor.scalar_bound security scalar))

theorem anchorEvaluate_cast (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (anchorEvaluate security (Parameters.modulus security) (Parameters.anchorWidth security)
      (Parameters.sourceCutoff security - 1) bits primary.val output.val : ℝ) =
        (approximateAnchorLaw security bits primary).weight output := by
  simp only [anchorEvaluate_eq_window_sum, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq, approximateAnchorLaw,
    FiniteDist.mix_weight, windowApproxLaw]
  apply Finset.sum_congr rfl
  intro scalar _
  rw [anchorKernel_cast security primary output scalar.val (InwardAnchor.scalar_bound security scalar)]

theorem anchor_cast (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (anchor security bits primary.val output.val : ℝ) = (approximateAnchorLaw security bits primary).weight output := by
  unfold anchor
  rw [PublicParameterProgram.modulus_value]
  have hA : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  have hB : (security + 2)^2 = Parameters.sourceCutoff security := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [hA, hB]
  exact anchorEvaluate_cast security bits primary output







theorem anchor_zero_outside (security bits : ℕ) (primary output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) :
    anchor security bits primary.val output.val = 0 := by
  have h : (anchor security bits primary.val output.val : ℝ) = 0 := by
    rw [anchor_cast]
    simp only [approximateAnchorLaw, FiniteDist.mix_weight,
      InwardAnchor.shiftedAnchorLaw_zero_outside security primary _ _ output hunsafe,
      mul_zero, Finset.sum_const_zero]
  exact_mod_cast h

def approximateSeedLaw (security bits : ℕ) : FiniteDist (ActualSeed security) :=
  ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)).prod
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)

theorem seedWeight_cast (security bits : ℕ) (seed : ActualSeed security) :
    (seedWeight security bits seed : ℝ) = (approximateSeedLaw security bits).weight seed := by
  simp only [seedWeight, Rat.cast_mul, gaussianWeight_eq, approximateSeedLaw,
    FiniteDist.prod_weight, windowApproxLaw]

theorem seedEvaluate_cast (security bits : ℕ) (kernel : ActualSeed security → ℚ) :
    (seedEvaluate security bits kernel : ℝ) =
      (approximateSeedLaw security bits).expectation (fun seed => (kernel seed : ℝ)) := by
  simp only [seedEvaluate_eq_window_sum, Rat.cast_sum, Rat.cast_mul, seedWeight_cast, FiniteDist.expectation]



theorem shift_condition (security : ℕ) (shift : ℤ) (baseline output : FirstHistogram.Palette security) :
    shiftEquiv security shift baseline = output ↔
      ((baseline.val : ℤ) + shift) % Parameters.modulus security = (output.val : ℤ) := by
  rw [← (ZMod.finEquiv (Parameters.modulus security)).injective.eq_iff]
  change RefinedPublicOutput.embed security (shiftEquiv security shift baseline) =
    RefinedPublicOutput.embed security output ↔ _
  rw [RefinedPublicOutput.embed_shift, RefinedPublicOutput.embed_value, RefinedPublicOutput.embed_value]
  have hcast : (baseline.val : ZMod (Parameters.modulus security)) + (shift : ZMod (Parameters.modulus security)) =
      (((baseline.val : ℤ) + shift : ℤ) : ZMod (Parameters.modulus security)) := by push_cast; rfl
  rw [hcast]
  have hout : (output.val : ZMod (Parameters.modulus security)) =
      ((output.val : ℤ) : ZMod (Parameters.modulus security)) := by simp only [Int.cast_natCast]
  rw [hout]
  rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast output.isLt)]

theorem bodyKernel_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (bodyKernel (Parameters.modulus security) (Parameters.safeMargin security) shift output.val : ℝ) =
      ((safeLaw security).map (shiftEquiv security shift)).weight output := by
  simp only [bodyKernel, Rat.cast_sum, FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro baseline _
  rw [shift_condition]
  split_ifs
  · rw [safeEntry, AFT.V7Calibration.sliceProbabilityProgram_cast,
      safeLaw, TrimmedSlice.finiteLaw_weight]
  · norm_num



def approximateBodyLaw (security bits : ℕ) (includeScalar : Bool) : FiniteDist (FirstHistogram.Palette security) :=
  (approximateSeedLaw security bits).mix (fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0)))

theorem body_cast (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    (body security bits includeScalar output.val : ℝ) = (approximateBodyLaw security bits includeScalar).weight output := by
  unfold body
  rw [seedEvaluate_cast, PublicParameterProgram.modulus_value]
  have hM : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  simp_rw [hM, bodyKernel_cast]
  rfl





def fairProfile (security : ℕ) (source : FiniteDist (ActualSeed security))
    (output : FirstHistogram.Palette security) : ℝ :=
  (profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 true source
      (actualBlur security) (actualSecond security) output +
    profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 false source
      (actualBlur security) (actualSecond security) output) / 2

theorem fairProfile_expectation (security : ℕ) (source : FiniteDist (ActualSeed security))
    (output : FirstHistogram.Palette security) :
    fairProfile security source output = source.expectation (fun seed =>
      (diffuseKernel (Parameters.modulus security) (Parameters.anchorWidth security)
        (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) := by
  simp only [fairProfile, profile, TrimmedSlice.mixedLaw, FiniteDist.expectation,
    diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
    AFT.V7Calibration.averagedSliceProgram_cast, intervalStart,
    if_true, Bool.false_eq_true, if_false]
  simp only [mul_div, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem fairProfile_mass (security : ℕ) (source : FiniteDist (ActualSeed security)) :
    ∑ output, fairProfile security source output = 1 := by
  have hm (positive : Bool) : ∑ color, profile (Parameters.modulus security) (Parameters.anchorWidth security)
      1 positive source (actualBlur security) (actualSecond security) color = 1 := by
    exact profile_mass _ _ _ _ _ _ _ ((Parameters.sourceCutoff security : ℤ) - 1)
      ((Parameters.sourceCutoff security : ℤ) - 1)
      (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _)
      (by norm_num) (actualBlur_bound security) (actualSecond_bound security) (by
        have h := deletion_clearance security
        unfold deletion at h
        omega)
  simp only [fairProfile, ← Finset.sum_div, Finset.sum_add_distrib, hm]
  norm_num

def approximateDiffuseLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight := fairProfile security (approximateSeedLaw security bits)
  nonneg output := div_nonneg (add_nonneg (profile_nonneg _ _ _ _ _ _ _ _) (profile_nonneg _ _ _ _ _ _ _ _))
    (by norm_num)
  sum_one := fairProfile_mass security _

theorem diffuse_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (diffuse security bits output.val : ℝ) = (approximateDiffuseLaw security bits).weight output := by
  unfold diffuse
  rw [seedEvaluate_cast, PublicParameterProgram.modulus_value]
  have hA : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  rw [hA]
  exact (fairProfile_expectation security (approximateSeedLaw security bits) output).symm



theorem activationApprox_pos (security bits : ℕ) :
    0 < (LocalPairProgram.activationApprox security bits : ℝ) := by
  have h : 0 < LocalPairProgram.activationApprox security bits :=
    mul_pos (by norm_num) (windowApproxWeight_positive _ _ _ _)
  exact_mod_cast h

theorem primaryRaw_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (primaryRaw security bits output.val : ℝ) =
      ((Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits) *
          (approximateBodyLaw security bits false).weight output -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          (approximateBodyLaw security bits true).weight output -
        2 * Parameters.legCount security * (1 - (LocalPairProgram.activationApprox security bits : ℝ)) *
          (approximateDiffuseLaw security bits).weight output) /
        ((Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits) := by
  have hL : (security + 2)^128 = Parameters.legCount security := by
    simp only [Parameters.legCount_eq, Parameters.base]
  have hB : Parameters.modulus security * (security + 2)^96 = Parameters.bodySize security := by
    simp only [Parameters.bodySize_eq, Parameters.base]
  unfold primaryRaw
  try dsimp only
  rw [PublicParameterProgram.modulus_value, hL, hB]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, body_cast, diffuse_cast]
  simp only [freeMass, Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_one]

theorem primaryRaw_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, primaryRaw security bits output.val) = 1 := by
  have hq : (Parameters.modulus security : ℝ) ≠ 0 := (FirstResponse.modulus_pos security).ne'
  have hl : (Parameters.legCount security : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    rw [Parameters.legCount_eq]
    exact (pow_pos (Parameters.base_pos security) 128).ne'
  have hr := (activationApprox_pos security bits).ne'
  have hmass : (∑ output : FirstHistogram.Palette security, (primaryRaw security bits output.val : ℝ)) = 1 := by
    simp_rw [primaryRaw_cast]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
      FiniteDist.sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold freeMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hq, hl, hr]
    ring
  exact_mod_cast hmass









theorem primary_lower (security bits : ℕ) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primary security bits output.val : ℝ) := by
  unfold primary
  split_ifs with hgood
  · unfold primaryGood at hgood
    rw [PublicParameterProgram.modulus_value] at hgood
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (hgood output)
  · simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value]
    have hq := FirstResponse.modulus_pos security
    apply one_div_le_one_div_of_le hq
    nlinarith

theorem primary_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, primary security bits output.val) = 1 := by
  unfold primary
  by_cases hgood : primaryGood security bits
  · simp only [if_pos hgood]
    exact primaryRaw_mass security bits
  · simp only [if_neg hgood, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, PublicParameterProgram.modulus_value]
    have hq : (Parameters.modulus security : ℚ) ≠ 0 := by
      exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
    field_simp

def approximatePrimaryLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight output := primary security bits output.val
  nonneg output := (by positivity : (0 : ℝ) ≤ 1 / (4 * (Parameters.modulus security : ℝ))).trans
    (primary_lower security bits output)
  sum_one := by exact_mod_cast primary_mass security bits



theorem approximateAnchorLaw_height (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (approximateAnchorLaw security bits primary).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold approximateAnchorLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ scalar, (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
        (Parameters.sourceCutoff security - 1) bits).weight scalar * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun scalar _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_height security primary scalar.val
          (InwardAnchor.scalar_bound security scalar) output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def approximateAnchorPrimaryLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) :=
  (approximatePrimaryLaw security bits).mix (approximateAnchorLaw security bits)

theorem anchorPrimary_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (anchorPrimary security bits output.val : ℝ) = (approximateAnchorPrimaryLaw security bits).weight output := by
  unfold anchorPrimary
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, anchor_cast, approximateAnchorPrimaryLaw, FiniteDist.mix_weight]
  rfl

theorem approximateAnchorPrimaryLaw_height (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (approximateAnchorPrimaryLaw security bits).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold approximateAnchorPrimaryLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (approximatePrimaryLaw security bits).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_left
        (approximateAnchorLaw_height security bits primary output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem approximateAnchorPrimaryLaw_zero_outside (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) :
    (approximateAnchorPrimaryLaw security bits).weight output = 0 := by
  simp only [approximateAnchorPrimaryLaw, FiniteDist.mix_weight, ← anchor_cast,
    anchor_zero_outside security bits _ output hunsafe, Rat.cast_zero, mul_zero, Finset.sum_const_zero]

theorem compensationApprox_cast (security bits : ℕ) :
    (compensationApprox security bits : ℝ) =
      (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits / freeMass security := by
  have hL : (security + 2)^128 = Parameters.legCount security := by
    simp only [Parameters.legCount_eq, Parameters.base]
  have hB : Parameters.modulus security * (security + 2)^96 = Parameters.bodySize security := by
    simp only [Parameters.bodySize_eq, Parameters.base]
  unfold compensationApprox
  try dsimp only
  rw [PublicParameterProgram.modulus_value, hL, hB]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, freeMass]

theorem compensationApprox_nonneg (security bits : ℕ) : 0 ≤ (compensationApprox security bits : ℝ) := by
  rw [compensationApprox_cast]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (activationApprox_pos security bits).le) (freeMass_pos security).le

theorem compensationApprox_le_leg_body (security bits : ℕ) :
    (compensationApprox security bits : ℝ) ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := by
  have hnum : (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits ≤
      (Parameters.legCount security : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (LocalPairProgram.activationApprox_bounds security bits).2
      (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)]
  rw [compensationApprox_cast]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / freeMass security :=
      div_le_div_of_nonneg_right hnum (freeMass_pos security).le
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / ((Parameters.bodySize security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos (bodySize_pos security)) (freeMass_lower security)
    _ = _ := by ring



theorem compensationApprox_anchor_cost (security bits : ℕ) :
    (compensationApprox security bits : ℝ) / Parameters.anchorWidth security ≤ safeHeight security / 2 := by
  have hA : (0 : ℝ) < Parameters.anchorWidth security := by exact_mod_cast InwardAnchor.anchorWidth_pos security
  have hB := bodySize_pos security
  have hq := FirstResponse.modulus_pos security
  have hbudget : 2 * (Parameters.legCount security : ℝ) * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by
    exact_mod_cast anchor_center_budget security
  have hfirst : ((Parameters.legCount security : ℝ) / Parameters.bodySize security) /
      Parameters.anchorWidth security ≤ 1 / (2 * (Parameters.modulus security : ℝ)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hB hA) (by positivity)).mpr
    nlinarith only [hbudget]
  have hs : (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security ≤ Parameters.modulus security := by
    have hM : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
    linarith
  have hsafe : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le
    · have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
      push_cast at h
      linarith
    · exact hs
  exact (div_le_div_of_nonneg_right (compensationApprox_le_leg_body security bits) hA.le).trans
    (hfirst.trans (by convert div_le_div_of_nonneg_right hsafe (by norm_num : (0 : ℝ) ≤ 2) using 1; ring))

def approximateCenterProfile (security bits : ℕ) (output : FirstHistogram.Palette security) : ℝ :=
  (1 + (compensationApprox security bits : ℝ)) * (safeLaw security).weight output -
    (compensationApprox security bits : ℝ) * (approximateAnchorPrimaryLaw security bits).weight output

theorem center_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (center security bits output.val : ℝ) = approximateCenterProfile security bits output := by
  unfold center
  rw [PublicParameterProgram.modulus_value]
  have hM : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  rw [hM]
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one, anchorPrimary_cast]
  rw [safeEntry, AFT.V7Calibration.sliceProbabilityProgram_cast]
  change (1 + (compensationApprox security bits : ℝ)) * TrimmedSlice.law _ _ _ _ - _ = _
  rw [← TrimmedSlice.finiteLaw_weight _ _ _ (by positivity)
    (by have := safe_clearance security; simp only [abs_zero]; omega)]
  rfl

theorem approximateCenterProfile_bounds (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (safeLaw security).weight output / 2 ≤ approximateCenterProfile security bits output ∧
      approximateCenterProfile security bits output ≤
        (1 + (compensationApprox security bits : ℝ)) * (safeLaw security).weight output := by
  have hc := compensationApprox_nonneg security bits
  have hanchor := (approximateAnchorPrimaryLaw security bits).nonneg output
  constructor
  · by_cases hsafe : InwardAnchor.SafeColor security output
    · have hcost := mul_le_mul_of_nonneg_left (approximateAnchorPrimaryLaw_height security bits output) hc
      rw [mul_one_div] at hcost
      have hcost' := compensationApprox_anchor_cost security bits
      unfold approximateCenterProfile
      rw [safeLaw_weight, if_pos hsafe]
      nlinarith only [hcost, hcost', mul_nonneg hc (safeHeight_pos security).le]
    · unfold approximateCenterProfile
      rw [safeLaw_weight, if_neg hsafe, approximateAnchorPrimaryLaw_zero_outside security bits output hsafe]
      simp
  · unfold approximateCenterProfile
    exact sub_le_self _ (mul_nonneg hc hanchor)

theorem center_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, center security bits output.val) = 1 := by
  have hm : (∑ output : FirstHistogram.Palette security, (center security bits output.val : ℝ)) = 1 := by
    simp_rw [center_cast]
    simp only [approximateCenterProfile, Finset.sum_sub_distrib, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
    ring
  exact_mod_cast hm

theorem center_nonneg (security bits : ℕ) (output : FirstHistogram.Palette security) :
    0 ≤ center security bits output.val := by
  have h := (div_nonneg ((safeLaw security).nonneg output) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (approximateCenterProfile_bounds security bits output).1
  rw [← center_cast] at h
  exact_mod_cast h

theorem center_zero_outside (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) : center security bits output.val = 0 := by
  have h : (center security bits output.val : ℝ) = 0 := by
    rw [center_cast]
    unfold approximateCenterProfile
    rw [safeLaw_weight, if_neg hunsafe, approximateAnchorPrimaryLaw_zero_outside security bits output hunsafe]
    ring
  exact_mod_cast h



def approximateCenterLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight output := center security bits output.val
  nonneg output := by exact_mod_cast center_nonneg security bits output
  sum_one := by exact_mod_cast center_mass security bits

def approximateBodyReference (security bits : ℕ) : FiniteDist (ActualControls.SafePalette security) :=
  ActualControls.supportedLaw (approximateCenterLaw security bits) (InwardAnchor.SafeColor security)
    (fun output hunsafe => by
      change (center security bits output.val : ℝ) = 0
      exact_mod_cast center_zero_outside security bits output hunsafe)

def approximateAnchorReference (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    FiniteDist (ActualControls.SafePalette security) :=
  ActualControls.supportedLaw (approximateAnchorLaw security bits primary) (InwardAnchor.SafeColor security)
    (fun output hunsafe => by rw [← anchor_cast, anchor_zero_outside security bits primary output hunsafe, Rat.cast_zero])













end
end CurrentAFT.RationalProposalProgram

end

section
























/-! # Rational programs for the actual sign profile and first inverse

All tables use the same current Gaussian approximation and activation as
the proposal. The inverse is the literal rank-one formula, with an exact
rational denominator guard for low precision. No real matrix inverse is
an input to the program.
-/
namespace CurrentAFT.RationalFirstResponseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def profileKernel (colors width : ℕ) (positive : Bool) (blur source : ℤ) (output : ℕ) : ℚ :=
  AFT.V7Calibration.averagedSliceProgram colors 1
    ((if positive then (width : ℤ) else -2*(width : ℤ)+1)+blur) source width output

def profile (security bits : ℕ) (positive : Bool) (output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed => profileKernel (PublicParameterProgram.modulus security).count
    ((security+2)^48) positive (seed.1.1.val-seed.1.2.val) seed.2.val output)

def signProfile (security bits output : ℕ) : ℚ :=
  (1-LocalPairProgram.activationApprox security bits)*(profile security bits true output-profile security bits false output)

def anchorSign (security color : ℕ) : ℚ :=
  if 2*color < (PublicParameterProgram.modulus security).count-1 then -1
  else if (PublicParameterProgram.modulus security).count-1 < 2*color then 1 else 0

def functional (security : ℕ) (input : ℕ → ℚ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count, anchorSign security color.val*input color.val

def denominator (security bits : ℕ) : ℚ :=
  LocalPairProgram.activationApprox security bits + functional security (signProfile security bits)

def guardedDenominator (security bits : ℕ) : ℚ :=
  max (denominator security bits) (LocalPairProgram.activationApprox security bits / 4)



def inverse (security bits : ℕ) (input : ℕ → ℚ) (output : ℕ) : ℚ :=
  input output - functional security input / guardedDenominator security bits * signProfile security bits output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation

















def actualDenominator (security : ℕ) : ℝ := DiffuseProfiles.activation security +
  AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security)





def PrecisionBudget (security bits : ℕ) : Prop :=
  (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤ 1/(16*(Parameters.base security:ℝ))











def inverseErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security:ℝ)*(112*(Parameters.base security:ℝ)+
    512*(Parameters.base security:ℝ)^2*(8*(Parameters.modulus security:ℝ)+1))



def sufficientBits (security : ℕ) : ℕ :=
  16*Parameters.base security*(8*(131072*Parameters.base security^64)+2)

attribute [local irreducible] sufficientBits









end
end CurrentAFT.RationalFirstResponseProgram

end

section






















/-! # The actual primary inverse including activation and reference whitening -/
namespace CurrentAFT.RationalDensityInverseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (score : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalFirstResponseProgram.inverse security bits
    (fun color => primary security bits color*score color) output /
    (LocalPairProgram.activationApprox security bits*primary security bits output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw

def inverseBound (security : ℕ) : ℝ := 1+32*(Parameters.base security:ℝ)*Parameters.modulus security







def errorConstant (security : ℕ) : ℝ :=
  let base : ℝ := Parameters.base security
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*base*Parameters.dimension security
  (32*base*q)*(RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient) +
    inverseBound security*(32*base*q)^2*(1/2+coefficient)



end
end CurrentAFT.RationalDensityInverseProgram

end

section




















/-! # Explicit rational primary tensor inverse on full joint arrays

The program enumerates the current palette in each retained coordinate.
It applies the actual normalized first inverse in every coordinate, without
factoring the input tensor or querying a real inverse.
-/
namespace CurrentAFT.RationalTensorInverseProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def entry (security bits source output : ℕ) : ℚ :=
  RationalDensityInverseProgram.current security bits (fun color => if color = source then 1 else 0) output

def current (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ) (output : Fin degree → ℕ) : ℚ :=
  ∑ source : Fin degree → Fin (PublicParameterProgram.modulus security).count,
    input (fun index => (source index).val) *
      ∏ index, entry security bits (source index).val (output index)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def actualBound (security : ℕ) : ℝ :=
  8 * (Parameters.base security : ℝ) * Parameters.modulus security *
    RationalDensityInverseProgram.inverseBound security









def factorBound (security : ℕ) : ℝ :=
  1 + actualBound security + RationalDensityInverseProgram.errorConstant security









def tensorErrorConstant (security degree : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^degree * degree * RationalDensityInverseProgram.errorConstant security *
    (factorBound security)^degree





end
end CurrentAFT.RationalTensorInverseProgram

end

section


























/-! # Actual first mass lift with a rational rank-one inverse

The mass profile is passed directly to the first inverse. Activation and
the primary output atom are the only additional denominators, with proved
polynomial lower bounds. Input profile approximation is handled separately.
-/
namespace CurrentAFT.RationalMassLiftProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (profile : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalFirstResponseProgram.inverse security bits profile output /
    (LocalPairProgram.activationApprox security bits * primary security bits output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw

def actual (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  (PrimaryTensorInverse.densityInverse security).comp (RootTaggedLocal.profileDensity security)















def errorConstant (security : ℕ) : ℝ :=
  (32 * (Parameters.base security : ℝ) * Parameters.modulus security) * RationalFirstResponseProgram.inverseErrorConstant security +
    RationalDensityInverseProgram.inverseBound security * (32 * (Parameters.base security : ℝ) * Parameters.modulus security)^2 *
      (1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security)







end
end CurrentAFT.RationalMassLiftProgram

end

section






















/-! # Literal one-slot primary mass-certificate data -/
namespace CurrentAFT.RationalMassCertificateTable
open AFT GradedControlAlgebra BackgroundFamilies PrimaryMassFamilies ActualControls
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance massFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



end
end CurrentAFT.RationalMassCertificateTable

end

section























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RationalFiniteMean
end CurrentAFT.RationalFiniteMean





/-! # Fixed-scalar pair means and their original one-primary certificate -/
namespace CurrentAFT.RationalConditionalPairProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def pairProfile (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  (∑ other : Fin (colors security), LocalPairProgram.current security bits primary scalar output other.val)+
    ∑ other : Fin (colors security), LocalPairProgram.current security bits primary scalar other.val output

def pairMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  ∑ primary : Fin (colors security), RationalProposalProgram.primary security bits primary.val*pairProfile security bits primary.val scalar output

def centeredMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  pairMean security bits scalar output-2/(colors security:ℚ)

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order
    (RationalMassLiftProgram.current security bits (centeredMean security bits scalar)) (fun _ => 0)

noncomputable section
open scoped Classical
local instance conditionalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def actualPairProfile (security : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) : ℝ :=
  (∑ other, (LocalReferenceEnergy.pairAt security primary scalar).weight (output, other))+
    ∑ other, (LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)

def profileErrorConstant (security : ℕ) : ℝ := 6*(Parameters.modulus security:ℝ)+
  2*(Parameters.modulus security:ℝ)*(64*(Parameters.base security:ℝ)*Parameters.dimension security)

def computedBound (security : ℕ) : ℝ := 4+6*(Parameters.modulus security:ℝ)

def errorConstant (security : ℕ) : ℝ := RationalMassLiftProgram.errorConstant security*computedBound security+
  RationalTensorInverseProgram.actualBound security*profileErrorConstant security



















end
end CurrentAFT.RationalConditionalPairProgram

end

section

























/-! # Literal rational profiles for the current mixed background data

Safe projections are exact rational finite sums.  Root convolutions keep
both Gaussian edges and use the same local seed law as the actual model.
-/
namespace CurrentAFT.RationalBackgroundProfiles
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus Parameters.base Parameters.safeMargin

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def margin (security : ℕ) : ℕ := 3*(security+2)^2

def safe (security output : ℕ) : ℚ := RationalProposalProgram.safeEntry (colors security) (margin security) output

def shifted (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalProposalProgram.bodyKernel (colors security) (margin security) shift output

def Safe (security output : ℕ) : Prop :=
  (margin security:ℤ) ≤ output ∧ (output:ℤ) < (colors security:ℤ)-margin security

instance safeDecidable (security output : ℕ) : Decidable (Safe security output) := by unfold Safe; infer_instance

def unsafeProfile (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  if Safe security output then 0 else shifted security shift output

def unsafeTotal (security : ℕ) (shift : ℤ) : ℚ :=
  ∑ output : Fin (colors security), unsafeProfile security shift output.val

def projected (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  shifted security shift output-unsafeProfile security shift output+unsafeTotal security shift*safe security output

def seedProfile (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ := projected security shift output-safe security output

def inverseShift (security : ℕ) (shift : ℤ) (output : ℕ) : ℕ :=
  (((output:ℤ)-shift) % (colors security:ℤ)).toNat

def convolution (security bits : ℕ) (profile : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalProposalProgram.seedEvaluate security bits (fun seed =>
    profile (inverseShift security (seed.1.1.val-seed.1.2.val) output))

def bodyDeviation (security bits output : ℕ) : ℚ :=
  RationalProposalProgram.body security bits false output-1/(colors security:ℚ)

def residual (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  convolution security bits (unsafeProfile security shift) output-
    unsafeTotal security shift*RationalProposalProgram.body security bits false output

noncomputable section
open scoped Classical





























end
end CurrentAFT.RationalBackgroundProfiles

end

section
























/-! # Numerical densities of the original mixed background certificates -/
namespace CurrentAFT.RationalBackgroundDensities
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def primary (security bits output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (RationalBackgroundProfiles.bodyDeviation security bits) output

def residual (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (RationalBackgroundProfiles.residual security bits shift) output

def body (security bits output : ℕ) : ℚ :=
  1-RationalBackgroundProfiles.safe security output/RationalProposalProgram.center security bits output

def seed (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalBackgroundProfiles.seedProfile security shift output/RationalProposalProgram.center security bits output

noncomputable section
open scoped Classical

def centerErrorConstant (security : ℕ) : ℝ :=
  64*(Parameters.base security:ℝ)*Parameters.dimension security*Parameters.modulus security+2

def primaryErrorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+3*RationalTensorInverseProgram.actualBound security

def residualErrorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+6*RationalTensorInverseProgram.actualBound security

def bodyErrorConstant (security : ℕ) : ℝ := (2*(Parameters.modulus security:ℝ))^2*centerErrorConstant security























end
end CurrentAFT.RationalBackgroundDensities

end

section






















/-! # The actual paired public score evaluated with one rational reference

The primary, safe center, anchor and activation are the current computed
tables. The error theorem compares their literal score with the actual
paired lift, uniformly in the exposed primary and safe center colors.
-/
namespace CurrentAFT.RationalPairedLiftProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def anchorProfile (security bits : ℕ) (score : ℕ → ℚ) (output : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    primary security bits color.val * score color.val * anchor security bits color.val output

def current (security bits : ℕ) (score : ℕ → ℚ) (primary centerColor : ℕ) : ℚ :=
  score primary - LocalPairProgram.activationApprox security bits * anchorProfile security bits score centerColor /
    center security bits centerColor

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference





section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]







end Generic

def errorConstant (security : ℕ) : ℝ :=
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*(Parameters.base security:ℝ)*Parameters.dimension security
  q + 2*q^2*(coefficient+1) + 4*q^2*(coefficient*q+2)





end
end CurrentAFT.RationalPairedLiftProgram

end

section























/-! # Sparse rational entries of the actual selected closed-cycle law

Only ordered distinct selected sites and their touched latent edges are
enumerated. The full body permutation and all unused latent coordinates
are eliminated by exact probability identities. Every entry test below
is an explicit modular indicator, not an input oracle.
-/
namespace CurrentAFT.CurrentCycleEntryProgram

open AFT GaussianSource CycleSelections CyclePatternProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyCount (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count * (security + 2)^96

def pointTest (colors order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) : ℚ :=
  if ∀ index, roots index % colors = (output index : ℤ) then 1 else 0

def selectedEntry (security bits order : ℕ) (output : Fin order → ℕ) : ℚ :=
  averagedEvaluate security (edgeCutoff security) bits (bodyCount security) order
    (fun _ => pointTest (PublicParameterProgram.modulus security).count order output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩




















end
end CurrentAFT.CurrentCycleEntryProgram

end

section





















/-! # Root centering as a signed mass with no root-atom inverse

After multiplication by its actual root-reference mass, the selected
coefficient is an expectation of products `delta - marginal`. This is an
identity of coefficient data, before physical evaluation. The rational
program evaluates those explicit bounded tests on sparse cycle patterns.
-/
namespace CurrentAFT.RootSignedMassProgram

open AFT GaussianSource CycleSelections CyclePatternProgram CycleRootExpansion
  CurrentCycleEntryProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def referenceEntry (security bits output : ℕ) : ℚ :=
  selectedEntry security bits 1 (fun _ => output)

def signedTest (security bits order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) : ℚ :=
  ∏ index, ((if roots index % (PublicParameterProgram.modulus security).count = (output index : ℤ)
    then (1 : ℚ) else 0) - referenceEntry security bits (output index))

def weightedEntry (security bits order : ℕ) (output : Fin order → ℕ) : ℚ :=
  averagedEvaluate security (edgeCutoff security) bits (bodyCount security) order
    (fun _ => signedTest security bits order output)

def oneEquiv (Color : Type*) : (Fin 1 → Color) ≃ Color where
  toFun word := word 0
  invFun color _ := color
  left_inv word := by
    funext index
    exact congrArg word (Subsingleton.elim (0 : Fin 1) index)
  right_inv _ := rfl

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩





















def signedKernel (security bits order : ℕ) (output input : Fin order → Root security) : ℝ :=
  ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
    (referenceEntry security bits (output index).val : ℝ))







end
end CurrentAFT.RootSignedMassProgram

end

section

























/-! # Actual fixed-root mass columns without division by root atoms

The root reference is only a multiplier. The formulas below remain valid
at zero atoms. They expose the finite, fixed-root experiments that a
rational matrix-entry program evaluates before root averaging.
-/
namespace CurrentAFT.RootMassColumns

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalReferenceEnergy FirstHistogram ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

section Fiber
variable {Root Control Output : Type*} [Fintype Root]
  [AddCommMonoid Output] [Module ℝ Output]

def fiber (root : Root) (score : Control → ℝ) : Root → Control → ℝ :=
  fun other => if other = root then score else 0



end Fiber

/-- The real same-scalar paired experiment at two fixed roots. -/
def primaryMassAt (security : ℕ) (roots : RootTaggedSelected.RootPair security) :
    (ActualControls.Palette security → ℝ) →ₗ[ℝ]
      ((Fin 4 → ActualControls.Palette security) → ℝ) :=
  ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
    PairedReferenceEnergy.pairedMassLinear security (roots.1.val : ℤ) (roots.2.val : ℤ) scalar





/-- The full primary coefficient lift still has this root-mass factor.
The finite reciprocal is the actual one used by the full response. -/
def primaryResponseAt (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) : LocalCoefficientFamily.Family security order :=
  LocalRaisingLinear.completeFamilyLinear security order (primaryMassAt security roots score) *
    LocalRaisingBounds.positiveInverse security order





/-- The actual safe-control push at one fixed ordinary root. -/
def ordinaryMassAt (security : ℕ) (root : CycleRootExpansion.Root security) :
    (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root)











end
end CurrentAFT.RootMassColumns

end

section






















/-! # Rational fixed-root paired mass entries

Multiplication by the center reference cancels the paired-score quotient.
The resulting program uses only the actual primary, center, anchor, pair
and scalar tables, finite sums, and rational arithmetic. Unsafe center
colors and zero root atoms require no exceptional division.
-/
namespace CurrentAFT.RationalRootMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def anchorScore (security bits : ℕ) (score : ℕ → ℚ) (center : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    anchor security bits color.val center * primary security bits color.val * score color.val

def weightedScore (security bits : ℕ) (score : ℕ → ℚ) (primaryColor centerColor : ℕ) : ℚ :=
  center security bits centerColor * score primaryColor -
    LocalPairProgram.activationApprox security bits * anchorScore security bits score centerColor

def controlRest (security : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (centerColor : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  bodyKernel (PublicParameterProgram.modulus security).count (3 * (security + 2)^2)
    (attachmentRoot + scalar) (word 3) *
      (if ((centerColor : ℤ) + compensatorRoot) % (PublicParameterProgram.modulus security).count =
        (word 0 : ℤ) then 1 else 0)

def fixedMass (security bits : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ primaryColor : Fin (PublicParameterProgram.modulus security).count,
    ∑ centerColor : Fin (PublicParameterProgram.modulus security).count,
      primary security bits primaryColor.val *
        weightedScore security bits score primaryColor.val centerColor.val *
          LocalPairProgram.current security bits primaryColor.val scalar (word 1) (word 2) *
            controlRest security compensatorRoot attachmentRoot scalar centerColor.val word

def scalarAverage (security cutoff bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ index : Fin (2*cutoff+1),
    gaussianWeight security cutoff bits (FiniteConvolutionProgram.windowIndexEquiv cutoff index) *
      fixedMass security bits compensatorRoot attachmentRoot
        (FiniteConvolutionProgram.windowIndexEquiv cutoff index).val score word

def primaryMass (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  scalarAverage security ((security + 2)^2 - 1) bits compensatorRoot attachmentRoot score word

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw



def actualWeightedScore (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (primaryColor centerColor : FirstHistogram.Palette security) : ℝ :=
  (centerLaw security).weight centerColor * score primaryColor -
    DiffuseProfiles.activation security * PairedResponse.anchorWeightedScore security score centerColor













def primaryErrorConstant (security : ℕ) : ℝ :=
  64 * (Parameters.base security : ℝ) * Parameters.dimension security

def weightedErrorConstant (security : ℕ) : ℝ :=
  (primaryErrorConstant security * Parameters.modulus security + 2) + 1 +
    (Parameters.modulus security : ℝ) * (primaryErrorConstant security + 1)



def actualRest (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) : ℝ :=
  (attachmentAt security attachmentRoot scalar).weight (word 3) *
    FirstHistogram.atom (shiftEquiv security compensatorRoot centerColor) (word 0)











def fixedErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^2 *
    (8 * primaryErrorConstant security + 4 * weightedErrorConstant security + 6)











def primaryMassErrorConstant (security : ℕ) : ℝ :=
  fixedErrorConstant security + 2 * (Parameters.modulus security : ℝ)^2



end
end CurrentAFT.RationalRootMassProgram

end

section















/-! # Removing root masks before coefficient evaluation

The actual joint input is fixed by every root mask. This file removes
those masks in the canonical coefficient family itself. The selected
ordinary channel retains its original hybrid body coefficient.
-/
namespace CurrentAFT.ActualRootProjectionData
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount





def unprojectedChannel {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) →
      (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] Family security order
  | .inl (.inl _) => (RootTaggedSelectedChannel.channel security order).comp (RootPrimaryGroupedChannel.pairLinear security)
  | .inl (.inr _) => (SelectedOrdinaryHybrid.channel security order horder).comp (RootOrdinaryGroupedChannel.toRaw security)
  | .inr index => RootUnselectedGrouped.channel security order horder queue index.val.val





end
end CurrentAFT.ActualRootProjectionData

end

section





















/-! # Actual unprojected columns and their root reference factors

These identities expose the root mass as a multiplier in canonical
coefficient data. In particular they can be combined with the signed
root-mass program without inverting a root atom.
-/
namespace CurrentAFT.RootReferenceColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference





def primaryAt (security order : ℕ) (roots : RootTaggedSelected.RootPair security) (primaryColor : Palette security) :
    LocalCoefficientFamily.Family security order :=
  RootMassColumns.primaryResponseAt security order roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1))



def ordinaryFiber (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.Input security → ℝ :=
  fun sample => RootMassColumns.fiber root score sample.1 sample.2



def ordinaryDensityAt (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    Palette security → ℝ :=
  PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security (RootMassColumns.ordinaryMassAt security root
      (centerLinear (bodyReference security) score)))

theorem ordinaryDensityAt_mean (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    (primaryLaw security).expectation (ordinaryDensityAt security root score) = 0 := by
  rw [ordinaryDensityAt, PrimaryTensorInverse.densityInverse_mean, RootTaggedLocal.profileDensity_mean]
  have h := SelectedOrdinaryRoot.push_test (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root)
    (centerLinear (bodyReference security) score) (fun _ => 1)
  simp only [mul_one] at h
  change (∑ color, RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) score) color) = _ at h
  rw [h, center_mean, mul_zero]



def ordinaryAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) : LocalCoefficientFamily.Family security order :=
  LocalRaisingLinear.primaryEmbeddingLinear security order horder
    ⟨ordinaryDensityAt security root score, ordinaryDensityAt_mean security root score⟩ *
      OrdinaryRaising.positiveInverse security order horder









def hybridAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) : LocalCoefficientFamily.Family security order :=
  SelectedOrdinaryHybrid.independentChannel security order horder score +
    ordinaryAt security order horder root score -
      ∑ other, (rootReference security).weight other • ordinaryAt security order horder other score



def singletonDensityAt (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    Palette security → ℝ :=
  PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security (RootTaggedLocal.deviationProfile security role queue root))

theorem singletonDensityAt_mean (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    (primaryLaw security).expectation (singletonDensityAt security role queue root) = 0 := by
  rw [singletonDensityAt, PrimaryTensorInverse.densityInverse_mean, RootTaggedLocal.profileDensity_mean,
    RootTaggedLocal.deviationProfile_mass, mul_zero]

def singletonFirstAt (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
    (singletonDensityAt security role queue root) (singletonDensityAt_mean security role queue root)



def singletonAt (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  singletonFirstAt security order horder role queue root * RootMeanPrimary.positiveInverse security order horder role queue



def legHigherAt (security order : ℕ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  RootLegCoefficientLinear.higherFamilyLinear security order
    ((ActualBlockFock.primaryLawAt security root.val).weight - RootTaggedLegHigher.rawMassLinear security (fun _ => 1))



def legAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security) : LocalCoefficientFamily.Family security order :=
  (singletonFirstAt security order horder .attachment 0 root + legHigherAt security order root) *
    RootLegReciprocal.reciprocal security order



def unselectedAt (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (root : Root security) : LocalCoefficientFamily.Family security order :=
  match block with
  | .inl _ => legAt security order horder root
  | .inr (.inl _) => singletonAt security order horder .free 0 root
  | .inr (.inr _) => singletonAt security order horder .queue queue root











def reducedColumn {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security)) :
    (group : PairedRootPlacement.ActiveGroup selection tagged) →
      ActualRootGroupedChannel.Input selection tagged group → LocalCoefficientFamily.Family security order
  | .inl (.inl _), source => primaryAt security order (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2
  | .inl (.inr _), source => hybridAt security order horder (source.1 (0 : Fin 1)) (Pi.single source.2 1)
  | .inr index, source => unselectedAt security order horder queue index.val.val (source.1 (0 : Fin 1))



end
end CurrentAFT.RootReferenceColumns

end

section


























/-! # Rational actual shifted and mean body profiles for every role

The root mean uses the same protected two-edge blur as the construction.
Free, attachment and queue profiles retain their original laws, including
the one attachment scalar and the fixed common queue.
-/
namespace CurrentAFT.RationalRootProfileProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  RootTaggedLocal
open UniformBodyProfiles (BodyRole preRootLaw)
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def attachment (security bits output : ℕ) : ℚ :=
  ∑ index : Fin (2*((security+2)^2-1)+1),
    RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits
      (FiniteConvolutionProgram.windowIndexEquiv ((security+2)^2-1) index) *
      RationalBackgroundProfiles.shifted security
        (FiniteConvolutionProgram.windowIndexEquiv ((security+2)^2-1) index).val output

def preRoot (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  match role with
  | .free => RationalProposalProgram.center security bits output
  | .attachment => attachment security bits output
  | .queue => RationalBackgroundProfiles.shifted security queue output

def shifted (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  preRoot security bits role queue (RationalBackgroundProfiles.inverseShift security root output)

def mean (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  RationalBackgroundProfiles.convolution security bits (preRoot security bits role queue) output

def deviation (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  shifted security bits role queue root output - mean security bits role queue output

def meanDeviation (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  mean security bits role queue output - 1 / (PublicParameterProgram.modulus security).count

def firstDensity (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (deviation security bits role queue root) output

def meanDensity (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (meanDeviation security bits role queue) output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw



def approximatePreRoot (security bits : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (Palette security) :=
  match role with
  | .free => RationalProposalProgram.approximateCenterLaw security bits
  | .attachment =>
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).mix
        (fun scalar => (safeLaw security).map (shiftEquiv security scalar.val))
  | .queue => (safeLaw security).map (shiftEquiv security queue)





def preRootError (security : ℕ) : ℝ :=
  RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 3

























def firstErrorConstant (security : ℕ) : ℝ :=
  2 * RationalMassLiftProgram.errorConstant security +
    RationalTensorInverseProgram.actualBound security * (2 * preRootError security + 3)

def meanErrorConstant (security : ℕ) : ℝ :=
  2 * RationalMassLiftProgram.errorConstant security +
    RationalTensorInverseProgram.actualBound security * (3 + preRootError security)







end
end CurrentAFT.RationalRootProfileProgram

end

section


























/-! # Computed diffuse-pair safe seed and its actual quadratic residual -/
namespace CurrentAFT.RationalDiffuseResidualProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds DiffusePairResidual DiffusePairResidualRates
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def evaluate (security colors width cutoff bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  ∑ sign : Bool, ∑ left : Fin (2*cutoff+1), ∑ right : Fin (2*cutoff+1),
    (1 / 2 : ℚ) * RationalProposalProgram.gaussianWeight security cutoff bits
      (FiniteConvolutionProgram.windowIndexEquiv cutoff left) *
      RationalProposalProgram.gaussianWeight security cutoff bits
        (FiniteConvolutionProgram.windowIndexEquiv cutoff right) *
      AFT.V7Calibration.averagedPairProgram colors 1
        ((if sign then (width : ℤ) else -2 * (width : ℤ) + 1) +
          ((FiniteConvolutionProgram.windowIndexEquiv cutoff left).val -
            (FiniteConvolutionProgram.windowIndexEquiv cutoff right).val)) scalar width first second

def pair (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits scalar first second



def seed (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  rationalCanonicalPairProgram (PublicParameterProgram.modulus security).count
    (RationalBackgroundProfiles.safe security)
    (fun first second => if RationalBackgroundProfiles.Safe security first ∧ RationalBackgroundProfiles.Safe security second then
      pair security bits scalar first second else 0) first second

def uniformCanonical (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  rationalCanonicalPairProgram (PublicParameterProgram.modulus security).count
    (fun _ => 1 / (PublicParameterProgram.modulus security).count) (pair security bits scalar) first second

def smoothedSeed (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  RationalBackgroundProfiles.convolution security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second) first

def residual (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  uniformCanonical security bits scalar first second - smoothedSeed security bits scalar first second

def bodyDensity (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  seed security bits scalar first second /
    (RationalProposalProgram.center security bits first * RationalProposalProgram.center security bits second)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw
attribute [local irreducible] pair seed smoothedSeed

def approximatePairSeed (security bits : ℕ) : FiniteDist (PairSeed security) :=
  (FiniteDist.uniform Bool).prod
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))

def pairTest (security : ℕ) (scalar : ℤ) (first second : Palette security) (sample : PairSeed security) : ℝ :=
  AFT.TrimmedSlice.averagedPair (Parameters.modulus security) 1 (pairStart security sample) scalar
    (Parameters.anchorWidth security) first second















def pairBound (security : ℕ) : ℝ := ((Parameters.modulus security : ℝ) + 1)^2

















end
end CurrentAFT.RationalDiffuseResidualProgram

end

section






















/-! # The original safe diffuse-pair body certificate, evaluated rationally -/
namespace CurrentAFT.RationalDiffuseCertificateProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds RationalDiffuseResidualProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw







def bodyErrorConstant (security : ℕ) : ℝ :=
  2 * pairBound security * (4 * (Parameters.modulus security : ℝ)^2) +
    pairBound security * (2 * RationalBackgroundDensities.centerErrorConstant security) *
      (4 * (Parameters.modulus security : ℝ)^2)^2



end
end CurrentAFT.RationalDiffuseCertificateProgram

end

section




















/-! # A finite rational matrix tensor for the actual primary mass lift -/
namespace CurrentAFT.RationalMassLiftTensorProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def entry (security bits source output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (fun color => if color = source then 1 else 0) output

def current (security bits degree : ℕ) (profile : (Fin degree → ℕ) → ℚ) (output : Fin degree → ℕ) : ℚ :=
  ∑ source : Fin degree → Fin (PublicParameterProgram.modulus security).count,
    profile (fun index => (source index).val) * ∏ index, entry security bits (source index).val (output index)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw PublicParameterProgram.modulus









def factorBound (security : ℕ) : ℝ :=
  1 + RationalTensorInverseProgram.actualBound security + RationalMassLiftProgram.errorConstant security





def errorConstant (security degree : ℕ) (bound profileError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^degree *
    (bound * degree * RationalMassLiftProgram.errorConstant security + profileError) * (factorBound security)^degree



end
end CurrentAFT.RationalMassLiftTensorProgram

end

section


























/-! # Both original coefficient fibers of the actual diffuse certificate -/
namespace CurrentAFT.RationalDiffuseFamilyProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalDiffuseResidualProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyTable {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ) (value : Body → Body → Scalar) :
    Table Scalar Primary Body order := fun arity _ centers =>
  if h : arity.val.1.val = 0 ∧ arity.val.2.val = 2 then
    value (centers ⟨0, by omega⟩) (centers ⟨1, by omega⟩) else 0

def primaryTable {Scalar Primary Body : Type*} [Zero Scalar] (order degree : ℕ)
    (value : (Fin degree → Primary) → Scalar) : Table Scalar Primary Body order := fun arity colors _ =>
  if h : degree = arity.val.1.val ∧ 0 = arity.val.2.val then value (colors ∘ finCongr h.1) else 0

def body (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  bodyTable order (bodyDensity security bits scalar)

def primary (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  primaryTable order 2 (RationalMassLiftTensorProgram.current security bits 2
    (fun word => residual security bits scalar (word 0) (word 1)))

def current (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  body security bits order scalar + primary security bits order scalar

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  primaryLaw centerLaw PublicParameterProgram.modulus





def primaryErrorConstant (security : ℕ) : ℝ :=
  RationalMassLiftTensorProgram.errorConstant security 2
    (2 * pairBound security) (10 * pairBound security)





def errorConstant (security : ℕ) : ℝ :=
  RationalDiffuseCertificateProgram.bodyErrorConstant security + primaryErrorConstant security





end
end CurrentAFT.RationalDiffuseFamilyProgram

end

section














namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram



/-! # Fixed-degree rational powers and finite inverse tables

Only powers up to the fixed calibration order occur in the inverse and
binomial programs. Population powers are represented by binomial coefficients,
rather than by a population-length sequence of approximate multiplications.
-/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def unit {Scalar Primary Body : Type*} [Zero Scalar] [One Scalar] (order : ℕ) : Table Scalar Primary Body order :=
  fun arity _ _ => if arity = zeroArity order then 1 else 0

def power {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (table : Table Scalar Primary Body order) : ℕ → Table Scalar Primary Body order
  | 0 => unit order
  | count+1 => product order (power order table count) table

def reciprocal {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (table : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun arity colors centers => ∑ count ∈ Finset.range (order+1),
    power order (unit order - table) count arity colors centers

def binomial {Scalar Primary Body : Type*} [Field Scalar] (order population : ℕ)
    (table : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun arity colors centers => ∑ count ∈ Finset.range (order+1),
    (population.choose count : Scalar) * power order table count arity colors centers

noncomputable section
open scoped Classical
local instance powerFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





















end
end CurrentAFT.RationalFamilyProductProgram

end

section













/-! # Coefficient-table arithmetic commutes with palette representation -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable {Scalar Primary Body Primary' Body' : Type*}

def pullback (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) : Table Scalar Primary' Body' order :=
  fun arity colors centers => table arity (primary ∘ colors) (body ∘ centers)















end CurrentAFT.RationalFamilyProductProgram

end

section















/-! # Arithmetic errors in the literal current mixed coefficient data -/
namespace CurrentAFT.RationalActualFamilyApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance approximationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def interpret (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  RationalFamilyProductProgram.pullback order Fin.val (fun color : SafePalette security => color.val.val)
    (RationalFamilyProductProgram.realTable order table)

def data (security order : ℕ) (family : ActualFamily security order) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  fun arity => (family arity).val





def coordinateFactor (security order : ℕ) : ℝ :=
  (2*(Parameters.modulus security:ℝ)*Parameters.dimension security)^order



def productError (order : ℕ) (A B e f : ℝ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*(e*B+(A+e)*f)





end
end CurrentAFT.RationalActualFamilyApproximation

end

section






















/-! # The exact mixed free and queue certificate tables with rational leaves

These are the original primary/body coefficient data, before leading
endpoint evaluation.  The rational approximation is made in those data.
-/
namespace CurrentAFT.RationalBackgroundProgram
open AFT ControlCoordinates GradedControlAlgebra BackgroundFamilies ActualControls
  RationalBackgroundTable RationalBackgroundDensities
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def free (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  firstTable order (RationalBackgroundDensities.primary security bits) (RationalBackgroundDensities.body security bits)

def translation (security bits order : ℕ) (shift : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  firstTable order (fun color => RationalBackgroundDensities.primary security bits color+
    RationalBackgroundDensities.residual security bits shift color) (RationalBackgroundDensities.seed security bits shift)

noncomputable section
open scoped Classical
local instance programFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





def freeErrorConstant (security : ℕ) : ℝ := primaryErrorConstant security+bodyErrorConstant security

def translationErrorConstant (security : ℕ) : ℝ := primaryErrorConstant security+residualErrorConstant security+2*bodyErrorConstant security







end
end CurrentAFT.RationalBackgroundProgram

end

section






















/-! # The original marked mixed seed, evaluated in the rational references -/
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed MarkedPairLeading
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def fixedAnchor (security primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  RationalProposalProgram.anchorKernel (colors security) ((security+2)^48) primary (-scalar) output

def rawDensity (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  fixedAnchor security primary scalar output/RationalProposalProgram.center security bits output

def secondCentered (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  rawDensity security bits primary scalar output-1

def secondMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  ∑ primary : Fin (colors security), RationalProposalProgram.primary security bits primary.val*
    secondCentered security bits primary.val scalar output

def uniformRelative (security bits primary : ℕ) : ℚ :=
  (1/(colors security:ℚ))/RationalProposalProgram.primary security bits primary

def seedDensity (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  secondCentered security bits primary scalar output-uniformRelative security bits primary*secondMean security bits scalar output

def inverseDensity (security bits : ℕ) (scalar : ℤ) (primary center : ℕ) : ℚ :=
  RationalDensityInverseProgram.current security bits (fun color => seedDensity security bits color scalar center) primary

noncomputable section
open scoped Classical













end
end CurrentAFT.RationalMarkedSeedProgram

end

section





















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RationalFiniteMean
end CurrentAFT.RationalFiniteMean



/-! # Numerical error of the original marked mixed seed -/
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def primaryErrorConstant (security : ℕ) : ℝ := 64*(Parameters.base security:ℝ)*Parameters.dimension security

def profileBound (security : ℕ) : ℝ := 2*(Parameters.modulus security:ℝ)+1

def meanErrorConstant (security : ℕ) : ℝ := RationalBackgroundDensities.bodyErrorConstant security+
  profileBound security*((Parameters.modulus security:ℝ)*primaryErrorConstant security)

def uniformErrorConstant (security : ℕ) : ℝ := (4*(Parameters.modulus security:ℝ))^2*primaryErrorConstant security

def seedErrorConstant (security : ℕ) : ℝ := RationalBackgroundDensities.bodyErrorConstant security+
  4*meanErrorConstant security+profileBound security*uniformErrorConstant security

def inverseErrorConstant (security : ℕ) : ℝ := RationalDensityInverseProgram.errorConstant security*(5*profileBound security)+
  RationalTensorInverseProgram.actualBound security*seedErrorConstant security



















end
end CurrentAFT.RationalMarkedSeedProgram

end

section






















/-! # The actual marked `(1,1)` canonical coefficient data -/
namespace CurrentAFT.RationalMarkedCertificateProgram
open AFT ControlCoordinates GradedControlAlgebra ActualControls MarkedPairCertificates
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => if h : arity.val.1.val=1 ∧ arity.val.2.val=1 then
    RationalMarkedSeedProgram.inverseDensity security bits scalar (colors ⟨0, by omega⟩) (centers ⟨0, by omega⟩) else 0

noncomputable section
open scoped Classical
local instance certificateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def ideal (security order : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  fun arity colors centers => if h : arity.val.1.val=1 ∧ arity.val.2.val=1 then
    MarkedPairCertificates.inverseDensity security scalar (colors ⟨0, by omega⟩) (centers ⟨0, by omega⟩) else 0







end
end CurrentAFT.RationalMarkedCertificateProgram

end

section






















/-! # The original primary-deviation certificate as a rational table -/
namespace CurrentAFT.RationalPrimaryDeviationProgram
open AFT RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw

def profile (security bits output : ℕ) : ℚ :=
  RationalProposalProgram.primary security bits output -
    1/((PublicParameterProgram.modulus security).count:ℚ)

def current (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order
    (RationalMassLiftProgram.current security bits (profile security bits)) (fun _ => 0)

noncomputable section
open scoped Classical
local instance deviationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def profileErrorConstant (security : ℕ) : ℝ :=
  64*(Parameters.base security:ℝ)*Parameters.dimension security

def errorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+
    RationalTensorInverseProgram.actualBound security*profileErrorConstant security











end
end CurrentAFT.RationalPrimaryDeviationProgram

end

section




























/-! # The complete original marked quadratic certificate data -/
namespace CurrentAFT.RationalMarkedPairProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
  ProposalPrimary.primaryLaw ActualControls.bodyReference
  RationalPrimaryDeviationProgram.current RationalBackgroundProgram.free
  RationalMarkedCertificateProgram.current RationalFamilyProductProgram.product

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalMarkedCertificateProgram.current security bits order scalar arity colors centers+
    RationalFamilyProductProgram.product order (RationalPrimaryDeviationProgram.current security bits order)
      (RationalBackgroundProgram.free security bits order) arity colors centers

noncomputable section
open scoped Classical
local instance markedPairFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def primaryBound (security order : ℕ) : ℝ := coordinateFactor security order*24
def freeBound (security order : ℕ) : ℝ := coordinateFactor security order*84
def errorConstant (security order : ℕ) : ℝ :=
  RationalMarkedSeedProgram.inverseErrorConstant security+
    productError order (primaryBound security order) (freeBound security order)
      (RationalPrimaryDeviationProgram.errorConstant security) (RationalBackgroundProgram.freeErrorConstant security)













end
end CurrentAFT.RationalMarkedPairProgram

end

section






















/-! # The actual activation mixture of the original two quadratic certificates -/
namespace CurrentAFT.RationalPairQuadraticProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalDiffuseFamilyProgram.current RationalMarkedPairProgram.current

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    (1-LocalPairProgram.activationApprox security bits)*
      RationalDiffuseFamilyProgram.current security bits order scalar arity colors centers+
    LocalPairProgram.activationApprox security bits*
      RationalMarkedPairProgram.current security bits order scalar arity colors centers

noncomputable section
open scoped Classical
local instance pairQuadraticFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def diffuseBound (security order : ℕ) : ℝ := coordinateFactor security order*388480
def markedBound (security order : ℕ) : ℝ := coordinateFactor security order*18400
def errorConstant (security order : ℕ) : ℝ :=
  RationalDiffuseFamilyProgram.errorConstant security+RationalMarkedPairProgram.errorConstant security order+
    (diffuseBound security order+markedBound security order)/2











end
end CurrentAFT.RationalPairQuadraticProgram

end

section
























/-! # The same-scalar average and the original balanced leg-linear data -/
namespace CurrentAFT.RationalBackgroundLinearProgram
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def cutoff (security : ℕ) : ℕ := (security+2)^2-1

def meanTranslation (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ index : Fin (2*cutoff security+1),
    RationalProposalProgram.gaussianWeight security (cutoff security) bits
      (FiniteConvolutionProgram.windowIndexEquiv (cutoff security) index) *
      RationalBackgroundProgram.translation security bits order
        (FiniteConvolutionProgram.windowIndexEquiv (cutoff security) index).val arity colors centers

def freeMass (security : ℕ) : ℚ :=
  ((PublicParameterProgram.modulus security).count:ℚ)*(security+2)^96-(security+2)^128-(PublicParameterProgram.modulus security).count

def legLinear (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    -(freeMass security*RationalBackgroundProgram.free security bits order arity colors centers+
      ((PublicParameterProgram.modulus security).count:ℚ)*meanTranslation security bits order arity colors centers)/((security+2:ℚ)^128)

noncomputable section
open scoped Classical
local instance linearFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





def translationBound (security order : ℕ) : ℝ := 56*(2*(Parameters.modulus security:ℝ)*Parameters.dimension security)^order

def meanErrorConstant (security order : ℕ) : ℝ := RationalBackgroundProgram.translationErrorConstant security+translationBound security order

def linearErrorConstant (security order : ℕ) : ℝ :=
  (ProposalPrimary.freeMass security*RationalBackgroundProgram.freeErrorConstant security+
    (Parameters.modulus security:ℝ)*meanErrorConstant security order)/(Parameters.legCount security:ℝ)

















end
end CurrentAFT.RationalBackgroundLinearProgram

end

section






















/-! # Averaging complete coefficient tables under the one shared scalar -/
namespace CurrentAFT.RationalScalarFamilyAverage
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus

def current (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    ∑ index : Fin (2*RationalBackgroundLinearProgram.cutoff security+1),
      let scalar := FiniteConvolutionProgram.windowIndexEquiv
        (RationalBackgroundLinearProgram.cutoff security) index
      RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
        table scalar.val arity colors centers

noncomputable section
open scoped Classical
local instance scalarAverageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



def actual (security order : ℕ) (families : MarkedPairSeed.Scalar security → ActualFamily security order) :
    ActualFamily security order := ∑ scalar, (scalarLaw security).weight scalar • families scalar







end
end CurrentAFT.RationalScalarFamilyAverage

end

section


























/-! # The original complete leg atom with the shared scalar averaged last -/
namespace CurrentAFT.RationalLegBackgroundProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalPairQuadraticProgram.current RationalConditionalPairProgram.current
  RationalBackgroundProgram.translation RationalFamilyProductProgram.product

def conditionalQuadratic (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalPairQuadraticProgram.current security bits order scalar arity colors centers+
    RationalFamilyProductProgram.product order (RationalConditionalPairProgram.current security bits order scalar)
      (RationalBackgroundProgram.translation security bits order scalar) arity colors centers

def conditionalCubic (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.product order (RationalPairQuadraticProgram.current security bits order scalar)
    (RationalBackgroundProgram.translation security bits order scalar)

def quadratic (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order (conditionalQuadratic security bits order)

def cubic (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order (conditionalCubic security bits order)

def current (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalBackgroundLinearProgram.legLinear security bits order arity colors centers+
    quadratic security bits order arity colors centers+cubic security bits order arity colors centers

noncomputable section
open scoped Classical
local instance legBackgroundFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def conditionalLinearBound (security order : ℕ) : ℝ := coordinateFactor security order*32768
def pairBound (security order : ℕ) : ℝ := coordinateFactor security order*406880
def quadraticBound (security order : ℕ) : ℝ := coordinateFactor security order*2241888
def cubicBound (security order : ℕ) : ℝ := coordinateFactor security order*22785280
def conditionalQuadraticError (security order : ℕ) : ℝ :=
  RationalPairQuadraticProgram.errorConstant security order+
    productError order (conditionalLinearBound security order) (RationalBackgroundLinearProgram.translationBound security order)
      (RationalConditionalPairProgram.errorConstant security) (RationalBackgroundProgram.translationErrorConstant security)
def conditionalCubicError (security order : ℕ) : ℝ :=
  productError order (pairBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalPairQuadraticProgram.errorConstant security order) (RationalBackgroundProgram.translationErrorConstant security)
def errorConstant (security order : ℕ) : ℝ := RationalBackgroundLinearProgram.linearErrorConstant security order+
  (conditionalQuadraticError security order+quadraticBound security order)+
  (conditionalCubicError security order+cubicBound security order)

























end
end CurrentAFT.RationalLegBackgroundProgram

end

section













/-! # Fixed-order error propagation for finite powers and reciprocals -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false





def growth (order : ℕ) (bound error : ℝ) : ℝ :=
  1 + (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1)








end
end CurrentAFT.RationalFamilyProductProgram

end

section













namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram



/-! # Fixed-order population powers of literal approximate coefficient data -/
namespace CurrentAFT.RationalPopulationApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false





def bound (order population : ℕ) (A : ℝ) :=
  ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)*
    (RationalFamilyProductProgram.growth order A 0)^(order+1)

def error (order population : ℕ) (A e : ℝ) :=
  ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)^2*e*
    (RationalFamilyProductProgram.growth order A e)^(order+1)









end
end CurrentAFT.RationalPopulationApproximation

end

section
























/-! # The three actual population products of the original fixed-queue background -/
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies BackgroundScalarZero
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  PublicParameterProgram.modulus ProposalPrimary.primaryLaw bodyReference
  RationalBackgroundProgram.free RationalBackgroundProgram.translation RationalLegBackgroundProgram.current
  RationalFamilyProductProgram.binomial RationalFamilyProductProgram.product

def freeCount (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count*(security+2)^96-
  (security+2)^128-(PublicParameterProgram.modulus security).count
def freeFactor (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (freeCount security) (RationalBackgroundProgram.free security bits order)
def queueFactor (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (PublicParameterProgram.modulus security).count
    (RationalBackgroundProgram.translation security bits order queue)
def legFactor (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order ((security+2)^128) (RationalLegBackgroundProgram.current security bits order)
def current (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.product order
    (RationalFamilyProductProgram.product order (freeFactor security bits order) (queueFactor security bits order queue))
    (legFactor security bits order)

noncomputable section
open scoped Classical
local instance populationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



def freeActual (security order : ℕ) (horder : 2≤order) : ActualFamily security order :=
  (1+freeCertificate security order (by omega))^BackgroundPopulationBounds.freeCount security
def queueActual (security order : ℕ) (horder : 2≤order) (queue : ℤ) : ActualFamily security order :=
  (1+translationCertificate security order (by omega) queue)^Parameters.modulus security
def legActual (security order : ℕ) (horder : 2≤order) : ActualFamily security order :=
  (1+LegBackgroundFamilies.completeLegAtom security order horder)^Parameters.legCount security

def freeBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (BackgroundPopulationBounds.freeCount security) (RationalMarkedPairProgram.freeBound security order)
def queueBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (Parameters.modulus security) (RationalBackgroundLinearProgram.translationBound security order)
def legAtomBound (security order : ℕ) : ℝ := coordinateFactor security order*43377248
def legBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (Parameters.legCount security) (legAtomBound security order)
def freeError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (BackgroundPopulationBounds.freeCount security) (RationalMarkedPairProgram.freeBound security order)
  (RationalBackgroundProgram.freeErrorConstant security)
def queueError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (Parameters.modulus security) (RationalBackgroundLinearProgram.translationBound security order)
  (RationalBackgroundProgram.translationErrorConstant security)
def legError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (Parameters.legCount security) (legAtomBound security order) (RationalLegBackgroundProgram.errorConstant security order)
def freeQueueBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order):ℝ)^2*freeBound security order*queueBound security order
def freeQueueError (security order : ℕ) : ℝ := productError order (freeBound security order) (queueBound security order)
  (freeError security order) (queueError security order)
def errorConstant (security order : ℕ) : ℝ := productError order (freeQueueBound security order) (legBound security order)
  (freeQueueError security order) (legError security order)















end
end CurrentAFT.RationalBackgroundPopulationProgram

end

section






















/-! # Executed current counts for all three actual background populations -/
namespace CurrentAFT.BinaryBackgroundPopulationCounts
open AFT RationalNumerics BinaryArithmetic
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProposalMetadata.counts differenceCounter

structure Counts where
  free : ℕ
  queue : ℕ
  leg : ℕ
  work : ℕ

def current (security : ℕ) : Counts :=
  let sizes := BinaryProposalMetadata.counts security
  let noLegs := differenceCounter sizes.population sizes.legs
  let free := differenceCounter noLegs.count sizes.colors
  ⟨free.count,sizes.colors,sizes.legs,sizes.work+noLegs.work+free.work+3⟩





noncomputable def workPolynomial : Polynomial ℕ := BinaryProposalMetadata.countsWorkPolynomial+4*BinaryProposalMetadata.sizePolynomial+5



end CurrentAFT.BinaryBackgroundPopulationCounts

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundPopulationCounts.workPolynomial
  pure ()

end

section





















/-! # A stable norm on the explicit full calibration table

The exact response is contractive on the decoded coefficient family and
annihilates the redundant part of the table. The norm below records both
parts, with polynomial comparisons to the ordinary coordinate sup norm.
-/
namespace CurrentAFT.CalibrationTableNorm
open AFT ActualControls ProposalPrimary LocalCoefficientFamily BackgroundRates
  CalibrationPointCoordinates CalibrationCoordinateError GradedControlAlgebra
  GradedControlNorm GradedControlStability ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance tableFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Index (security order : ℕ) :=
  PointIndex (ActualControls.Palette security) (SafePalette security) order
abbrev Table (security order : ℕ) := Index security order → ℝ

def encodeCurrent (security order : ℕ) : Family security order →ₗ[ℝ] Table security order :=
  encode (primaryLaw security) (bodyReference security) order
def decodeCurrent (security order : ℕ) : Table security order →ₗ[ℝ] Family security order :=
  decode (primaryLaw security) (bodyReference security) (primaryReference_positive security)
    (bodyReference_positive security) order
def remainder (security order : ℕ) : Module.End ℝ (Table security order) :=
  LinearMap.id - (encodeCurrent security order).comp (decodeCurrent security order)
def measure (security order : ℕ) (table : Table security order) : ℝ :=
  LocalRaisingBounds.coefficientNorm security order (decodeCurrent security order table) +
    ‖remainder security order table‖

def encodeFactor (security order : ℕ) : ℝ :=
  (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order
def decodeFactor (security order : ℕ) : ℝ :=
  (order + 1 : ℕ)^2 * (2 * (Parameters.modulus security : ℝ) + 1)^order
def comparisonFactor (security order : ℕ) : ℝ :=
  1 + (1 + encodeFactor security order) * decodeFactor security order

























def exactDefect (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Module.End ℝ (Table security order) :=
  (encodeCurrent security order).comp
    ((fullResponse security order horder (room security order horder hsecurity) layout - LinearMap.id).comp
      (decodeCurrent security order))







end
end CurrentAFT.CalibrationTableNorm

end

section



















/-! # Stability of rational approximations to the actual calibration matrix

Entrywise approximation is measured against the concrete full response.
The required tolerance and all conversion factors are explicit functions of
the actual finite coordinates, rather than assumed operator norm bounds.
-/
namespace CurrentAFT.CalibrationMatrixApproximation
open AFT ActualControls ProposalPrimary LocalCoefficientFamily BackgroundRates
  CalibrationPointCoordinates CalibrationCoordinateError CalibrationTableNorm
  ActualCompleteStability
open GradedControlAlgebra ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance matrixFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



def perturbationFactor (security order : ℕ) : ℝ :=
  comparisonFactor security order * Fintype.card (Index security order) * (1 + encodeFactor security order)











def rhs (security order : ℕ) (point : Index security order) : ℚ :=
  if point.1 = zeroArity order then 1 else 0








end
end CurrentAFT.CalibrationMatrixApproximation

end

section



















/-! # Polynomial bit work for stored rational calibration iteration

The reused binary program performs every matrix read, multiplication, sum,
and cached vector update. A common denominator for the fixed stored matrix
and right-hand side gives a height bound linear in the iteration count.
These bounds concern the genuine program, not an assumed runtime field.
-/
namespace CurrentAFT.BinaryCalibrationIteration
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open Polynomial

noncomputable def heightPolynomial (count bits steps : Polynomial ℕ) : Polynomial ℕ :=
  steps * ((3 * (count^2 + count) + 1) * bits + count + 1)

noncomputable def primitivePolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 10000000 * (bits + 2)^3

noncomputable def workPolynomial (count bits steps : Polynomial ℕ) : Polynomial ℕ :=
  let B := bits + heightPolynomial count bits steps
  let D := (count + 1) * (2 * B + 1)
  let row := count * (10 * count + 13 + primitivePolynomial B + primitivePolynomial D + 2) + 2
  let step := count * (row + 2) + 2 + count * (6 * count + 13 + 2 * primitivePolynomial D) + 5
  steps * step + 2 * count + 2











end CurrentAFT.BinaryCalibrationIteration

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCalibrationIteration.primitivePolynomial
  pure ()

end

section





















/-! # Derived bit bounds for fixed-order stored arithmetic syntax

Only the fixed calibration order determines this syntax and its encoded
literals. Security-dependent values enter through executed binary leaves.
All intermediate heights are derived from the syntax, not supplied as a
runtime assumption.
-/
namespace CurrentAFT.BinaryFixedScalarProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 600000

variable {Leaf : Type*}

def literalBound : ScalarProgram Leaf → ℕ
  | .rational value => rationalLiteralHeight value
  | .atom _ => 0
  | .add first second => max (literalBound first) (literalBound second)
  | .multiply first second => max (literalBound first) (literalBound second)
  | .negate term => literalBound term
  | .inverse term => literalBound term





def height (program : StoredScalarProgram Leaf RationalBits) (leafBits : ℕ) : ℕ :=
  (program.meaning RationalBits.decode).nodes * (leafBits + literalBound (program.meaning RationalBits.decode) + 1)

def work (program : StoredScalarProgram Leaf RationalBits) (leafBits leafWork : ℕ) : ℕ :=
  (program.meaning RationalBits.decode).nodes * (leafWork + primitiveWorkBound (height program leafBits) + 1)







noncomputable def heightPolynomial (program : StoredScalarProgram Leaf RationalBits)
    (leafBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (program.meaning RationalBits.decode).nodes *
    (leafBits + Polynomial.C (literalBound (program.meaning RationalBits.decode)) + 1)

noncomputable def workPolynomial (program : StoredScalarProgram Leaf RationalBits)
    (leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (program.meaning RationalBits.decode).nodes *
    (leafWork + BinaryCalibrationIteration.primitivePolynomial (heightPolynomial program leafBits) + 1)





end CurrentAFT.BinaryFixedScalarProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFixedScalarProgram.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFixedScalarProgram.workPolynomial
  pure ()

end

section





















/-! # Fixed-order arithmetic syntax for exact joint family multiplication

The syntax and all its rational literals depend only on the fixed order
and output arity. Dynamic palette values enter exclusively through leaf
reads specified by stored slot vectors. No security-dependent literal is
encoded by the interpreter.
-/
namespace CurrentAFT.FamilyProductSyntax
open AFT RationalNumerics GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Leaf (order : ℕ) (output : TruncatedArity order) where
  second : Bool
  arity : TruncatedArity order
  primarySlots : Vector (Fin output.val.1.val) arity.val.1.val
  bodySlots : Vector (Fin output.val.2.val) arity.val.2.val

def value {Primary Body : Type*} (order : ℕ) (output : TruncatedArity order)
    (first second : Table ℚ Primary Body order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) (leaf : Leaf order output) : ℚ :=
  (if leaf.second then second else first) leaf.arity
    (fun index => colors (leaf.primarySlots.get index)) (fun index => centers (leaf.bodySlots.get index))

def sumList {Atom : Type*} : List (ScalarProgram Atom) → ScalarProgram Atom
  | [] => .rational 0
  | first::tail => .add first (sumList tail)



noncomputable section
open scoped Classical

def sum {Index Atom : Type*} [Fintype Index] (term : Index → ScalarProgram Atom) : ScalarProgram Atom :=
  sumList (List.ofFn (fun index : Fin (Fintype.card Index) => term ((Fintype.equivFin Index).symm index)))



def splitLeaf (order : ℕ) (output left right : TruncatedArity order)
    (hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val)
    (primaryOrder : Equiv.Perm (Fin (left.val.1.val+right.val.1.val)))
    (bodyOrder : Equiv.Perm (Fin (left.val.2.val+right.val.2.val))) (useSecond : Bool) : Leaf order output :=
  if useSecond then
    ⟨true, right,
      Vector.ofFn (fun index => finCongr hmatch.1 (primaryOrder (finSumFinEquiv (Sum.inr index)))),
      Vector.ofFn (fun index => finCongr hmatch.2 (bodyOrder (finSumFinEquiv (Sum.inr index))))⟩
  else
    ⟨false, left,
      Vector.ofFn (fun index => finCongr hmatch.1 (primaryOrder (finSumFinEquiv (Sum.inl index)))),
      Vector.ofFn (fun index => finCongr hmatch.2 (bodyOrder (finSumFinEquiv (Sum.inl index))))⟩

def homogeneous (order : ℕ) (output left right : TruncatedArity order)
    (hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val) : ScalarProgram (Leaf order output) :=
  .multiply (.rational (((left.val.1.val+right.val.1.val).factorial : ℚ)⁻¹ *
    ((left.val.2.val+right.val.2.val).factorial : ℚ)⁻¹))
    (sum (fun primaryOrder => sum (fun bodyOrder =>
      .multiply (.atom (splitLeaf order output left right hmatch primaryOrder bodyOrder false))
        (.atom (splitLeaf order output left right hmatch primaryOrder bodyOrder true)))))

def product (order : ℕ) (output : TruncatedArity order) : ScalarProgram (Leaf order output) :=
  sum (fun left : TruncatedArity order => sum (fun right : TruncatedArity order =>
    if hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val then
        homogeneous order output left right hmatch else .rational 0))







end
end CurrentAFT.FamilyProductSyntax

end

section





















/-! # Executed joint-slot gathers and binary coefficient multiplication -/
namespace CurrentAFT.BinaryFamilyProduct
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev CoefficientProgram (order : ℕ) := (arity : TruncatedArity order) →
  Vector ℕ arity.val.1.val → Vector ℕ arity.val.2.val → CountedValue RationalBits

def gatherEntry {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) (storedSlots : Vector ℕ outputCount)
    (hslots : ∀ index, storedSlots.get index = (slots.get index).val) (index : Fin outputCount) : CountedValue ℕ :=
  let position := readVector 0 storedSlots index
  let output := readVector 0 input ⟨position.value, by rw [readVector_value, hslots]; exact (slots.get index).isLt⟩
  ⟨output.value, position.work + output.work + 1⟩

def gather {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) : CountedValue (Vector ℕ outputCount) :=
  let positions := slots.map Fin.val
  let result := storeData outputCount (gatherEntry input slots positions (by intro index; simp [positions]))
  ⟨result.value, result.work + outputCount + 1⟩







def leaf (order : ℕ) (output : TruncatedArity order) (first second : CoefficientProgram order)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (code : FamilyProductSyntax.Leaf order output) : CountedValue RationalBits :=
  let primary := gather colors code.primarySlots
  let body := gather centers code.bodySlots
  let result := (if code.second then second else first) code.arity primary.value body.value
  ⟨result.value, primary.work + body.work + result.work + 3⟩

def run (order : ℕ) (output : TruncatedArity order)
    (stored : StoredScalarProgram (FamilyProductSyntax.Leaf order output) RationalBits)
    (first second : CoefficientProgram order)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val) : CountedValue RationalBits :=
  stored.binaryRun (leaf order output first second colors centers)



noncomputable section
open scoped Classical



def leafWork (order kernelWork : ℕ) : ℕ := 2*order*(6*order+10)+kernelWork+9





end
end CurrentAFT.BinaryFamilyProduct

end

section





















/-! # One finite program list for each fixed calibration order

The list is fixed before the security parameter. Runtime dispatch scans its
stored arity tags using executed counters. Choice occurs only in the proof
that this finite collection of static encoded programs exists.
-/
namespace CurrentAFT.FixedFamilyPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Program (order : ℕ) (arity : TruncatedArity order) :=
  StoredScalarProgram (FamilyProductSyntax.Leaf order arity) RationalBits
abbrev Entry (order : ℕ) := (arity : TruncatedArity order) × Program order arity

def matchArity (order : ℕ) (first second : TruncatedArity order) : CountedValue Bool :=
  let primary := equalCounter first.val.1.val second.val.1.val
  let body := equalCounter first.val.2.val second.val.2.val
  ⟨primary.value && body.value, primary.work+body.work+1⟩

theorem matchArity_value (order : ℕ) (first second : TruncatedArity order) :
    (matchArity order first second).value = true ↔ first = second := by
  simp only [matchArity, Bool.and_eq_true, equalCounter_value]
  constructor
  · intro h
    exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  · intro h
    subst second
    exact ⟨rfl, rfl⟩

theorem matchArity_work (order : ℕ) (first second : TruncatedArity order) :
    (matchArity order first second).work ≤ 12*order+5 := by
  have hp := equalCounter_work first.val.1.val second.val.1.val
  have hb := equalCounter_work first.val.2.val second.val.2.val
  have hf := first.property
  have hs := second.property
  change (equalCounter first.val.1.val second.val.1.val).work +
    (equalCounter first.val.2.val second.val.2.val).work + 1 ≤ _
  omega

def lookup (order : ℕ) (target : TruncatedArity order) : List (Entry order) → CountedValue (Program order target)
  | [] => ⟨.literal zero, 1⟩
  | entry::tail =>
      let equal := matchArity order entry.1 target
      if h : equal.value = true then
        let same := (matchArity_value order entry.1 target).mp h
        ⟨same ▸ entry.2, equal.work+2⟩
      else
        let result := lookup order target tail
        ⟨result.value, equal.work+result.work+2⟩



def nodes {order : ℕ} : List (Entry order) → ℕ
  | [] => 1
  | entry::tail => max (entry.2.meaning RationalBits.decode).nodes (nodes tail)

def literals {order : ℕ} : List (Entry order) → ℕ
  | [] => rationalLiteralHeight zero.decode
  | entry::tail => max (BinaryFixedScalarProgram.literalBound (entry.2.meaning RationalBits.decode)) (literals tail)



noncomputable section
open scoped Classical

def Correct (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ entry ∈ list, entry.2.meaning RationalBits.decode = FamilyProductSyntax.product order entry.1

def Complete (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ arity, ∃ program : Program order arity, (⟨arity, program⟩ : Entry order) ∈ list





end
end CurrentAFT.FixedFamilyPrograms

end

section



















/-! # Uniform fixed-order coefficient programs with derived bit bounds -/
namespace CurrentAFT.BinaryFamilyArithmetic
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra RationalFamilyProductProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- `programs` is a single finite constant list for the fixed order. -/
def multiply (order : ℕ) (programs : List (Entry order)) (first second : CoefficientProgram order) :
    CoefficientProgram order := fun arity colors centers =>
  let selected := lookup order arity programs
  let product := BinaryFamilyProduct.run order arity selected.value first second colors centers
  ⟨product.value, selected.work+product.work+1⟩

def multiplyHeight (order : ℕ) (programs : List (Entry order)) (bits : ℕ) : ℕ :=
  nodes programs * (bits + literals programs + 1)

def multiplyWork (order : ℕ) (programs : List (Entry order)) (bits budget : ℕ) : ℕ :=
  programs.length*(12*order+7)+1 + nodes programs *
    (leafWork order budget + primitiveWorkBound (multiplyHeight order programs bits) + 1) + 1

noncomputable section
open scoped Classical





noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order))
    (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (nodes programs) * (bits + Polynomial.C (literals programs) + 1)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order))
    (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (programs.length*(12*order+7)+1) + Polynomial.C (nodes programs) *
    (Polynomial.C (2*order*(6*order+10)+9) + budget +
      BinaryCalibrationIteration.primitivePolynomial (heightPolynomial order programs bits) + 1) + 1





end
end CurrentAFT.BinaryFamilyArithmetic

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFamilyArithmetic.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFamilyArithmetic.workPolynomial
  pure ()

end

section























/-! # Compiled scalar arithmetic for the actual rank-one mass lift -/
namespace CurrentAFT.BinaryMassLiftFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | input | functional | denominator | sign | activation | primary
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply
    (.add (.atom .input)
      (.negate (.multiply (.multiply (.atom .functional) (.inverse (.atom .denominator))) (.atom .sign))))
    (.inverse (.multiply (.atom .activation) (.atom .primary)))



def leaf (input functional denominator sign activation primary : RationalBits) : Leaf → RationalBits
  | .input => input
  | .functional => functional
  | .denominator => denominator
  | .sign => sign
  | .activation => activation
  | .primary => primary

def read (values : Leaf → RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data, result.work+1⟩

def current (input functional denominator sign activation primary : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf input functional denominator sign activation primary))
  ⟨result.value, result.work+1⟩



def height (bound : ℕ) : ℕ := expression.nodes*(bound+3)
def work (bound : ℕ) : ℕ := expression.nodes*
  (smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2



noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+
    primitiveWorkPolynomial (heightPolynomial bound)+2)+2





end CurrentAFT.BinaryMassLiftFormula

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftFormula.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftFormula.workPolynomial
  pure ()

end

section
























/-! # Executed anchor-sign functional with sequential input reads -/
namespace CurrentAFT.BinaryRankOneFunctional
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter subtractCounter lessCounter

def anchor (count color : ℕ) : RationalResult :=
  let doubled := addCounter color color
  let last := subtractCounter count 1
  let left := lessCounter doubled.count last.count
  let right := lessCounter last.count doubled.count
  let negative := RationalBits.negate one
  ⟨if left.value then negative.data else if right.value then one else zero,
    doubled.work+last.work+left.work+right.work+negative.work+6⟩







def term {count : ℕ} (input : Vector RationalBits count) (color : Fin count) : RationalResult :=
  let coefficient := anchor count color.val
  let value := readVector zero input color
  let result := RationalBits.multiply coefficient.data value.value
  ⟨result.data, coefficient.work+value.work+result.work+3⟩



def current {count : ℕ} (input : Vector RationalBits count) : RationalResult := sumFin count (term input)



def height (count bits : ℕ) := (count+1)*(bits+2)
def work (count bits : ℕ) :=
  count*(33*count+primitiveWorkBound 1+32+primitiveWorkBound (bits+1)+primitiveWorkBound (height count bits))+2







noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ := (count+1)*(bits+2)
noncomputable def workPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(33*count+Polynomial.C (primitiveWorkBound 1)+32+primitiveWorkPolynomial (bits+1)+primitiveWorkPolynomial (heightPolynomial count bits))+2





end CurrentAFT.BinaryRankOneFunctional

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRankOneFunctional.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRankOneFunctional.workPolynomial
  pure ()

end

section




















/-! # Rational guards from actual cross products and signed comparisons -/
namespace CurrentAFT.BinaryRationalCompare
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def le (first second : RationalBits) : CountedValue Bool :=
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  let result := signedLe first.negative second.negative left.digits right.digits
  ⟨result.value, left.work + right.work + result.work + 3⟩

theorem le_value (first second : RationalBits) :
    (le first second).value = true ↔ first.decode ≤ second.decode := by
  have cross (sign : Bool) (top bottom : List Bool) :
      signedValue sign (BinaryArithmetic.multiply top bottom).digits =
        signedValue sign top*(value bottom:ℤ) := by
    cases sign <;> simp [signedValue, BinaryArithmetic.multiply_value]
  simp only [le, signedLe_value, cross]
  rw [decode_fraction, decode_fraction,
    div_le_div_iff₀ (by exact_mod_cast first.denominator_positive) (by exact_mod_cast second.denominator_positive)]
  constructor <;> intro h <;> exact_mod_cast h

def workBound (height : ℕ) : ℕ := 40*(2*height+3)^2+72*(height+1)+21



def maximum (first second : RationalBits) : RationalResult :=
  let test := le first second
  ⟨if test.value then second else first, test.work+3⟩







noncomputable def workPolynomial (height : Polynomial ℕ) : Polynomial ℕ := 40*(2*height+3)^2+72*(height+1)+21


end CurrentAFT.BinaryRationalCompare

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRationalCompare.workPolynomial
  pure ()

end

section



























/-! # Guarded rank-one inversion and mass whitening on stored binary arrays -/
namespace CurrentAFT.BinaryMassLiftKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryRankOneFunctional.current

def prepare {count : ℕ} (sign : Vector RationalBits count) (rate : RationalBits) : RationalResult :=
  let functional := BinaryRankOneFunctional.current sign
  let denominator := RationalBits.add rate functional.data
  let quarter := RationalBits.multiply half half
  let lower := RationalBits.multiply rate quarter.data
  let result := BinaryRationalCompare.maximum denominator.data lower.data
  ⟨result.data, functional.work+denominator.work+quarter.work+lower.work+result.work+6⟩



def prepareHeight (count bits : ℕ) := BinaryRankOneFunctional.height count bits+bits+5
def prepareWork (count bits : ℕ) := BinaryRankOneFunctional.work count bits+
  3*primitiveWorkBound (prepareHeight count bits)+BinaryRationalCompare.workBound (prepareHeight count bits)+9



def current {count : ℕ} (primary sign input : Vector RationalBits count)
    (rate denominator : RationalBits) (output : Fin count) : RationalResult :=
  let functional := BinaryRankOneFunctional.current input
  let point := readVector zero input output
  let direction := readVector zero sign output
  let atom := readVector zero primary output
  let result := BinaryMassLiftFormula.current point.value functional.data denominator direction.value rate atom.value
  ⟨result.data, functional.work+point.work+direction.work+atom.work+result.work+5⟩



def operandHeight (count bits : ℕ) := BinaryRankOneFunctional.height count bits+bits
def height (count bits : ℕ) := BinaryMassLiftFormula.height (operandHeight count bits)
def work (count bits : ℕ) := BinaryRankOneFunctional.work count bits+9*count+14+
  BinaryMassLiftFormula.work (operandHeight count bits)



end CurrentAFT.BinaryMassLiftKernel

end

section


















/-! # One-dimensional Gaussian averages with charged binary lookup and sums -/
namespace CurrentAFT.BinaryWindowAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def term {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult)
    (index : Fin count) : RationalResult :=
  let weight := readVector zero weights index
  let value := kernel index
  let result := RationalBits.multiply weight.value value.data
  ⟨result.data, weight.work + value.work + result.work + 3⟩

theorem term_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) (index : Fin count) :
    (term weights kernel index).data.decode = (weights.get index).decode*(kernel index).data.decode := by
  simp only [term, RationalBits.multiply_value, readVector_value]

def termWork (count gh kh kw : ℕ) : ℕ := 3*count+3+kw+primitiveWorkBound (gh+kh)+3



def sum {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) : RationalResult :=
  sumFin count (term weights kernel)

theorem sum_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) :
    (sum weights kernel).data.decode = ∑ index, (weights.get index).decode*(kernel index).data.decode := by
  simp only [sum, sumFin_value, term_value]

def sumHeight (count gh kh : ℕ) : ℕ := count*(gh+kh+1)
def sumWork (count gh kh kw : ℕ) : ℕ :=
  count*(termWork count gh kh kw+primitiveWorkBound ((count+1)*(gh+kh+1))+2)+2



def evaluate (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → RationalResult) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum weights.data kernel
  ⟨result.data, weights.work + result.work + 2⟩

theorem evaluate_value (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → RationalResult) :
    (evaluate security cutoff bits kernel).data.decode =
      ∑ index, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits index*(kernel index).data.decode := by
  simp only [evaluate, sum_value, CurrentGaussianBits.table_value]

def evaluateWork (security cutoff bits kh kw : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits +
    sumWork (2*cutoff+1) (BinaryGaussianAverage.gaussianHeight security bits) kh kw + 2





noncomputable def termWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  3*count+3+kw+primitiveWorkPolynomial (gh+kh)+3
noncomputable def sumWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  count*(termWorkPolynomial count gh kh kw+primitiveWorkPolynomial ((count+1)*(gh+kh+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) (500000000*((Polynomial.X+2)^2+precision+2)^6) kh kw + 2



end CurrentAFT.BinaryWindowAverage

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWindowAverage.evaluateWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWindowAverage.sumWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWindowAverage.termWorkPolynomial
  pure ()

end

section


























/-! # The actual smoothed anchor table produced by binary arithmetic -/
namespace CurrentAFT.BinaryAnchorProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def coordinate (cutoff index : ℕ) : SignedResult :=
  let first := canonicalCounter index
  let second := canonicalCounter cutoff
  let result := signedAdd false true first.digits second.digits
  ⟨result.negative, result.digits, first.work + second.work + result.work + 3⟩

theorem coordinate_value (cutoff index : ℕ) :
    signedValue (coordinate cutoff index).negative (coordinate cutoff index).digits = (index:ℤ)-cutoff := by
  unfold coordinate
  rw [signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, canonicalCounter_value]
  ring

def coordinateWork (bound : ℕ) : ℕ := 100*(2*bound+1)^2+40*bound+11



def atIndex (colors width primary cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := coordinate cutoff index.val
  let primaryCode := canonicalCounter primary
  let value := BinaryMarkedKernel.average colors width primary 0 0 (!scalar.negative)
    scalar.digits primaryCode.digits output
  ⟨value.data, scalar.work + primaryCode.work + value.work + 3⟩

theorem atIndex_value (colors width primary cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) :
    (atIndex colors width primary cutoff output index).data.decode =
      RationalProposalProgram.anchorKernel colors width primary ((index.val:ℤ)-cutoff) (value output) := by
  unfold atIndex
  rw [BinaryMarkedKernel.average_value, BinaryTrimmedPair.signed_negate, coordinate_value]
  simp only [canonicalCounter_value]
  rfl

def kernelWork (width bound : ℕ) : ℕ := coordinateWork bound + 50*(bound+1)^2 +
  BinaryMarkedKernel.averageWork width (4*bound+10) + 3



def evaluate (security colors width cutoff bits primary : ℕ) (output : List Bool) : RationalResult :=
  BinaryWindowAverage.evaluate security cutoff bits (atIndex colors width primary cutoff output)

theorem evaluate_value (security colors width cutoff bits primary : ℕ) (output : List Bool) :
    (evaluate security colors width cutoff bits primary output).data.decode =
      RationalProposalProgram.anchorEvaluate security colors width cutoff bits primary (value output) := by
  simp only [evaluate, BinaryWindowAverage.evaluate_value, atIndex_value, windowGaussianWeights,
    RationalProposalProgram.anchorEvaluate_eq_window_sum, RationalProposalProgram.gaussianWeight_eq]
  rw [← (windowIndexEquiv cutoff).sum_comp]
  rfl



def current (security bits primary : ℕ) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.colors parameters.width window.count bits primary output
  ⟨result.data, parameters.work + window.work + result.work + 3⟩

theorem current_value (security bits primary : ℕ) (output : List Bool) :
    (current security bits primary output).data.decode = RationalProposalProgram.anchor security bits primary (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, _⟩
  unfold current
  rw [evaluate_value, hq, hw, BinaryActivationProgram.cutoff_value]
  unfold RationalProposalProgram.anchor
  rw [PublicParameterProgram.modulus_value]

noncomputable section
open scoped Classical



noncomputable def coordinateWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(2*bound+1)^2+40*bound+11
noncomputable def kernelWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  coordinateWorkPolynomial bound+50*(bound+1)^2+BinaryMarkedCurrent.averageWorkPolynomial width (4*bound+10)+3



noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    BinaryWindowAverage.evaluateWorkPolynomial ((Polynomial.X+2)^2) precision
      (BinaryMarkedCurrent.averageHeightPolynomial ((Polynomial.X+2)^48))
      (kernelWorkPolynomial ((Polynomial.X+2)^48) (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 3



end
end CurrentAFT.BinaryAnchorProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryAnchorProgram.coordinateWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryAnchorProgram.currentWorkPolynomial
  pure ()

end

section
























/-! # The current diffuse marginal kernel on actual binary operands -/
namespace CurrentAFT.BinaryProfileKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd doubleCounter

def start (width : ℕ) (positive : Bool) : SignedResult :=
  let positiveCode := canonicalCounter width
  let doubled := doubleCounter width
  let negativeCode := canonicalCounter doubled.count
  let negative := signedAdd true false negativeCode.digits [true]
  ⟨if positive then false else negative.negative, if positive then positiveCode.digits else negative.digits,
    positiveCode.work + doubled.work + negativeCode.work + negative.work + 5⟩

theorem start_value (width : ℕ) (positive : Bool) :
    signedValue (start width positive).negative (start width positive).digits =
      if positive then (width:ℤ) else -2*(width:ℤ)+1 := by
  cases positive with
  | false =>
    unfold start
    simp only [Bool.false_eq_true, if_false]
    rw [signedAdd_value]
    simp only [signedValue, if_true, canonicalCounter_value, doubleCounter_value]
    norm_num [value]
  | true => simp only [start, if_true, signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]

def startWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + 3*bound+1 + 50*(2*bound+1)^2 + 20*(2*bound+1)+8 + 5



def current (colors width edgeCutoff scalarCutoff : ℕ) (positive : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let baseline := start width positive
  let blur := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  let shifted := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  let result := binaryAveragedSlice false false shifted.negative source.negative false
    colorCode.digits [true] shifted.digits source.digits output width
  ⟨result.data, baseline.work + blur.work + source.work + shifted.work + colorCode.work + result.work + 6⟩

theorem current_value (colors width edgeCutoff scalarCutoff : ℕ) (positive : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :
    (current colors width edgeCutoff scalarCutoff positive output left right scalar).data.decode =
      RationalFirstResponseProgram.profileKernel colors width positive ((left.val:ℤ)-right.val)
        ((scalar.val:ℤ)-scalarCutoff) (value output) := by
  unfold current
  rw [binaryAveragedSlice_value, signedAdd_value, start_value, BinaryAnchorProgram.coordinate_value,
    BinaryAnchorProgram.coordinate_value]
  simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
  norm_num [value]
  rfl

def integerBound (bound : ℕ) : ℕ := 8*bound+20
def currentHeight (bound : ℕ) : ℕ := integerBound bound*(2*integerBound bound+7)
def currentWork (bound : ℕ) : ℕ := startWork bound + BinaryAnchorProgram.coordinateWork (2*bound) +
  BinaryAnchorProgram.coordinateWork bound + (20*(4*bound+2)+8) + 50*(bound+1)^2 +
    binaryAveragedSliceWork (integerBound bound) + 6



noncomputable def integerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 8*bound+20
noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  integerPolynomial bound*(2*integerPolynomial bound+7)
noncomputable def startWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2 + 3*bound+1 + 50*(2*bound+1)^2 + 20*(2*bound+1)+8+5
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  100*(bits+2)+20*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)
noncomputable def anchorWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  110*(bits+1)^2+40*(bits+1)+16+sliceWorkPolynomial (bits+2)+
    primitiveWorkPolynomial bits+primitiveWorkPolynomial (2*bits+6)+8
noncomputable def averagedWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  bits*(anchorWorkPolynomial bits+primitiveWorkPolynomial ((bits+1)*(2*bits+7))+2)+2
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  startWorkPolynomial bound+BinaryAnchorProgram.coordinateWorkPolynomial (2*bound)+
    BinaryAnchorProgram.coordinateWorkPolynomial bound+(20*(4*bound+2)+8)+50*(bound+1)^2+
      averagedWorkPolynomial (integerPolynomial bound)+6





end CurrentAFT.BinaryProfileKernel

end

section


















/-! # The three actual local Gaussian seeds evaluated by finite binary sums

Only two public blur edges and the one local scalar are averaged. This
does not enumerate the body latent word or an entire public core.
-/
namespace CurrentAFT.BinarySeedAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def evaluate (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) : RationalResult :=
  BinaryWindowAverage.evaluate security scalarCutoff bits (fun scalar =>
    BinaryGaussianAverage.evaluate security edgeCutoff bits (fun left right => kernel left right scalar))

theorem evaluate_value (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) :
    (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode =
      ∑ left, ∑ right, ∑ scalar,
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) edgeCutoff bits left *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) edgeCutoff bits right *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) scalarCutoff bits scalar *
        (kernel left right scalar).data.decode := by
  simp only [evaluate, BinaryWindowAverage.evaluate_value, BinaryGaussianAverage.evaluate_value,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro scalar _
  ring

theorem evaluate_window_value (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) :
    (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) edgeCutoff bits seed.1.1 *
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) edgeCutoff bits seed.1.2 *
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) scalarCutoff bits seed.2 *
        (kernel ((FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).symm seed.1.1)
          ((FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).symm seed.1.2)
          ((FiniteConvolutionProgram.windowIndexEquiv scalarCutoff).symm seed.2)).data.decode := by
  rw [evaluate_value]
  simp only [Fintype.sum_prod_type]
  rw [← (FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro left _
  rw [← (FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro right _
  rw [← (FiniteConvolutionProgram.windowIndexEquiv scalarCutoff).sum_comp]
  simp only [Equiv.symm_apply_apply, windowGaussianWeights]

def innerHeight (security edgeCutoff bits kernelHeight : ℕ) : ℕ :=
  BinaryGaussianAverage.sumHeight (2*edgeCutoff+1) (BinaryGaussianAverage.gaussianHeight security bits) kernelHeight
def outputHeight (security edgeCutoff scalarCutoff bits kernelHeight : ℕ) : ℕ :=
  BinaryWindowAverage.sumHeight (2*scalarCutoff+1) (BinaryGaussianAverage.gaussianHeight security bits)
    (innerHeight security edgeCutoff bits kernelHeight)
def workBound (security edgeCutoff scalarCutoff bits kernelHeight kernelWork : ℕ) : ℕ :=
  BinaryWindowAverage.evaluateWork security scalarCutoff bits (innerHeight security edgeCutoff bits kernelHeight)
    (BinaryGaussianAverage.evaluateWork security edgeCutoff bits kernelHeight kernelWork)





noncomputable def innerHeightPolynomial (edge precision kh : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*edge+1
  count*(count*(2*(500000000*((Polynomial.X+2)^2+precision+2)^6)+kh+1)+1)
noncomputable def workPolynomial (edge scalar precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWindowAverage.evaluateWorkPolynomial scalar precision (innerHeightPolynomial edge precision kh)
    (BinaryGaussianAverage.evaluateWorkPolynomial edge precision kh kw)



end CurrentAFT.BinarySeedAverage

end

section






















/-! # The full current sign-dependent diffuse profile produced on binary data -/
namespace CurrentAFT.BinaryProfileProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def evaluate (security colors width edgeCutoff scalarCutoff bits : ℕ) (positive : Bool) (output : List Bool) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits
    (BinaryProfileKernel.current colors width edgeCutoff scalarCutoff positive output)

theorem evaluate_value (security colors width edgeCutoff scalarCutoff bits : ℕ) (positive : Bool) (output : List Bool) :
    (evaluate security colors width edgeCutoff scalarCutoff bits positive output).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1 *
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2 *
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2 *
        RationalFirstResponseProgram.profileKernel colors width positive (seed.1.1.val-seed.1.2.val) seed.2.val (value output) := by
  rw [evaluate, BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  rw [BinaryProfileKernel.current_value]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff = seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff = seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  have hs : (((windowIndexEquiv scalarCutoff).symm seed.2).val:ℤ)-scalarCutoff = seed.2.val :=
    congrArg Subtype.val ((windowIndexEquiv scalarCutoff).apply_symm_apply seed.2)
  have hblur : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-
      ((windowIndexEquiv edgeCutoff).symm seed.1.2).val = seed.1.1.val-seed.1.2.val := by omega
  rw [hblur, hs]



def current (security bits : ℕ) (positive : Bool) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.colors parameters.width parameters.cutoff window.count bits positive output
  ⟨result.data, parameters.work + window.work + result.work + 3⟩

theorem current_value (security bits : ℕ) (positive : Bool) (output : List Bool) :
    (current security bits positive output).data.decode =
      RationalFirstResponseProgram.profile security bits positive (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  unfold current
  rw [evaluate_value, hq, hw, hc, BinaryActivationProgram.cutoff_value]
  unfold RationalFirstResponseProgram.profile
  rw [RationalProposalProgram.seedEvaluate_eq_window_sum]
  unfold RationalProposalProgram.seedWeight
  rw [PublicParameterProgram.modulus_value]
  have he : ((security+2)^2-1)/2 = DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1 = Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]

noncomputable section
open scoped Classical



noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision
      (BinaryProfileKernel.heightPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits))
      (BinaryProfileKernel.workPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 3

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+BinaryProfileKernel.heightPolynomial
    (BinaryDiffuseCurrent.parameterPolynomial inputBits)+1)+1)+1)





end
end CurrentAFT.BinaryProfileProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileProgram.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileProgram.currentWorkPolynomial
  pure ()

end

section




















/-! # Diffuse mean and sign tables from the same actual binary profiles -/
namespace CurrentAFT.BinaryProfileTables
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def diffuse (security bits : ℕ) (output : List Bool) : RationalResult :=
  let first := BinaryProfileProgram.current security bits true output
  let second := BinaryProfileProgram.current security bits false output
  let total := RationalBits.add first.data second.data
  let result := RationalBits.multiply total.data half
  ⟨result.data, first.work + second.work + total.work + result.work + 4⟩

theorem diffuse_formula (security bits output : ℕ) :
    RationalProposalProgram.diffuse security bits output =
      (RationalFirstResponseProgram.profile security bits true output+
        RationalFirstResponseProgram.profile security bits false output)/2 := by
  simp only [RationalProposalProgram.diffuse, RationalFirstResponseProgram.profile,
    RationalProposalProgram.seedEvaluate_eq_window_sum, RationalProposalProgram.diffuseKernel,
    RationalFirstResponseProgram.profileKernel, if_true, Bool.false_eq_true, if_false,
    mul_div, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem diffuse_value (security bits : ℕ) (output : List Bool) :
    (diffuse security bits output).data.decode = RationalProposalProgram.diffuse security bits (value output) := by
  simp only [diffuse, RationalBits.multiply_value, RationalBits.add_value, half_value,
    BinaryProfileProgram.current_value, diffuse_formula]
  ring

def sign (security bits : ℕ) (output : List Bool) : RationalResult :=
  let rate := BinaryActivationProgram.current security bits
  let first := BinaryProfileProgram.current security bits true output
  let second := BinaryProfileProgram.current security bits false output
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let negativeSecond := RationalBits.negate second.data
  let difference := RationalBits.add first.data negativeSecond.data
  let result := RationalBits.multiply remaining.data difference.data
  ⟨result.data, rate.work + first.work + second.work + negativeRate.work + remaining.work +
    negativeSecond.work + difference.work + result.work + 8⟩



noncomputable section
open scoped Classical





noncomputable def diffuseHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+3
noncomputable def diffuseWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryProfileProgram.currentWorkPolynomial precision inputBits+
    primitiveWorkPolynomial (BinaryProfileProgram.currentHeightPolynomial precision inputBits)+
    primitiveWorkPolynomial (2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+2)+4



noncomputable def signHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentHeightPolynomial precision+
    2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+10
noncomputable def signWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision+2*BinaryProfileProgram.currentWorkPolynomial precision inputBits+
    5*primitiveWorkPolynomial (signHeightPolynomial precision inputBits)+8



end
end CurrentAFT.BinaryProfileTables

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileTables.diffuseHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileTables.diffuseWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileTables.signHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileTables.signWorkPolynomial
  pure ()

end

section
























/-! # The complete current anchor matrix as an executed binary array -/
namespace CurrentAFT.BinaryAnchorTable
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def point (security bits primary output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryAnchorProgram.current security bits primary code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits primary output : ℕ) :
    (point security bits primary output).data.decode = RationalProposalProgram.anchor security bits primary output := by
  simp only [point, BinaryAnchorProgram.current_value, canonicalCounter_value]

def current (security bits : ℕ) : MatrixResult (PublicParameterProgram.modulus security).count :=
  let colors := PublicParameterProgram.modulus security
  let result := buildMatrix colors.count (fun primary output => point security bits primary.val output.val)
  ⟨result.data, colors.work+result.work+2⟩

theorem current_value (security bits : ℕ) (primary output : Fin (PublicParameterProgram.modulus security).count) :
    (((current security bits).data.get primary).get output).decode =
      RationalProposalProgram.anchor security bits primary.val output.val := by
  simp only [current, buildMatrix_get, point_value]



noncomputable section

noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  (2*(Polynomial.X+2)^2+1)*
    (500000000*((Polynomial.X+2)^2+precision+2)^6+4*(Polynomial.X+2)^48+4)



noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := pointHeightPolynomial precision
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let count := BinaryProposalMetadata.sizePolynomial
  let pointWork := 50*(count+1)^2+BinaryAnchorProgram.currentWorkPolynomial precision count+2
  PublicParameterProgram.workPolynomial+count*(count*(pointWork+2)+4)+4



end
end CurrentAFT.BinaryAnchorTable

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryAnchorTable.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryAnchorTable.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryAnchorTable.pointHeightPolynomial
  pure ()

end

section
























/-! # Executed scalar formula for the current center correction -/
namespace CurrentAFT.BinaryCenterFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | colors | legs | population | activation | safe | anchor
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  let colors : ScalarProgram Leaf := .atom .colors
  let legs : ScalarProgram Leaf := .atom .legs
  let population : ScalarProgram Leaf := .atom .population
  let rate : ScalarProgram Leaf := .atom .activation
  let remaining := .add (.add population (.negate legs)) (.negate colors)
  let compensation := .multiply (.multiply legs rate) (.inverse remaining)
  .add (.multiply (.add (.rational 1) compensation) (.atom .safe))
    (.negate (.multiply compensation (.atom .anchor)))



def leaf (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) : Leaf → RationalBits
  | .colors => metadata.colors
  | .legs => metadata.legs
  | .population => metadata.population
  | .activation => rate
  | .safe => safe
  | .anchor => anchor

def read (values : Leaf → RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data, result.work+1⟩

def current (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf metadata rate safe anchor))
  ⟨result.value, result.work+1⟩

theorem current_value (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) :
    (current metadata rate safe anchor).data.decode =
      (1+metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode))*safe.decode-
        metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode)*anchor.decode := by
  simp only [current, ScalarProgram.compileBinaryRun_value, read, RationalBits.copy_value,
    expression, leaf, ScalarProgram.run, div_eq_mul_inv, sub_eq_add_neg]

def height (bound : ℕ) : ℕ := expression.nodes*(bound+3)
def work (bound : ℕ) : ℕ := expression.nodes*
  (smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2



noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+
    primitiveWorkPolynomial (heightPolynomial bound)+2)+2





end CurrentAFT.BinaryCenterFormula

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterFormula.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterFormula.workPolynomial
  pure ()

end

section




























/-! # Center entries from already generated binary reference arrays -/
namespace CurrentAFT.BinaryCenterKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter

def anchorEntry {count : ℕ} (anchor : Vector (Vector RationalBits count) count)
    (output input : Fin count) : RationalResult :=
  let result := matrixEntry anchor input output
  ⟨result.value, result.work+1⟩

theorem anchorEntry_value {count : ℕ} (anchor : Vector (Vector RationalBits count) count)
    (output input : Fin count) :
    (anchorEntry anchor output input).data.decode = ((anchor.get input).get output).decode := by
  simp only [anchorEntry, matrixEntry_value]

def anchorAverage {count : ℕ} (primary : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (output : Fin count) : RationalResult :=
  BinaryWindowAverage.sum primary (anchorEntry anchor output)

theorem anchorAverage_value {count : ℕ} (primary : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (output : Fin count) :
    (anchorAverage primary anchor output).data.decode =
      ∑ input, (primary.get input).decode*((anchor.get input).get output).decode := by
  simp only [anchorAverage, BinaryWindowAverage.sum_value, anchorEntry_value]



def safe (count margin : ℕ) (output : Fin count) : RationalResult :=
  let colors := canonicalCounter count
  let boundary := canonicalCounter margin
  let color := canonicalCounter output.val
  let result := binarySliceProbability false false false false colors.digits boundary.digits [] color.digits
  ⟨result.data, colors.work+boundary.work+color.work+result.work+4⟩

theorem safe_value (count margin : ℕ) (output : Fin count) :
    (safe count margin output).data.decode = AFT.V7Calibration.sliceProbabilityProgram count margin 0 output.val := by
  simp only [safe, binarySliceProbability_value, signedValue, canonicalCounter_value, value, Bool.false_eq_true, if_false, Nat.cast_zero]

def integerBound (count margin : ℕ) : ℕ := count+margin+1



def point {count : ℕ} (margin : ℕ) (metadata : BinaryProposalMetadata.Encoded) (rate : RationalBits)
    (primary : Vector RationalBits count) (anchor : Vector (Vector RationalBits count) count)
    (output : Fin count) : RationalResult :=
  let first := safe count margin output
  let average := anchorAverage primary anchor output
  let result := BinaryCenterFormula.current metadata rate first.data average.data
  ⟨result.data, first.work+average.work+result.work+3⟩

theorem point_value {count : ℕ} (margin : ℕ) (metadata : BinaryProposalMetadata.Encoded) (rate : RationalBits)
    (primary : Vector RationalBits count) (anchor : Vector (Vector RationalBits count) count) (output : Fin count) :
    (point margin metadata rate primary anchor output).data.decode =
      (1+metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode))*
        AFT.V7Calibration.sliceProbabilityProgram count margin 0 output.val-
      metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode)*
        ∑ input, (primary.get input).decode*((anchor.get input).get output).decode := by
  simp only [point, BinaryCenterFormula.current_value, safe_value, anchorAverage_value]

def formulaBound (count margin height : ℕ) : ℕ := height+(integerBound count margin+3)+count*(2*height+1)
def height (count margin bound : ℕ) : ℕ := BinaryCenterFormula.height (formulaBound count margin bound)
def work (count margin bound : ℕ) : ℕ :=
  3*(50*(integerBound count margin+1)^2)+binarySliceProbabilityWork (integerBound count margin)+4+
    BinaryWindowAverage.sumWork count bound bound (7*count+9)+BinaryCenterFormula.work (formulaBound count margin bound)+3



noncomputable def formulaPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  bound+(count+margin+1+3)+count*(2*bound+1)
noncomputable def heightPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCenterFormula.heightPolynomial (formulaPolynomial count margin bound)
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  100*(bits+2)+20*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)

noncomputable def workPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  3*(50*(count+margin+1+1)^2)+sliceWorkPolynomial (count+margin+1)+4+
    BinaryWindowAverage.sumWorkPolynomial count bound bound (7*count+9)+
    BinaryCenterFormula.workPolynomial (formulaPolynomial count margin bound)+3







end CurrentAFT.BinaryCenterKernel

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterKernel.formulaPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterKernel.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterKernel.sliceWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCenterKernel.workPolynomial
  pure ()

end

section























/-! # The translated safe-body kernel with genuine binary residues

The finite palette sum retains the exact modular shift. Every baseline,
residue, comparison and safe-interval probability is computed explicitly.
-/
namespace CurrentAFT.BinaryBodyKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd IntegerBits.residue

def atBaseline {colors : ℕ} (modulus margin : List Bool) (shiftSign : Bool) (shift output : List Bool)
    (baseline : Fin colors) : RationalResult :=
  let color := canonicalCounter baseline.val
  let translated := signedAdd false shiftSign color.digits shift
  let residue := IntegerBits.residue ⟨translated.negative, translated.digits⟩ modulus
  let matched := signedEqual false false residue.digits output
  let probability := binarySliceProbability false false false false modulus margin [] color.digits
  ⟨if matched.value then probability.data else zero,
    color.work + translated.work + residue.work + matched.work + probability.work + 5⟩

theorem atBaseline_value {colors : ℕ} (modulus margin : List Bool) (shiftSign : Bool) (shift output : List Bool)
    (baseline : Fin colors) (hq : 0 < value modulus) :
    (atBaseline modulus margin shiftSign shift output baseline).data.decode =
      if ((baseline.val:ℤ)+signedValue shiftSign shift)%(value modulus:ℤ) = (value output:ℤ)
      then RationalProposalProgram.safeEntry (value modulus) (value margin) baseline.val else 0 := by
  have hres := IntegerBits.residue_value
    (⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
      (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ : IntegerBits) modulus hq
  have hv : (⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
      (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ : IntegerBits).decode =
      (baseline.val:ℤ)+signedValue shiftSign shift := by
    rw [IntegerBits.decode, signedAdd_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
  have hm : (signedEqual false false
      (IntegerBits.residue ⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
        (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ modulus).digits output).value = true ↔
      ((baseline.val:ℤ)+signedValue shiftSign shift)%(value modulus:ℤ) = (value output:ℤ) := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false]
    rw [hres, hv]
    rfl
  unfold atBaseline
  try dsimp only
  simp only [hm]
  split_ifs
  · rw [binarySliceProbability_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
    norm_num [value]
    rfl
  · exact zero_value

def baselineHeight (bound : ℕ) : ℕ := bound+3
def baselineWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + (20*bound+8) + (60*(2*bound+2)^2+10) +
    (48*(2*bound+1)+39) + binarySliceProbabilityWork bound + 5



def translated (colors margin : ℕ) (shiftSign : Bool) (shift output : List Bool) : RationalResult :=
  let modulusCode := canonicalCounter colors
  let marginCode := canonicalCounter margin
  let result := sumFin colors (atBaseline modulusCode.digits marginCode.digits shiftSign shift output)
  ⟨result.data, modulusCode.work + marginCode.work + result.work + 3⟩

theorem translated_value (colors margin : ℕ) (shiftSign : Bool) (shift output : List Bool) (hq : 0 < colors) :
    (translated colors margin shiftSign shift output).data.decode =
      RationalProposalProgram.bodyKernel colors margin (signedValue shiftSign shift) (value output) := by
  simp only [translated, sumFin_value]
  have hcode : 0 < value (canonicalCounter colors).digits := by rw [canonicalCounter_value]; exact hq
  simp_rw [atBaseline_value (canonicalCounter colors).digits (canonicalCounter margin).digits shiftSign shift output _ hcode]
  simp only [canonicalCounter_value]
  rfl

def translatedWork (bound : ℕ) : ℕ := 100*(bound+1)^2 +
  bound*(baselineWork bound+primitiveWorkBound ((bound+1)*(bound+4))+2)+5



noncomputable def sliceWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+2)+20*(bound+2)+11+200*(bound+5)+primitiveWorkPolynomial (bound+3)
noncomputable def baselineWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2+(20*bound+8)+(60*(2*bound+2)^2+10)+(48*(2*bound+1)+39)+sliceWorkPolynomial bound+5
noncomputable def translatedWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+1)^2+bound*(baselineWorkPolynomial bound+primitiveWorkPolynomial ((bound+1)*(bound+4))+2)+5



end CurrentAFT.BinaryBodyKernel

end

section























/-! # The two actual body reference tables produced by binary arithmetic -/
namespace CurrentAFT.BinaryBodyProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signedAdd addCounter multiplyCounter BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def shift (edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : SignedResult :=
  let edge := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  let result := signedAdd edge.negative (if includeScalar then source.negative else false)
    edge.digits (if includeScalar then source.digits else [])
  ⟨result.negative, result.digits, edge.work + source.work + result.work + 3⟩

theorem shift_value (edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :
    signedValue (shift edgeCutoff scalarCutoff includeScalar left right scalar).negative
      (shift edgeCutoff scalarCutoff includeScalar left right scalar).digits =
      (left.val:ℤ)-right.val + if includeScalar then (scalar.val:ℤ)-scalarCutoff else 0 := by
  unfold shift
  rw [signedAdd_value, BinaryAnchorProgram.coordinate_value]
  cases includeScalar with
  | false => rfl
  | true =>
    simp only [if_true]
    rw [BinaryAnchorProgram.coordinate_value]

def shiftWork (bound : ℕ) : ℕ := BinaryAnchorProgram.coordinateWork (2*bound)+
  BinaryAnchorProgram.coordinateWork bound+(20*(4*bound+1)+8)+3



def kernel (colors margin edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let translated := shift edgeCutoff scalarCutoff includeScalar left right scalar
  let result := BinaryBodyKernel.translated colors margin translated.negative translated.digits output
  ⟨result.data, translated.work + result.work + 2⟩

theorem kernel_value (colors margin edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (hq : 0 < colors) :
    (kernel colors margin edgeCutoff scalarCutoff includeScalar output left right scalar).data.decode =
      RationalProposalProgram.bodyKernel colors margin
        ((left.val:ℤ)-right.val+if includeScalar then (scalar.val:ℤ)-scalarCutoff else 0) (value output) := by
  unfold kernel
  rw [BinaryBodyKernel.translated_value _ _ _ _ _ hq, shift_value]

def integerBound (bound : ℕ) : ℕ := 8*bound+20
def kernelHeight (bound : ℕ) : ℕ := integerBound bound*(integerBound bound+4)
def kernelWork (bound : ℕ) : ℕ := shiftWork bound+BinaryBodyKernel.translatedWork (integerBound bound)+2



def evaluate (security colors margin edgeCutoff scalarCutoff bits : ℕ) (includeScalar : Bool) (output : List Bool) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits (kernel colors margin edgeCutoff scalarCutoff includeScalar output)

theorem evaluate_value (security colors margin edgeCutoff scalarCutoff bits : ℕ) (includeScalar : Bool) (output : List Bool)
    (hq : 0 < colors) :
    (evaluate security colors margin edgeCutoff scalarCutoff bits includeScalar output).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1 *
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2 *
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2 *
        RationalProposalProgram.bodyKernel colors margin
          (seed.1.1.val-seed.1.2.val+if includeScalar then seed.2.val else 0) (value output) := by
  rw [evaluate, BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  rw [kernel_value _ _ _ _ _ _ _ _ _ hq]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff = seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff = seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  have hs : (((windowIndexEquiv scalarCutoff).symm seed.2).val:ℤ)-scalarCutoff = seed.2.val :=
    congrArg Subtype.val ((windowIndexEquiv scalarCutoff).apply_symm_apply seed.2)
  have hblur : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-
      ((windowIndexEquiv edgeCutoff).symm seed.1.2).val = seed.1.1.val-seed.1.2.val := by omega
  rw [hblur, hs]



def current (security bits : ℕ) (includeScalar : Bool) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let result := evaluate security parameters.colors margin.count parameters.cutoff window.count bits includeScalar output
  ⟨result.data, parameters.work + window.work + square.work + margin.work + result.work + 5⟩

theorem margin_value (security : ℕ) :
    (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count = 3*(security+2)^2 := by
  rw [multiplyCounter_value, addCounter_value, BinaryActivationProgram.cutoff_value, Nat.sub_add_cancel]
  have hb : 0 < (security+2)^2 := by positivity
  omega

theorem current_value (security bits : ℕ) (includeScalar : Bool) (output : List Bool) :
    (current security bits includeScalar output).data.decode = RationalProposalProgram.body security bits includeScalar (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, _, hc⟩
  have hp : 0 < (BinaryDiffuseCurrent.metadata security).colors := by rw [hq]; exact (Parameters.modulus_spec security).2.pos
  unfold current
  rw [evaluate_value _ _ _ _ _ _ _ _ hp, hq, hc, margin_value, BinaryActivationProgram.cutoff_value]
  unfold RationalProposalProgram.body
  rw [RationalProposalProgram.seedEvaluate_eq_window_sum]
  unfold RationalProposalProgram.seedWeight
  rw [PublicParameterProgram.modulus_value]
  have he : ((security+2)^2-1)/2 = DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1 = Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]

noncomputable section
open scoped Classical



noncomputable def integerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 8*bound+20
noncomputable def kernelHeightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := integerPolynomial bound*(integerPolynomial bound+4)
noncomputable def shiftWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryAnchorProgram.coordinateWorkPolynomial (2*bound)+BinaryAnchorProgram.coordinateWorkPolynomial bound+(20*(4*bound+1)+8)+3
noncomputable def kernelWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  shiftWorkPolynomial bound+BinaryBodyKernel.translatedWorkPolynomial (integerPolynomial bound)+2





noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.parameterPolynomial inputBits+2*(Polynomial.X+2)^2

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial + (2*(Polynomial.X+2)^2+1) +
    (3*(2*(Polynomial.X+2)^2+3)+1) + BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2)
      precision (kernelHeightPolynomial (parameterPolynomial inputBits)) (kernelWorkPolynomial (parameterPolynomial inputBits)) + 5

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+kernelHeightPolynomial (parameterPolynomial inputBits)+1)+1)+1)





end
end CurrentAFT.BinaryBodyProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBodyProgram.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBodyProgram.currentWorkPolynomial
  pure ()

end

section






























/-! # Binary evaluation of the actual primary balancing formula

Every security-dependent input is generated by the local programs.  The
remaining scalar syntax is fixed and has only the literals one and two.
-/
namespace CurrentAFT.BinaryPrimaryRaw
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | colors | legs | population | activation | bodyZero | bodyOne | diffuse
  deriving DecidableEq

structure Cache where
  metadata : BinaryProposalMetadata.Encoded
  activation : RationalBits
  bodyZero : RationalBits
  bodyOne : RationalBits
  diffuse : RationalBits
  work : ℕ

def cache (security bits : ℕ) (output : List Bool) : Cache :=
  let metadata := BinaryProposalMetadata.current security
  let activation := BinaryActivationProgram.current security bits
  let bodyZero := BinaryBodyProgram.current security bits false output
  let bodyOne := BinaryBodyProgram.current security bits true output
  let diffuse := BinaryProfileTables.diffuse security bits output
  ⟨metadata, activation.data, bodyZero.data, bodyOne.data, diffuse.data,
    metadata.work+activation.work+bodyZero.work+bodyOne.work+diffuse.work+5⟩

def Cache.entry (data : Cache) : Leaf → RationalBits
  | .colors => data.metadata.colors
  | .legs => data.metadata.legs
  | .population => data.metadata.population
  | .activation => data.activation
  | .bodyZero => data.bodyZero
  | .bodyOne => data.bodyOne
  | .diffuse => data.diffuse

def Cache.read (data : Cache) (leaf : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (data.entry leaf)
  ⟨result.data, result.work+1⟩

def expression : ScalarProgram Leaf :=
  let q : ScalarProgram Leaf := .atom .colors
  let legs : ScalarProgram Leaf := .atom .legs
  let population : ScalarProgram Leaf := .atom .population
  let rate : ScalarProgram Leaf := .atom .activation
  let two : ScalarProgram Leaf := .rational 2
  let one : ScalarProgram Leaf := .rational 1
  let free := .add (.add population (.negate legs)) (.negate q)
  let marked := .multiply legs rate
  let uniform := .multiply (.add population (.multiply two legs)) (.inverse q)
  let bodyZero := .multiply (.add free marked) (.atom .bodyZero)
  let bodyOne := .multiply (.add legs q) (.atom .bodyOne)
  let diffuse := .multiply (.multiply (.multiply two legs) (.add one (.negate rate))) (.atom .diffuse)
  .multiply (.add (.add (.add uniform (.negate bodyZero)) (.negate bodyOne)) (.negate diffuse)) (.inverse marked)



theorem expression_value (leaf : Leaf → ℚ) :
    expression.run leaf =
      ((leaf .population+2*leaf .legs)/leaf .colors-
        (leaf .population-leaf .legs-leaf .colors+leaf .legs*leaf .activation)*leaf .bodyZero-
        (leaf .legs+leaf .colors)*leaf .bodyOne-
        2*leaf .legs*(1-leaf .activation)*leaf .diffuse)/(leaf .legs*leaf .activation) := by
  simp only [expression, ScalarProgram.run, sub_eq_add_neg, div_eq_mul_inv]

def current (security bits : ℕ) (output : List Bool) : RationalResult :=
  let data := cache security bits output
  let result := expression.compileBinaryRun data.read
  ⟨result.value, data.work+result.work+2⟩

theorem current_value (security bits : ℕ) (output : List Bool) :
    (current security bits output).data.decode = RationalProposalProgram.primaryRaw security bits (value output) := by
  rcases BinaryProposalMetadata.current_value security with ⟨hq, hl, hp⟩
  unfold current
  rw [ScalarProgram.compileBinaryRun_value, expression_value]
  simp only [Cache.read, RationalBits.copy_value, Cache.entry, cache,
    BinaryActivationProgram.current_value, BinaryBodyProgram.current_value,
    BinaryProfileTables.diffuse_value, hq, hl, hp]
  unfold RationalProposalProgram.primaryRaw
  rw [PublicParameterProgram.modulus_value]
  push_cast
  rfl

noncomputable section

noncomputable def leafHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryActivationProgram.currentHeightPolynomial precision+
    BinaryBodyProgram.currentHeightPolynomial precision inputBits+
    BinaryProfileTables.diffuseHeightPolynomial precision inputBits+1

noncomputable def cacheWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.currentWorkPolynomial+BinaryActivationProgram.currentWorkPolynomial precision+
    2*BinaryBodyProgram.currentWorkPolynomial precision inputBits+
    BinaryProfileTables.diffuseWorkPolynomial precision inputBits+5

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(leafHeightPolynomial precision inputBits+5)

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  cacheWorkPolynomial precision inputBits+
    ScalarProgram.compilationWorkPolynomial (Polynomial.C expression.nodes) 2
      (leafHeightPolynomial precision inputBits) (4*leafHeightPolynomial precision inputBits+9)+2





end
end CurrentAFT.BinaryPrimaryRaw

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryRaw.cacheWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryRaw.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryRaw.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryRaw.leafHeightPolynomial
  pure ()

end

section





















/-! # The proposal's full palette guard on stored binary entries

This executes every rational lower comparison and the uniform fallback.
The separate raw-table producer must still supply its actual binary data;
the theorem here does not postulate a cost for producing that table.
-/
namespace CurrentAFT.BinaryProposalGuard
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def allFin : (count : ℕ) → (Fin count → CountedValue Bool) → CountedValue Bool
  | 0, _ => ⟨true, 1⟩
  | count+1, test =>
    let previous := allFin count (fun index => test index.castSucc)
    let current := test (Fin.last count)
    ⟨previous.value && current.value, previous.work + current.work + 2⟩

theorem allFin_value (count : ℕ) (test : Fin count → CountedValue Bool) :
    (allFin count test).value = true ↔ ∀ index, (test index).value = true := by
  induction count with
  | zero => simp [allFin]
  | succ count ih =>
    simp only [allFin, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hprevious, hlast⟩ index
      exact Fin.lastCases hlast hprevious index
    · intro hall
      exact ⟨fun index => hall index.castSucc, hall (Fin.last count)⟩



def lowerCheck {count : ℕ} (threshold : RationalBits) (values : Vector RationalBits count) : CountedValue Bool :=
  allFin count (fun index =>
    let found := readVector zero values index
    let checked := BinaryRationalCompare.le threshold found.value
    ⟨checked.value, found.work + checked.work + 2⟩)

theorem lowerCheck_value {count : ℕ} (threshold : RationalBits) (values : Vector RationalBits count) :
    (lowerCheck threshold values).value = true ↔ ∀ index, threshold.decode ≤ (values.get index).decode := by
  simp only [lowerCheck, allFin_value, BinaryRationalCompare.le_value, readVector_value]

def lowerCheckWork (count height : ℕ) : ℕ := count*(3*count+BinaryRationalCompare.workBound height+7)+1



def uniformTable (count : ℕ) : ArrayResult count :=
  let denominator := ofCounter count
  let atom := RationalBits.inverse denominator.data
  let values := buildArray count (fun _ => ⟨atom.data, 1⟩)
  ⟨values.data, denominator.work + atom.work + values.work + 3⟩

theorem uniformTable_value (count : ℕ) (index : Fin count) :
    ((uniformTable count).data.get index).decode = (count:ℚ)⁻¹ := by
  simp only [uniformTable, buildArray_get, RationalBits.inverse_value, ofCounter_value]

def uniformWork (count : ℕ) : ℕ := 60*(count+1)^2+primitiveWorkBound count+3*count+5



def guardedTable {count : ℕ} (threshold : RationalBits) (raw : Vector RationalBits count) : ArrayResult count :=
  let checked := lowerCheck threshold raw
  let values := if checked.value then ⟨raw, 1⟩ else uniformTable count
  ⟨values.data, checked.work + values.work + 3⟩

theorem guardedTable_value {count : ℕ} (threshold : RationalBits) (raw : Vector RationalBits count) (index : Fin count) :
    ((guardedTable threshold raw).data.get index).decode =
      if ∀ position, threshold.decode ≤ (raw.get position).decode then (raw.get index).decode else (count:ℚ)⁻¹ := by
  unfold guardedTable
  try dsimp only
  simp only [lowerCheck_value]
  split_ifs <;> simp only [uniformTable_value]



def threshold (count : ℕ) : RationalResult :=
  let fourfold := multiplyCounter 4 count
  let encoded := ofCounter fourfold.count
  let result := RationalBits.inverse encoded.data
  ⟨result.data, fourfold.work + encoded.work + result.work + 3⟩

theorem threshold_value (count : ℕ) : (threshold count).data.decode = 1/(4*(count:ℚ)) := by
  simp only [threshold, RationalBits.inverse_value, ofCounter_value, multiplyCounter_value, Nat.cast_mul, Nat.cast_ofNat, one_div]



def thresholdWork (count : ℕ) : ℕ := (4*(2*count+3)+1) + 60*(4*count+1)^2+primitiveWorkBound (4*count)+3



def primary {count : ℕ} (raw : Vector RationalBits count) : ArrayResult count :=
  let lower := threshold count
  let guarded := guardedTable lower.data raw
  ⟨guarded.data, lower.work + guarded.work + 2⟩

theorem primary_value (security bits : ℕ)
    (raw : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (hraw : ∀ index, (raw.get index).decode = RationalProposalProgram.primaryRaw security bits index.val)
    (index : Fin (PublicParameterProgram.modulus security).count) :
    ((primary raw).data.get index).decode = RationalProposalProgram.primary security bits index.val := by
  simp only [primary, guardedTable_value, threshold_value]
  simp_rw [hraw]
  unfold RationalProposalProgram.primary RationalProposalProgram.primaryGood
  split_ifs <;> simp only [one_div]



end CurrentAFT.BinaryProposalGuard

end

section


























/-! # The full binary primary proposal table

The raw entries, lower guard and uniform fallback are all executed.  The
index loop is over the computed current prime and not over a hidden seed.
-/
namespace CurrentAFT.BinaryPrimaryTable
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter PublicParameterProgram.modulus

def point (security bits output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryPrimaryRaw.current security bits code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits output : ℕ) :
    (point security bits output).data.decode = RationalProposalProgram.primaryRaw security bits output := by
  simp only [point, BinaryPrimaryRaw.current_value, canonicalCounter_value]

def raw (security bits : ℕ) : ArrayResult (PublicParameterProgram.modulus security).count :=
  let colors := PublicParameterProgram.modulus security
  let values := buildArray colors.count (fun index => point security bits index.val)
  ⟨values.data, colors.work+values.work+2⟩

theorem raw_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((raw security bits).data.get index).decode = RationalProposalProgram.primaryRaw security bits index.val := by
  simp only [raw, buildArray_get, point_value]

def current (security bits : ℕ) : ArrayResult (PublicParameterProgram.modulus security).count :=
  let values := raw security bits
  let guarded := BinaryProposalGuard.primary values.data
  ⟨guarded.data, values.work+guarded.work+2⟩

theorem current_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).data.get index).decode = RationalProposalProgram.primary security bits index.val := by
  exact BinaryProposalGuard.primary_value security bits (raw security bits).data (raw_value security bits) index



noncomputable section

noncomputable def countPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
noncomputable def rawHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryRaw.currentHeightPolynomial precision countPolynomial
noncomputable def rawWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    countPolynomial*(50*(countPolynomial+1)^2+BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial+4)+4

noncomputable def guardWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  (4*(2*count+3)+1)+60*(4*count+1)^2+primitiveWorkPolynomial (4*count)+3+
  (count*(3*count+BinaryRationalCompare.workPolynomial (4*count+height)+7)+1)+
  (60*(count+1)^2+primitiveWorkPolynomial count+3*count+5)+6

noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := rawHeightPolynomial precision+countPolynomial
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  rawWorkPolynomial precision+guardWorkPolynomial countPolynomial (rawHeightPolynomial precision)+2









end
end CurrentAFT.BinaryPrimaryTable

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryTable.countPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryTable.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryTable.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryTable.guardWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryTable.rawWorkPolynomial
  pure ()

end

section




























/-! # Generated binary caches for all current reference probabilities

The center table reuses the very same primary table, anchor matrix and
activation entry that are returned to the paired-score evaluator.
-/
namespace CurrentAFT.BinaryReferenceTables
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter PublicParameterProgram.modulus BinaryActivationProgram.cutoff

structure Result (security : ℕ) where
  primary : Vector RationalBits (PublicParameterProgram.modulus security).count
  center : Vector RationalBits (PublicParameterProgram.modulus security).count
  anchor : Vector (Vector RationalBits (PublicParameterProgram.modulus security).count) (PublicParameterProgram.modulus security).count
  activation : RationalBits
  work : ℕ

def current (security bits : ℕ) : Result security :=
  let primary := BinaryPrimaryTable.current security bits
  let anchor := BinaryAnchorTable.current security bits
  let metadata := BinaryProposalMetadata.current security
  let activation := BinaryActivationProgram.current security bits
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let center := buildArray (PublicParameterProgram.modulus security).count
    (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data)
  ⟨primary.data, center.data, anchor.data, activation.data,
    primary.work+anchor.work+metadata.work+activation.work+window.work+square.work+margin.work+center.work+8⟩

theorem primary_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).primary.get index).decode = RationalProposalProgram.primary security bits index.val :=
  BinaryPrimaryTable.current_value security bits index



theorem activation_value (security bits : ℕ) :
    (current security bits).activation.decode = LocalPairProgram.activationApprox security bits :=
  BinaryActivationProgram.current_value security bits

theorem center_value (security bits : ℕ) (output : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).center.get output).decode = RationalProposalProgram.center security bits output.val := by
  have hc : (BinaryProposalMetadata.current security).colors.decode = ((PublicParameterProgram.modulus security).count:ℚ) := by
    rw [PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.current_value security).1
  have hl := (BinaryProposalMetadata.current_value security).2.1
  have hp : (BinaryProposalMetadata.current security).population.decode =
      ((PublicParameterProgram.modulus security).count*(security+2)^96:ℕ) := by
    rw [PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.current_value security).2.2
  change ((buildArray (PublicParameterProgram.modulus security).count
    (BinaryCenterKernel.point (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count
      (BinaryProposalMetadata.current security) (BinaryActivationProgram.current security bits).data
      (BinaryPrimaryTable.current security bits).data (BinaryAnchorTable.current security bits).data)).data.get output).decode = _
  rw [buildArray_get, BinaryCenterKernel.point_value, BinaryBodyProgram.margin_value, hc, hl, hp,
    BinaryActivationProgram.current_value]
  simp_rw [BinaryPrimaryTable.current_value, BinaryAnchorTable.current_value]
  unfold RationalProposalProgram.center RationalProposalProgram.compensationApprox
    RationalProposalProgram.anchorPrimary RationalProposalProgram.safeEntry
  push_cast
  generalize ((security : ℚ)+2)^128 = legs
  generalize ((security : ℚ)+2)^96 = factor
  ring

noncomputable section

noncomputable def referenceHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryPrimaryTable.currentHeightPolynomial precision+
    BinaryAnchorTable.currentHeightPolynomial precision+BinaryActivationProgram.currentHeightPolynomial precision+1
noncomputable def marginPolynomial : Polynomial ℕ := 3*(Polynomial.X+2)^2
noncomputable def centerHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCenterKernel.heightPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  referenceHeightPolynomial precision+centerHeightPolynomial precision
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryTable.currentWorkPolynomial precision+BinaryAnchorTable.currentWorkPolynomial precision+
    BinaryProposalMetadata.currentWorkPolynomial+BinaryActivationProgram.currentWorkPolynomial precision+
    BinaryActivationProgram.cutoffWorkPolynomial+(2*(Polynomial.X+2)^2+1)+(3*(2*(Polynomial.X+2)^2+3)+1)+
    BinaryProposalMetadata.sizePolynomial*
      (BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)+2)+10





end
end CurrentAFT.BinaryReferenceTables

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryReferenceTables.centerHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryReferenceTables.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryReferenceTables.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryReferenceTables.marginPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryReferenceTables.referenceHeightPolynomial
  pure ()

end

section






























/-! # Generated current sign tables and literal binary mass-lift evaluation -/
namespace CurrentAFT.BinaryFirstInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryProfileTables.sign
  BinaryMassLiftKernel.prepare BinaryMassLiftKernel.current BinaryReferenceTables.current

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def signPoint (security bits output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryProfileTables.sign security bits code.digits
  ⟨result.data, code.work+result.work+2⟩



structure Cache (security : ℕ) where
  sign : Vector RationalBits (colors security)
  denominator : RationalBits
  work : ℕ

def prepare (security bits : ℕ) : Cache security :=
  let modulus := PublicParameterProgram.modulus security
  let sign := buildArray modulus.count (fun output => signPoint security bits output.val)
  let rate := BinaryActivationProgram.current security bits
  let denominator := BinaryMassLiftKernel.prepare sign.data rate.data
  ⟨sign.data, denominator.data, modulus.work+sign.work+rate.work+denominator.work+4⟩





def inputAt (security : ℕ) (input : Vector RationalBits (colors security)) (output : ℕ) : ℚ :=
  if h : output<colors security then (input.get ⟨output,h⟩).decode else 0



def current (security bits : ℕ) (input : Vector RationalBits (colors security)) (output : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let inverse := prepare security bits
  let result := BinaryMassLiftKernel.current references.primary inverse.sign input references.activation inverse.denominator output
  ⟨result.data, references.work+inverse.work+result.work+3⟩



noncomputable section
open scoped Classical

noncomputable def colorsPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
noncomputable def signHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileTables.signHeightPolynomial precision colorsPolynomial
noncomputable def signWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(colorsPolynomial+1)^2+BinaryProfileTables.signWorkPolynomial precision colorsPolynomial+2





end
end CurrentAFT.BinaryFirstInverseProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.colorsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.signWorkPolynomial
  pure ()

end

section























/-! # Polynomial resources for the executed guarded mass lift -/
namespace CurrentAFT.BinaryMassLiftKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000









noncomputable def prepareHeightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.heightPolynomial count bits+bits+5
noncomputable def prepareWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.workPolynomial count bits+3*primitiveWorkPolynomial (prepareHeightPolynomial count bits)+
    BinaryRationalCompare.workPolynomial (prepareHeightPolynomial count bits)+9
noncomputable def operandHeightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.heightPolynomial count bits+bits
noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftFormula.heightPolynomial (operandHeightPolynomial count bits)
noncomputable def workPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.workPolynomial count bits+9*count+14+
    BinaryMassLiftFormula.workPolynomial (operandHeightPolynomial count bits)











end CurrentAFT.BinaryMassLiftKernel

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftKernel.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftKernel.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftKernel.prepareHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftKernel.prepareWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftKernel.workPolynomial
  pure ()

end

section


























/-! # Closed current-parameter resource bounds for the mass-lift producer -/
namespace CurrentAFT.BinaryFirstInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus prepare BinaryReferenceTables.current
  BinaryMassLiftKernel.current BinaryMassLiftKernel.prepare
  BinaryMassLiftFormula.current BinaryRankOneFunctional.current
noncomputable section

noncomputable def cacheInputHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  signHeightPolynomial precision+BinaryActivationProgram.currentHeightPolynomial precision
noncomputable def cacheHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftKernel.prepareHeightPolynomial colorsPolynomial (cacheInputHeightPolynomial precision)+cacheInputHeightPolynomial precision
noncomputable def cacheWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+colorsPolynomial*(signWorkPolynomial precision+2)+2+
    BinaryActivationProgram.currentWorkPolynomial precision+
    BinaryMassLiftKernel.prepareWorkPolynomial colorsPolynomial (cacheInputHeightPolynomial precision)+4



noncomputable def inputHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  cacheHeightPolynomial precision+BinaryReferenceTables.heightPolynomial precision+inputBits
noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftKernel.heightPolynomial colorsPolynomial (inputHeightPolynomial precision inputBits)
noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+cacheWorkPolynomial precision+
    BinaryMassLiftKernel.workPolynomial colorsPolynomial (inputHeightPolynomial precision inputBits)+3



end
end CurrentAFT.BinaryFirstInverseProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.cacheHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.cacheInputHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.cacheWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.currentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFirstInverseProgram.inputHeightPolynomial
  pure ()

end

section
























/-! # Materializing every profile entry before the actual binary mass lift -/
namespace CurrentAFT.BinaryMassLiftInput
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFirstInverseProgram.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security



def current (security bits : ℕ) (profile : Fin (colors security) → RationalResult) (output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let input := buildArray modulus.count profile
  let result := BinaryFirstInverseProgram.current security bits input.data output
  ⟨result.data, modulus.work+input.work+result.work+4⟩



noncomputable section
noncomputable def heightPolynomial (precision profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.currentHeightPolynomial precision profileBits
noncomputable def workPolynomial (precision profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryFirstInverseProgram.currentWorkPolynomial precision profileBits+4



end
end CurrentAFT.BinaryMassLiftInput

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftInput.workPolynomial
  pure ()

end

section
























/-! # A binary-key lookup by a charged complete palette scan -/
namespace CurrentAFT.BinaryPaletteLookup
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedEqual

def term {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (color : Fin count) : RationalResult :=
  let code := canonicalCounter color.val
  let matched := signedEqual false false code.digits key
  let atom := readVector zero table color
  ⟨if matched.value then atom.value else zero, code.work+matched.work+atom.work+3⟩



def current {count : ℕ} (table : Vector RationalBits count) (key : List Bool) : RationalResult := sumFin count (term table key)



def termWork (count keyBits : ℕ) : ℕ := 50*(count+1)^2+48*(count+keyBits)+42+3*count+3
def work (count keyBits bits : ℕ) : ℕ :=
  count*(termWork count keyBits+primitiveWorkBound ((count+1)*(bits+1))+2)+2







end CurrentAFT.BinaryPaletteLookup

end

section


























/-! # A root difference acts on a stored profile through an actual binary residue -/
namespace CurrentAFT.BinaryRootConvolutionKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegerBits.residue signedAdd BinaryBodyProgram.shift BinaryPaletteLookup.current

def key (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : Result :=
  let root := BinaryBodyProgram.shift edgeCutoff scalarCutoff false left right scalar
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative, difference.digits⟩ modulus
  ⟨residue.digits, root.work+difference.work+residue.work+3⟩



def profile {count : ℕ} (table : Vector RationalBits count) (output : ℕ) : ℚ :=
  if h : output<count then (table.get ⟨output,h⟩).decode else 0

def current {count : ℕ} (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (table : Vector RationalBits count)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let index := key edgeCutoff scalarCutoff modulus output left right scalar
  let result := BinaryPaletteLookup.current table index.digits
  ⟨result.data, index.work+result.work+2⟩



def keyBits (bound : ℕ) := 5*bound+3
def keyWork (bound : ℕ) := BinaryBodyProgram.shiftWork bound+(100*bound+48)+60*(5*bound+4)^2+10+3



def work (count bound bits : ℕ) := keyWork bound+BinaryPaletteLookup.work count (keyBits bound) bits+2



end CurrentAFT.BinaryRootConvolutionKernel

end

section


























/-! # The current Gaussian root convolution executed on an explicit profile array -/
namespace CurrentAFT.BinaryRootConvolution
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff
  BinaryRootConvolutionKernel.current

def evaluate (security count edgeCutoff scalarCutoff bits : ℕ) (table : Vector RationalBits count)
    (output : List Bool) : RationalResult :=
  let modulus := canonicalCounter count
  let result := BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits
    (BinaryRootConvolutionKernel.current edgeCutoff scalarCutoff modulus.digits output table)
  ⟨result.data, modulus.work+result.work+2⟩



def current (security bits : ℕ) (table : Vector RationalBits (BinaryFirstInverseProgram.colors security))
    (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let modulus := PublicParameterProgram.modulus security
  let result := evaluate security modulus.count parameters.cutoff window.count bits table output
  ⟨result.data, parameters.work+window.work+modulus.work+result.work+4⟩



end CurrentAFT.BinaryRootConvolution

end

section
























/-! # Complete current-parameter resources for the root convolution -/
namespace CurrentAFT.BinaryRootConvolution
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff
  evaluate BinaryRootConvolutionKernel.current BinaryPaletteLookup.current





noncomputable section
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+(Polynomial.X+2)^2+inputBits
noncomputable def kernelHeightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(profileBits+1)
noncomputable def keyWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBodyProgram.shiftWorkPolynomial bound+100*bound+48+60*(5*bound+4)^2+13
noncomputable def kernelWorkPolynomial (bound profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let key := 5*bound+3
  keyWorkPolynomial bound+Q*(50*(Q+1)^2+48*(Q+key)+42+3*Q+3+
    primitiveWorkPolynomial ((Q+1)*(profileBits+1))+2)+2+2
noncomputable def heightPolynomial (precision _inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+kernelHeightPolynomial profileBits+1)+1)+1)
noncomputable def workPolynomial (precision inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+BinaryActivationProgram.cutoffWorkPolynomial+PublicParameterProgram.workPolynomial+
    50*(parameterPolynomial inputBits+1)^2+
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision
      (kernelHeightPolynomial profileBits) (kernelWorkPolynomial (parameterPolynomial inputBits) profileBits)+6







end
end CurrentAFT.BinaryRootConvolution

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootConvolution.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootConvolution.workPolynomial
  pure ()

end

section


























/-! # Actual public margin and safe-law atom on binary operands -/
namespace CurrentAFT.BinarySafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus addCounter multiplyCounter powerCounter

def margin (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let result := multiplyCounter 3 square.count
  ⟨result.count, base.work+square.work+result.work+3⟩



def marginWork (security : ℕ) := 2*security+1+powerCounterWork (security+2) 2+3*(2*(security+2)^2+3)+1+3



def current (security : ℕ) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let safeMargin := margin security
  let modulusCode := canonicalCounter modulus.count
  let marginCode := canonicalCounter safeMargin.count
  let result := binarySliceProbability false false false false modulusCode.digits marginCode.digits [] output
  ⟨result.data, modulus.work+safeMargin.work+modulusCode.work+marginCode.work+result.work+5⟩



noncomputable section
noncomputable def marginWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1+3*(6*(Polynomial.X+3)^4+4)+3*(2*(Polynomial.X+2)^2+3)+1+3
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+inputBits
noncomputable def heightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ := parameterPolynomial inputBits+3
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  120*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+marginWorkPolynomial+100*(parameterPolynomial inputBits+1)^2+
    sliceWorkPolynomial (parameterPolynomial inputBits)+5







end
end CurrentAFT.BinarySafeProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinarySafeProfile.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinarySafeProfile.workPolynomial
  pure ()

end

section
























/-! # Actual shifted unsafe profile with binary interval tests -/
namespace CurrentAFT.BinaryUnsafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus signedAdd signedLe BinaryBodyKernel.translated

def membership (modulus margin output : List Bool) : CountedValue Bool :=
  let lower := signedLe false false margin output
  let upper := signedAdd false true modulus margin
  let last := signedLe upper.negative false upper.digits output
  ⟨lower.value && !last.value, lower.work+upper.work+last.work+4⟩





def kernel (count margin : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulusCode := canonicalCounter count
  let marginCode := canonicalCounter margin
  let safe := membership modulusCode.digits marginCode.digits output
  let shifted := BinaryBodyKernel.translated count margin shift.negative shift.digits output
  ⟨if safe.value then zero else shifted.data,
    modulusCode.work+marginCode.work+safe.work+shifted.work+5⟩



def kernelWork (bound : ℕ) := 100*(bound+1)^2+100*bound+100+BinaryBodyKernel.translatedWork bound+5



def current (security : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let result := kernel modulus.count margin.count shift output
  ⟨result.data, modulus.work+margin.work+result.work+3⟩



noncomputable section
noncomputable def parameterPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+shiftBits+outputBits
noncomputable def heightPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  parameterPolynomial shiftBits outputBits*(parameterPolynomial shiftBits outputBits+4)
noncomputable def kernelWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+1)^2+100*bound+100+BinaryBodyKernel.translatedWorkPolynomial bound+5
noncomputable def workPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    kernelWorkPolynomial (parameterPolynomial shiftBits outputBits)+3





end
end CurrentAFT.BinaryUnsafeProfile

end

section
























/-! # The full shifted safe law, with generated current metadata -/
namespace CurrentAFT.BinaryShiftedSafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBodyKernel.translated

def current (security : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let result := BinaryBodyKernel.translated modulus.count margin.count shift.negative shift.digits output
  ⟨result.data,modulus.work+margin.work+result.work+3⟩



noncomputable section
noncomputable def heightPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeProfile.heightPolynomial shiftBits outputBits
noncomputable def workPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    BinaryBodyKernel.translatedWorkPolynomial (BinaryUnsafeProfile.parameterPolynomial shiftBits outputBits)+3



end
end CurrentAFT.BinaryShiftedSafeProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryShiftedSafeProfile.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryShiftedSafeProfile.workPolynomial
  pure ()

end

section




























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryRootConvolution
end CurrentAFT.BinaryRootConvolution
namespace CurrentAFT.RationalBackgroundProfiles
end CurrentAFT.RationalBackgroundProfiles







/-! # Executed shifted and averaged profiles for the actual root channels -/
namespace CurrentAFT.BinaryRootProfile
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram FiniteConvolutionProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryReferenceTables.current BinaryShiftedSafeProfile.current BinaryRootConvolution.current
  BinaryMassLiftInput.current IntegerBits.residue

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def attachmentAt (security cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := BinaryAnchorProgram.coordinate cutoff index.val
  let result := BinaryShiftedSafeProfile.current security ⟨scalar.negative, scalar.digits⟩ output
  ⟨result.data, scalar.work+result.work+2⟩



def attachment (security bits : ℕ) (output : List Bool) : RationalResult :=
  let window := BinaryActivationProgram.cutoff security
  let result := BinaryWindowAverage.evaluate security window.count bits (attachmentAt security window.count output)
  ⟨result.data, window.work+result.work+2⟩



def preRoot (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  match role with
  | .free =>
    let reference := BinaryReferenceTables.current security bits
    let result := BinaryPaletteLookup.current reference.center output
    ⟨result.data, reference.work+result.work+2⟩
  | .attachment => attachment security bits output
  | .queue => BinaryShiftedSafeProfile.current security queue output



def key (security : ℕ) (root : IntegerBits) (output : List Bool) : BinaryArithmetic.Result :=
  let modulus := PublicParameterProgram.modulus security
  let code := canonicalCounter modulus.count
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative,difference.digits⟩ code.digits
  ⟨residue.digits, modulus.work+code.work+difference.work+residue.work+4⟩





def shifted (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) : RationalResult :=
  let index := key security root output
  let result := preRoot security bits role queue index.digits
  ⟨result.data,index.work+result.work+2⟩



def profileAt (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := preRoot security bits role queue code.digits
  ⟨result.data,code.work+result.work+2⟩



def mean (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let profile := buildArray modulus.count (profileAt security bits role queue)
  let result := BinaryRootConvolution.current security bits profile.data output
  ⟨result.data,modulus.work+profile.work+result.work+3⟩



def deviation (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) : RationalResult :=
  let first := shifted security bits role queue root output
  let second := mean security bits role queue output
  let result := difference first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩



def meanDeviation (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := ofCounter modulus.count
  let reciprocal := RationalBits.inverse encoded.data
  let average := mean security bits role queue output
  let result := difference average.data reciprocal.data
  ⟨result.data,modulus.work+encoded.work+reciprocal.work+average.work+result.work+5⟩



def densityInput (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := deviation security bits role queue root code.digits
  ⟨result.data,code.work+result.work+2⟩

def meanDensityInput (security bits : ℕ) (role : BodyRole) (queue : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := meanDeviation security bits role queue code.digits
  ⟨result.data,code.work+result.work+2⟩

def firstDensity (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (densityInput security bits role queue root) output

def meanDensity (security bits : ℕ) (role : BodyRole) (queue : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (meanDensityInput security bits role queue) output





end CurrentAFT.BinaryRootProfile

end

section
























/-! # Polynomial resources for every actual pre-root law -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
  BinaryPaletteLookup.current BinaryShiftedSafeProfile.current PublicParameterProgram.modulus
  BinaryActivationProgram.cutoff
noncomputable section

def cutoffPolynomial : Polynomial ℕ := (Polynomial.X+2)^2
def scalarBitsPolynomial : Polynomial ℕ := 2*cutoffPolynomial+1

def attachmentAtHeightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedSafeProfile.heightPolynomial scalarBitsPolynomial inputBits
def attachmentAtWorkPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryAnchorProgram.coordinateWorkPolynomial cutoffPolynomial+
    BinaryShiftedSafeProfile.workPolynomial scalarBitsPolynomial inputBits+2



def attachmentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  (2*cutoffPolynomial+1)*(500000000*((Polynomial.X+2)^2+precision+2)^6+attachmentAtHeightPolynomial inputBits+1)
def attachmentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.cutoffWorkPolynomial+
    BinaryWindowAverage.evaluateWorkPolynomial cutoffPolynomial precision (attachmentAtHeightPolynomial inputBits)
      (attachmentAtWorkPolynomial inputBits)+2



def freeHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+1)
def freeWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let H := BinaryReferenceTables.heightPolynomial precision
  BinaryReferenceTables.currentWorkPolynomial precision+
    Q*(50*(Q+1)^2+48*(Q+inputBits)+42+3*Q+3+primitiveWorkPolynomial ((Q+1)*(H+1))+2)+4



def preRootHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  freeHeightPolynomial precision+attachmentHeightPolynomial precision inputBits+
    BinaryShiftedSafeProfile.heightPolynomial queueBits inputBits
def preRootWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  freeWorkPolynomial precision inputBits+attachmentWorkPolynomial precision inputBits+
    BinaryShiftedSafeProfile.workPolynomial queueBits inputBits



end
end CurrentAFT.BinaryRootProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.attachmentAtWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.attachmentHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.attachmentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.cutoffPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.freeHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.freeWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.preRootHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.preRootWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.scalarBitsPolynomial
  pure ()

end

section




























/-! # One shared actual scalar averaged after complete coefficient products -/
namespace CurrentAFT.BinaryCoefficientScalarAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct GradedControlAlgebra FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryActivationProgram.cutoff

def term (order cutoff : ℕ) (table : IntegerBits → CoefficientProgram order)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := BinaryAnchorProgram.coordinate cutoff index.val
  let result := table ⟨scalar.negative,scalar.digits⟩ arity colors centers
  ⟨result.value,scalar.work+result.work+2⟩

def current (security bits order : ℕ) (table : IntegerBits → CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let window := BinaryActivationProgram.cutoff security
    let result := BinaryWindowAverage.evaluate security window.count bits (term order window.count table arity colors centers)
    ⟨result.data,window.work+result.work+2⟩



noncomputable section
def scalarBitsPolynomial : Polynomial ℕ := BinaryRootProfile.scalarBitsPolynomial
def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  (2*BinaryRootProfile.cutoffPolynomial+1)*(500000000*((Polynomial.X+2)^2+precision+2)^6+leafBits+1)
def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.cutoffWorkPolynomial+
    BinaryWindowAverage.evaluateWorkPolynomial BinaryRootProfile.cutoffPolynomial precision leafBits
      (BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2)+2



end
end CurrentAFT.BinaryCoefficientScalarAverage

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientScalarAverage.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientScalarAverage.scalarBitsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientScalarAverage.workPolynomial
  pure ()

end

section























/-! # Binomial coefficients with a fixed number of binary arithmetic steps

The loop length is the selected degree, not the population. Every subtraction,
conversion and rational operation belongs to the executed program.
-/
namespace CurrentAFT.BinaryBinomialCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def current (population : ℕ) : ℕ → RationalResult
  | 0 => ⟨one, 2⟩
  | count+1 =>
    let previous := current population count
    let remaining := subtractCounter population count
    let numerator := ofCounter remaining.count
    let denominator := ofCounter (count+1)
    let product := multiply previous.data numerator.data
    let result := quotient product.data denominator.data
    ⟨result.data, previous.work+remaining.work+numerator.work+denominator.work+product.work+result.work+5⟩



def stepWork (order population : ℕ) : ℕ :=
  2*population+2 + 60*(population+1)^2 + 60*(order+2)^2 +
    3*primitiveWorkBound ((order+1)*(population+order+2)) + 7





noncomputable def heightPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C order * (population + Polynomial.C (order+1))

noncomputable def workPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C order * (2*population+2+60*(population+1)^2+Polynomial.C (60*(order+2)^2)+
    3*BinaryCalibrationIteration.primitivePolynomial
      (Polynomial.C (order+1)*(population+Polynomial.C (order+2)))+7)+2



end CurrentAFT.BinaryBinomialCoefficient

end

section





















/-! # Binary fixed-degree powers of complete joint coefficient tables -/
namespace CurrentAFT.BinaryFamilyPower
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def unit (order : ℕ) : CoefficientProgram order := fun arity _ _ =>
  let decision := matchArity order arity (zeroArity order)
  ⟨if decision.value then one else zero, decision.work+1⟩

def power (order : ℕ) (programs : List (Entry order)) (table : CoefficientProgram order) : ℕ → CoefficientProgram order
  | 0 => unit order
  | count+1 => BinaryFamilyArithmetic.multiply order programs (power order programs table count) table





noncomputable section
open scoped Classical



noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order))
    (bits : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 0
  | count+1 => BinaryFamilyArithmetic.heightPolynomial order programs (heightPolynomial order programs bits count + bits)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order))
    (bits budget : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.C (12*order+6)
  | count+1 => BinaryFamilyArithmetic.workPolynomial order programs
      (heightPolynomial order programs bits count + bits) (workPolynomial order programs bits budget count + budget)



end
end CurrentAFT.BinaryFamilyPower

end


