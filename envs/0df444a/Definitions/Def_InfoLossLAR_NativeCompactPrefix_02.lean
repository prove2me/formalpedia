-- Prove2me | Definitions.Def_InfoLossLAR_NativeCompactPrefix_02
-- name    : InfoLossLAR_NativeCompactPrefix_02
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:46:28.105831+00:00
-- url     : https://prove2.me/theorems/31e2dae5-f867-4fd7-8b09-7c2660c6b559
-- title:
--   Independent response syntax and current proposal controls
-- statement:
--   This package defines independent canonical reference seeds and role laws, role equivalences and kernel polynomials, finite expansion and squarefree extraction syntax, fixed-order numbering, scalar compilation and paired canonical programs, current parameter and diffuse profile data, inward primary proposals, paired controls, fringe and background certificates, and first histogram coordinates.
--
--   The interfaces retain the shared finite reference experiment and the concrete current controls used to formulate local calibration. Ordinary approximation and transport bounds are stated separately. Supporting constructor identities remain part of the data API; native operation counts are kept separate from the platform machine-time certificate.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; exact source units Definitions.Def_InfoLossLAR_NativeSparsePrefix_14, Definitions.Def_InfoLossLAR_NativeSparsePrefix_15, Definitions.Def_InfoLossLAR_NativeSparsePrefix_16, Definitions.Def_InfoLossLAR_NativeSparsePrefix_17, Definitions.Def_InfoLossLAR_NativeSparsePrefix_18, Definitions.Def_InfoLossLAR_NativeSparsePrefix_19. Original module paths and non-import body hashes are recorded in native_compact_prefix/manifest.json. These previously audited data bodies are copied byte-for-byte with closed section wrappers, and published SparsePrefix01–07 remain unchanged. SHA256 2f6a41485e03548c9bb4d1f367c9b3655743fac341743e00e13bad5a0a0c5523.

import Definitions.Def_InfoLossLAR_NativeCompactPrefix_01

section

section








/-! # Centering at one reference and measuring fibers at another

These are the actual coefficients with atoms `δ - r`, divided by `p`.
Only the upper comparison `r ≤ R p` is used; no lower comparison or inverse
minimum atom enters the full, singleton, or supremum bounds.
-/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def referenceAtom (p r : FiniteDist Color) (source value : Color) : ℝ :=
  (if source=value then (p.weight value)⁻¹ else 0)-r.weight value/p.weight value

def referenceProjection (p r : Slot → FiniteDist Color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (value : Slot → Color) : ℝ :=
  ∑ source,(FiniteDist.independent p).weight source*f source*
    ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)

theorem referenceAtom_eq (p r : FiniteDist Color) (source value : Color) :
    referenceAtom p r source value = ((if source=value then 1 else 0)-r.weight value)/p.weight value := by
  unfold referenceAtom
  split_ifs <;> simp [sub_div,neg_div]

theorem referenceAtom_mean (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color) (source : Color) :
    (∑ value,p.weight value*referenceAtom p r source value)=0 := by
  have he (value : Color) : p.weight value*referenceAtom p r source value =
      (if source=value then 1 else 0)-r.weight value := by
    rw [referenceAtom_eq]
    field_simp [(hp value).ne']
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,r.sum_one]
  simp

theorem referenceAtom_abs_le (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color)
    (bound : ℝ) (hb : 1 ≤ bound) (hr : ∀ color,r.weight color ≤ bound*p.weight color)
    (source value : Color) : |referenceAtom p r source value| ≤ bound*atomMajorant p source value := by
  have hd : 0 ≤ r.weight value/p.weight value := div_nonneg (r.nonneg value) (hp value).le
  have hu : r.weight value/p.weight value ≤ bound := (div_le_iff₀ (hp value)).mpr (hr value)
  unfold referenceAtom atomMajorant
  split_ifs
  · have hi : 0 ≤ (p.weight value)⁻¹ := inv_nonneg.mpr (hp value).le
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hi,abs_of_nonneg hd]
    nlinarith
  · simpa only [zero_sub,abs_neg,abs_of_nonneg hd,zero_add,mul_one] using hu

theorem referenceProjection_square_majorant (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) (value : Slot → Color) :
    referenceProjection p r selected f value^2 ≤ bound^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2 := by
  let kernel (source : Slot → Color) := ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)
  have hk (source) : |kernel source| ≤ bound^selected.card*projectionMajorant p selected source value := by
    dsimp only [kernel]
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun slot _ => referenceAtom_abs_le _ _ (hp slot) bound hb (hr slot) _ _)).trans_eq
      (by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl)
  have hc : (∑ source,(FiniteDist.independent p).weight source*f source*kernel source)^2 ≤
      (∑ source,(FiniteDist.independent p).weight source*|kernel source|)*
      ∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro source _; exact mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)
    · intro source _; exact mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _)
    · intro source _; ring_nf; rw [sq_abs]
  have hm : (∑ source,(FiniteDist.independent p).weight source*|kernel source|) ≤
      bound^selected.card*(2:ℝ)^selected.card := by
    rw [← projectionMajorant_source p hp selected value,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_left (hk source) (FiniteDist.nonneg _ _)).trans_eq (by ring)
  have hs : (∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2) ≤
      bound^selected.card*∑ source,(FiniteDist.independent p).weight source*
        projectionMajorant p selected source value*f source^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hk source)
      (FiniteDist.nonneg _ _)) (sq_nonneg _)).trans_eq (by ring)
  apply hc.trans
  apply (mul_le_mul hm hs
    (Finset.sum_nonneg fun source _ => mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _))
    (by positivity)).trans_eq
  rw [pow_mul]
  ring





theorem referenceProjection_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent p).l2Sq (referenceProjection p r selected f) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq f := by
  have hb0 : 0 ≤ bound := le_trans (by norm_num) hb
  have hm (source : Slot → Color) :
      (∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value) =
      (2:ℝ)^selected.card := by
    unfold projectionMajorant
    rw [expectation_partial_product p selected (fun slot value => atomMajorant (p slot) (source slot) value)]
    simp only [atomMajorant_value _ (hp _),Finset.prod_const]
  calc
    _ ≤ ∑ value,(FiniteDist.independent p).weight value*(bound^(2*selected.card)*(2:ℝ)^selected.card*
        ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2) :=
      Finset.sum_le_sum fun value _ => mul_le_mul_of_nonneg_left
        (referenceProjection_square_majorant p r hp selected f bound hb hr value) (FiniteDist.nonneg _ _)
    _ = bound^(2*selected.card)*(2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro value _
      ring
    _ = _ := by
      simp_rw [hm]
      rw [← Finset.sum_mul]
      simp only [FiniteDist.l2Sq,FiniteDist.expectation,mul_pow]
      rw [Nat.mul_comm 2 selected.card,pow_mul]
      ring

end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance mixedReferenceCanonicalFibersSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- The literal selected coefficient centered at `r`, expressed as a density
relative to `p` on precisely the selected slots. -/
def referenceRestrictedComponent (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) : ℝ :=
  ∑ input,mass input*∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (input slot) (word slot)

theorem referenceRestrictedComponent_canonical (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.Canonical (fun slot : selected => p slot) Finset.univ
      (referenceRestrictedComponent p r mass selected) := by
  constructor
  · intro first second heq
    have heq : first=second := funext (fun slot => heq slot (Finset.mem_univ slot))
    rw [heq]
  · intro fixed _ values
    simp only [referenceRestrictedComponent,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro source _
    have hprod (color : Color) :
        (∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (Function.update values fixed color slot)) =
          MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
            ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ fixed),Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro slot hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    simp_rw [hprod]
    have hterm (color : Color) : (p fixed).weight color*(mass source*
        (MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
          ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))) =
        (mass source*∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))*
          ((p fixed).weight color*MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum,MixedKernel.referenceAtom_mean _ _ (hp fixed),mul_zero]

theorem referenceRestrictedComponent_eq (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (word : Slot → Color) :
    referenceRestrictedComponent p r mass selected (fun slot => word slot) =
      MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source) word := by
  unfold referenceRestrictedComponent MixedKernel.referenceProjection
  apply Finset.sum_congr rfl
  intro source _
  have hpos : (FiniteDist.independent p).weight source ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun slot _ => hp slot (source slot))
  rw [mul_div_cancel₀ _ hpos]
  congr 1
  exact Finset.prod_coe_sort selected (fun slot => MixedKernel.referenceAtom (p slot) (r slot) (source slot) (word slot))



theorem referenceRestrictedComponent_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq
        (fun source => mass source/(FiniteDist.independent p).weight source) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := independent_restriction_expectation p selected
    (fun word => referenceRestrictedComponent p r mass selected word^2)
  simp_rw [referenceRestrictedComponent_eq p r hp] at hh
  have he : (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) =
      (FiniteDist.independent p).l2Sq (MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source)) := by
    convert hh.symm using 1
    all_goals
      unfold FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
  rw [he]
  exact MixedKernel.referenceProjection_l2Sq_le p r hp selected _ bound hb hr

variable [Nonempty Color]











end
end AFT.LocalTensors

end

section



















































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primarySplitEquiv
end AFT.RepresentedPolynomial.primarySplitEquiv
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.seedExpansion
end AFT.RepresentedPolynomial.seedExpansion
namespace AFT.RepresentedPolynomial.seedExpansion.match_1
end AFT.RepresentedPolynomial.seedExpansion.match_1
namespace AFT.RepresentedPolynomial.splitPrimaryIndex
end AFT.RepresentedPolynomial.splitPrimaryIndex
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentOriginalJointSeed
end AFT.V7Calibration.independentOriginalJointSeed
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope



/-! # The actual independent numerator, replacing only old primary coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

structure PendingInput (Color : Type*) where
  seed : InputSeed Color
  pending : Finset (Fin seed.primaryOrder)



end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingExpansionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero





def pendingLinearState {Color : Type*} (state : PendingInput Color) : PendingInput Color :=
  if h : state.pending.Nonempty then ⟨state.seed,state.pending.erase (state.pending.min' h)⟩ else state





@[simp] theorem pendingLinearState_seed {Color : Type*} (state : PendingInput Color) :
    (pendingLinearState state).seed=state.seed := by
  unfold pendingLinearState
  split_ifs <;> rfl











end
end AFT.V7Calibration

end

section















/-! # The literal reference-centered coefficients reconstruct the full physical PGF -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance referenceCoefficientSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceCoefficientForm (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : MvPolynomial Color ℝ :=
  ∑ word : selected → Color,
    MvPolynomial.C (LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected word*∏ slot,primary.weight (word slot))*
      ∏ slot,MvPolynomial.X (word slot)









end
end AFT.RepresentedPolynomial

end

section








namespace AFT
end AFT
namespace AFT.MixedKernel
end AFT.MixedKernel



/-! # The actual linear coefficient uses only a positive singleton marginal -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]
local instance referenceSingletonSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

theorem referenceRestrictedComponent_singleton (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (slot : Slot) (values : ({slot} : Finset Slot) → Color) :
    referenceRestrictedComponent p r mass {slot} values =
      ((∑ word,if word slot=values ⟨slot,Finset.mem_singleton_self slot⟩ then mass word else 0) -
        (r slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩)*(∑ word,mass word)) /
      (p slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩) := by
  have hprod (source : Slot → Color) :
      (∏ index : ({slot} : Finset Slot),MixedKernel.referenceAtom (p index) (r index) (source index) (values index)) =
      MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values ⟨slot,Finset.mem_singleton_self slot⟩) :=
    Fintype.prod_subsingleton _ (⟨slot,Finset.mem_singleton_self slot⟩ : ({slot} : Finset Slot))
  unfold referenceRestrictedComponent
  simp_rw [hprod,MixedKernel.referenceAtom_eq]
  rw [sub_div,Finset.sum_div,Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> ring





end
end AFT.LocalTensors

end

section



























































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockDensity.signedAttachedMass
end AFT.BlockDensity.signedAttachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.taggedBlockMass
end AFT.BlockProducts.taggedBlockMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.sharedQueueShift
end AFT.FiniteDist.sharedQueueShift
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.independentCoordinateCost
end AFT.GaussianSource.independentCoordinateCost
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.normalizedRoot
end AFT.GaussianSource.normalizedRoot
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.pairedOutputCoordinateCost
end AFT.GaussianSource.pairedOutputCoordinateCost
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.rootMomentConstant
end AFT.GaussianSource.rootMomentConstant
namespace AFT.GaussianSource.rootPrefixDensity
end AFT.GaussianSource.rootPrefixDensity
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.GaussianSource.v7RootKernelSq
end AFT.GaussianSource.v7RootKernelSq
namespace AFT.GaussianSource.v7RootThetaBound
end AFT.GaussianSource.v7RootThetaBound
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.mixtureMass
end AFT.HistogramNormalization.mixtureMass
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.JointPhysicalChannel
end AFT.JointPhysicalChannel
namespace AFT.JointPhysicalChannel.mass
end AFT.JointPhysicalChannel.mass
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryInteriorFactor
end AFT.RepresentedPolynomial.boundaryInteriorFactor
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.initialPendingInput
end AFT.RepresentedPolynomial.initialPendingInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.physicalFirstProfile
end AFT.RepresentedPolynomial.physicalFirstProfile
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profileForm
end AFT.RepresentedPolynomial.profileForm
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.referenceCoefficientSeed
end AFT.RepresentedPolynomial.referenceCoefficientSeed
namespace AFT.RepresentedPolynomial.referenceCoefficientTable
end AFT.RepresentedPolynomial.referenceCoefficientTable
namespace AFT.RepresentedPolynomial.referenceInverseTable
end AFT.RepresentedPolynomial.referenceInverseTable
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.prefixLaw
end AFT.RootSlice.prefixLaw
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.RootSlice.subsetCoordinates
end AFT.RootSlice.subsetCoordinates
namespace AFT.RootSlice.subsetEnumeration
end AFT.RootSlice.subsetEnumeration
namespace AFT.RootSlice.subsetPrefix
end AFT.RootSlice.subsetPrefix
namespace AFT.RootTensor
end AFT.RootTensor
namespace AFT.RootTensor.groupedDensity
end AFT.RootTensor.groupedDensity
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBodyBranch
end AFT.V7Calibration.actualBodyBranch
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyRootSourceCost
end AFT.V7Calibration.actualBodyRootSourceCost
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCenteredRootBlock
end AFT.V7Calibration.actualCenteredRootBlock
namespace AFT.V7Calibration.actualCenteredRootBlock.match_1
end AFT.V7Calibration.actualCenteredRootBlock.match_1
namespace AFT.V7Calibration.actualCenteredRootTriple
end AFT.V7Calibration.actualCenteredRootTriple
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualConditionalForwardPolynomial
end AFT.V7Calibration.actualConditionalForwardPolynomial
namespace AFT.V7Calibration.actualControlResponseLinear
end AFT.V7Calibration.actualControlResponseLinear
namespace AFT.V7Calibration.actualControlRootDefectLinear
end AFT.V7Calibration.actualControlRootDefectLinear
namespace AFT.V7Calibration.actualControlRootSetResponseLinear
end AFT.V7Calibration.actualControlRootSetResponseLinear
namespace AFT.V7Calibration.actualCorrelatedForwardPolynomial
end AFT.V7Calibration.actualCorrelatedForwardPolynomial
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualForwardRootDefectPolynomial
end AFT.V7Calibration.actualForwardRootDefectPolynomial
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualIndependentControlResponseLinear
end AFT.V7Calibration.actualIndependentControlResponseLinear
namespace AFT.V7Calibration.actualIndependentForwardPolynomial
end AFT.V7Calibration.actualIndependentForwardPolynomial
namespace AFT.V7Calibration.actualInitialBackgroundCorrection
end AFT.V7Calibration.actualInitialBackgroundCorrection
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualJointTaggedOutput
end AFT.V7Calibration.actualJointTaggedOutput
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedChannel
end AFT.V7Calibration.actualPairedChannel
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceBoundaryRate
end AFT.V7Calibration.actualReferenceBoundaryRate
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualRootResponseLinear
end AFT.V7Calibration.actualRootResponseLinear
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_background_product_boundary_eventually
end AFT.V7Calibration.actual_background_product_boundary_eventually
namespace AFT.V7Calibration.actual_background_product_boundary_eventually.match_1_1
end AFT.V7Calibration.actual_background_product_boundary_eventually.match_1_1
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blockPhysicalPolynomial.match_1
end AFT.V7Calibration.blockPhysicalPolynomial.match_1
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.bodyRootReference
end AFT.V7Calibration.bodyRootReference
namespace AFT.V7Calibration.centeredRootBodyProfile
end AFT.V7Calibration.centeredRootBodyProfile
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentBodyPositiveMass
end AFT.V7Calibration.independentBodyPositiveMass
namespace AFT.V7Calibration.independentBodyReciprocal
end AFT.V7Calibration.independentBodyReciprocal
namespace AFT.V7Calibration.independentGlobalQuotient
end AFT.V7Calibration.independentGlobalQuotient
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointHigherTable
end AFT.V7Calibration.independentJointHigherTable
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedForm
end AFT.V7Calibration.independentPairedForm
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentPairedPositiveMass
end AFT.V7Calibration.independentPairedPositiveMass
namespace AFT.V7Calibration.independentPositiveInputTable
end AFT.V7Calibration.independentPositiveInputTable
namespace AFT.V7Calibration.independentPositiveReciprocal
end AFT.V7Calibration.independentPositiveReciprocal
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.independentRootResponseLinear
end AFT.V7Calibration.independentRootResponseLinear
namespace AFT.V7Calibration.integerAnchorDifferenceProfile
end AFT.V7Calibration.integerAnchorDifferenceProfile
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.integerTranslateLinear
end AFT.V7Calibration.integerTranslateLinear
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.pendingOtherForms
end AFT.V7Calibration.pendingOtherForms
namespace AFT.V7Calibration.pendingPhysicalForms
end AFT.V7Calibration.pendingPhysicalForms
namespace AFT.V7Calibration.pendingPhysicalPolynomial
end AFT.V7Calibration.pendingPhysicalPolynomial
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicBodyConstant
end AFT.V7Calibration.publicBodyConstant
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.publicIndependentForms
end AFT.V7Calibration.publicIndependentForms
namespace AFT.V7Calibration.publicInputIndependentPolynomial
end AFT.V7Calibration.publicInputIndependentPolynomial
namespace AFT.V7Calibration.publicPrimaryRootPolynomial
end AFT.V7Calibration.publicPrimaryRootPolynomial
namespace AFT.V7Calibration.publicRoleReference
end AFT.V7Calibration.publicRoleReference
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.rolePartition
end AFT.V7Calibration.rolePartition
namespace AFT.V7Calibration.rootBlockFullCost
end AFT.V7Calibration.rootBlockFullCost
namespace AFT.V7Calibration.rootBodyAllocatedCost
end AFT.V7Calibration.rootBodyAllocatedCost
namespace AFT.V7Calibration.rootBodyFullCost
end AFT.V7Calibration.rootBodyFullCost
namespace AFT.V7Calibration.rootBodyRowCost
end AFT.V7Calibration.rootBodyRowCost
namespace AFT.V7Calibration.rootBodyVariance
end AFT.V7Calibration.rootBodyVariance
namespace AFT.V7Calibration.rootCenteredShift
end AFT.V7Calibration.rootCenteredShift
namespace AFT.V7Calibration.rootCoreFringe
end AFT.V7Calibration.rootCoreFringe
namespace AFT.V7Calibration.rootProfileOperator
end AFT.V7Calibration.rootProfileOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.boundaryAverage_square_le
end AFT.boundaryAverage_square_le
namespace AFT.boundaryCollapse_density_energy_le
end AFT.boundaryCollapse_density_energy_le
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope




/-! # Actual public placement semantics of every joint mixed input seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPublicSeedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicSeedSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicSeedSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def inputSeedRole {Color : Type*} (seed : InputSeed Color) : Fin (seed.primaryOrder+seed.bodyOrder) → Bool :=
  Fin.addCases (fun _ => true) (fun _ => false)

theorem inputSeedRole_primary_card {Color : Type*} (seed : InputSeed Color) :
    Fintype.card (PrimaryRoles (inputSeedRole seed))=seed.primaryOrder := by
  let equiv : Fin seed.primaryOrder ≃ PrimaryRoles (inputSeedRole seed) := Equiv.ofBijective
    (fun index => ⟨Fin.castAdd seed.bodyOrder index,by simp [inputSeedRole]⟩) (by
      constructor
      · intro first second he
        apply Fin.ext
        exact congrArg (fun x => x.val.val) he
      · intro index
        rcases index with ⟨index,hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ index
        · intro first _
          exact ⟨first,rfl⟩
        · intro second hh
          simp [inputSeedRole] at hh)
  simpa only [Fintype.card_fin] using (Fintype.card_congr equiv).symm

theorem inputSeedRole_body_card {Color : Type*} (seed : InputSeed Color) :
    Fintype.card (BodyRoles (inputSeedRole seed))=seed.bodyOrder := by
  let equiv : Fin seed.bodyOrder ≃ BodyRoles (inputSeedRole seed) := Equiv.ofBijective
    (fun index => ⟨Fin.natAdd seed.primaryOrder index,by simp [inputSeedRole]⟩) (by
      constructor
      · intro first second he
        apply Fin.ext
        have hh := congrArg (fun x => x.val.val) he
        change seed.primaryOrder+first.val=seed.primaryOrder+second.val at hh
        omega
      · intro index
        rcases index with ⟨index,hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ index
        · intro first hh
          simp [inputSeedRole] at hh
        · intro second _
          exact ⟨second,rfl⟩)
  simpa only [Fintype.card_fin] using (Fintype.card_congr equiv).symm









end
end AFT.V7Calibration

end

section














































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.initialPendingInput
end AFT.RepresentedPolynomial.initialPendingInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.physicalFirstProfile
end AFT.RepresentedPolynomial.physicalFirstProfile
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.referenceCoefficientSeed
end AFT.RepresentedPolynomial.referenceCoefficientSeed
namespace AFT.RepresentedPolynomial.referenceCoefficientTable
end AFT.RepresentedPolynomial.referenceCoefficientTable
namespace AFT.RepresentedPolynomial.referenceInverseTable
end AFT.RepresentedPolynomial.referenceInverseTable
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedChannel
end AFT.V7Calibration.actualPairedChannel
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentBodyPositiveMass
end AFT.V7Calibration.independentBodyPositiveMass
namespace AFT.V7Calibration.independentBodyReciprocal
end AFT.V7Calibration.independentBodyReciprocal
namespace AFT.V7Calibration.independentGlobalQuotient
end AFT.V7Calibration.independentGlobalQuotient
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointHigherTable
end AFT.V7Calibration.independentJointHigherTable
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentPairedPositiveMass
end AFT.V7Calibration.independentPairedPositiveMass
namespace AFT.V7Calibration.independentPositiveInputTable
end AFT.V7Calibration.independentPositiveInputTable
namespace AFT.V7Calibration.independentPositiveReciprocal
end AFT.V7Calibration.independentPositiveReciprocal
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.independentUpperColumn
end AFT.V7Calibration.independentUpperColumn
namespace AFT.V7Calibration.integerAnchorDifferenceProfile
end AFT.V7Calibration.integerAnchorDifferenceProfile
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.pendingOtherForms
end AFT.V7Calibration.pendingOtherForms
namespace AFT.V7Calibration.pendingPhysicalForms
end AFT.V7Calibration.pendingPhysicalForms
namespace AFT.V7Calibration.pendingPhysicalPolynomial
end AFT.V7Calibration.pendingPhysicalPolynomial
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope


/-! # The role-indexed realization of a literal mixed input seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance publicRoleSeedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance publicRoleSeedSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance publicRoleSeedSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
attribute [local instance] actualModulusNeZero



def publicRoleKernel {Color : Type*} (seed : InputSeed Color) :
    (PrimaryRoles (inputSeedRole seed) ⊕ BodyRoles (inputSeedRole seed) → Color) → ℝ :=
  fun word => seed.kernel (word ∘ (rolePartition (inputSeedRole seed)).symm)

def publicRoleSeed {Color : Type*} [Fintype Color] (seed : InputSeed Color) : InputSeed Color :=
  mixedFiniteSeed (publicRoleKernel seed)



@[simp] theorem publicRoleSeed_primaryOrder {Color : Type*} [Fintype Color] (seed : InputSeed Color) :
    (publicRoleSeed seed).primaryOrder=seed.primaryOrder := inputSeedRole_primary_card seed

@[simp] theorem publicRoleSeed_bodyOrder {Color : Type*} [Fintype Color] (seed : InputSeed Color) :
    (publicRoleSeed seed).bodyOrder=seed.bodyOrder := inputSeedRole_body_card seed







end
end AFT.V7Calibration

end

end

section

section








































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.monomialOccurrences
end AFT.RepresentedPolynomial.monomialOccurrences
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RepresentedPolynomial.wholeBoundarySeed
end AFT.RepresentedPolynomial.wholeBoundarySeed
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.seedBodyEquiv
end AFT.V7Calibration.seedBodyEquiv
namespace AFT.V7Calibration.seedPrimaryEquiv
end AFT.V7Calibration.seedPrimaryEquiv
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.boundaryAverage_square_le
end AFT.boundaryAverage_square_le
namespace AFT.boundaryCollapse_density_energy_le
end AFT.boundaryCollapse_density_energy_le
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix



/-! # Role-preserving equivalence of complete joint input seeds -/
namespace AFT.RepresentedPolynomial
open V7Calibration CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
local instance seedRoleFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance seedRoleSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance seedRoleSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
variable {Color : Type*}

/-- Reindex the full joint kernel while retaining each coordinate's primary/body role. -/
structure SeedRoleEquiv (first second : InputSeed Color) where
  coordinates : Fin (first.primaryOrder+first.bodyOrder) ≃ Fin (second.primaryOrder+second.bodyOrder)
  role : ∀ slot,inputSeedRole second (coordinates slot)=inputSeedRole first slot
  kernel : ∀ word,first.kernel (word ∘ coordinates)=second.kernel word

namespace SeedRoleEquiv
variable {first second third : InputSeed Color}

 

 

 

 

 

 

 

 

 

 

 

 

end SeedRoleEquiv
end
end AFT.RepresentedPolynomial

end

section































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Unweighted joint-kernel forms retaining the primary/body roles -/
namespace AFT.RepresentedPolynomial
open V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance kernelPolynomialUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance kernelPolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Other Color Output : Type*} [Fintype Slot] [Fintype Other]
  [DecidableEq Slot] [DecidableEq Other] [Fintype Color]

def kernelPolynomial (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ) : Table Output :=
  ∑ word,MvPolynomial.C (kernel word)*∏ slot,forms slot (word slot)









/-- The forms may keep the roles as separate indeterminates. No physical
channel identification or invertibility premise is used. -/
def inputKernelPolynomial (primary body : Color → Table Output) (seed : InputSeed Color) : Table Output :=
  kernelPolynomial (Fin.addCases (fun _ => primary) (fun _ => body)) seed.kernel

def inputKernelPolynomialHom (primary body : Color → Table Output) :
    Table (InputSeed Color) →+* Table Output :=
  MvPolynomial.eval₂Hom MvPolynomial.C (inputKernelPolynomial primary body)

@[simp] theorem inputKernelPolynomialHom_X (primary body : Color → Table Output) (seed : InputSeed Color) :
    inputKernelPolynomialHom primary body (MvPolynomial.X seed)=inputKernelPolynomial primary body seed := by
  simp [inputKernelPolynomialHom]



end
end AFT.RepresentedPolynomial

end

section























































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductForms
end AFT.RepresentedPolynomial.controlProductForms
namespace AFT.RepresentedPolynomial.controlProductForms.match_1
end AFT.RepresentedPolynomial.controlProductForms.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.initialPendingInput
end AFT.RepresentedPolynomial.initialPendingInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.kernelPolynomial
end AFT.RepresentedPolynomial.kernelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.physicalFirstProfile
end AFT.RepresentedPolynomial.physicalFirstProfile
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryInverseMatrix
end AFT.RepresentedPolynomial.primaryInverseMatrix
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.referenceCoefficientSeed
end AFT.RepresentedPolynomial.referenceCoefficientSeed
namespace AFT.RepresentedPolynomial.referenceCoefficientTable
end AFT.RepresentedPolynomial.referenceCoefficientTable
namespace AFT.RepresentedPolynomial.referenceInverseTable
end AFT.RepresentedPolynomial.referenceInverseTable
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualDensityInverseEntry
end AFT.V7Calibration.actualDensityInverseEntry
namespace AFT.V7Calibration.actualDensityInverseProgram
end AFT.V7Calibration.actualDensityInverseProgram
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedChannel
end AFT.V7Calibration.actualPairedChannel
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryReciprocalProgram
end AFT.V7Calibration.actualPrimaryReciprocalProgram
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentBodyPositiveMass
end AFT.V7Calibration.independentBodyPositiveMass
namespace AFT.V7Calibration.independentBodyReciprocal
end AFT.V7Calibration.independentBodyReciprocal
namespace AFT.V7Calibration.independentGlobalQuotient
end AFT.V7Calibration.independentGlobalQuotient
namespace AFT.V7Calibration.independentInverseColumn
end AFT.V7Calibration.independentInverseColumn
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointHigherTable
end AFT.V7Calibration.independentJointHigherTable
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentPairedPositiveMass
end AFT.V7Calibration.independentPairedPositiveMass
namespace AFT.V7Calibration.independentPositiveInputTable
end AFT.V7Calibration.independentPositiveInputTable
namespace AFT.V7Calibration.independentPositiveReciprocal
end AFT.V7Calibration.independentPositiveReciprocal
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.independentUpperColumn
end AFT.V7Calibration.independentUpperColumn
namespace AFT.V7Calibration.integerAnchorDifferenceProfile
end AFT.V7Calibration.integerAnchorDifferenceProfile
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.pendingKernelForms
end AFT.V7Calibration.pendingKernelForms
namespace AFT.V7Calibration.pendingKernelPolynomial
end AFT.V7Calibration.pendingKernelPolynomial
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.pendingNumeratorTable
end AFT.V7Calibration.pendingNumeratorTable
namespace AFT.V7Calibration.pendingOtherForms
end AFT.V7Calibration.pendingOtherForms
namespace AFT.V7Calibration.pendingOtherKernelForms
end AFT.V7Calibration.pendingOtherKernelForms
namespace AFT.V7Calibration.pendingPhysicalForms
end AFT.V7Calibration.pendingPhysicalForms
namespace AFT.V7Calibration.pendingPhysicalPolynomial
end AFT.V7Calibration.pendingPhysicalPolynomial
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix




/-! # The full independent joint response acts by role-specific forms -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentActionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color Output : Type*} [Fintype Color]



@[simp] theorem inputKernelPolynomialHom_C (primary body : Color → Table Output) (scalar : ℝ) :
    inputKernelPolynomialHom primary body (MvPolynomial.C scalar)=MvPolynomial.C scalar := by
  simp [inputKernelPolynomialHom]



end
end AFT.RepresentedPolynomial
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentActionV7FinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Output : Type*}
variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)













end
end AFT.V7Calibration

end

section










namespace AFT
end AFT
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState



/-! # Finite stored numbering for each fixed input-order bound

The numerical program takes the vectors below as finite constant data. Their
existence does not require computing `Fintype.equivFin` at runtime. The stored
vectors depend only on the fixed order bound, and on no security parameter,
source law, beta, channel, or input kernel.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- A mask is the ordinary four-bit output subset. -/
def pendingMask (mask : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun slot => mask.val.testBit slot.val)

def pendingNumberingIndex (bound : ℕ) :
    (Fin (bound+1) × (Fin (bound+1) × (Fin 16 × Fin (bound+4)))) ≃
      Fin ((bound+1)*((bound+1)*(16*(bound+4)))) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finProdFinEquiv

structure FixedOrderNumberingCode (bound : ℕ) where
  primary : Vector ℕ ((bound+1)*((bound+1)*(16*(bound+4))))
  body : Vector ℕ ((bound+1)*(bound+1))

def FixedOrderNumberingCode.primaryLookup {bound : ℕ} (code : FixedOrderNumberingCode bound)
    (order point : Fin (bound+1)) (mask : Fin 16) (slot : Fin (bound+4)) : ℕ :=
  code.primary.get (pendingNumberingIndex bound (order,point,mask,slot))



noncomputable section
open RepresentedPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance fixedOrderNumberingFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Semantic target for the stored vector; this function is never called
by the executable lookup. -/
def pendingNumberingMeaning {bound : ℕ} (order point : Fin (bound+1))
    (mask : Fin 16) (slot : Fin (bound+4)) : ℕ :=
  if hp : point.val<order.val then
    let selected := pendingMask mask
    let oldPoint : Fin order.val := ⟨point.val,hp⟩
    if hs : slot.val<4 then
      if hm : (⟨slot.val,hs⟩ : Fin 4)∈selected then
        (Fintype.equivFin (selected ⊕ {other : Fin order.val // other≠oldPoint}) (Sum.inl ⟨⟨slot.val,hs⟩,hm⟩)).val
      else 0
    else if ho : slot.val-4<order.val then
      if hd : (⟨slot.val-4,ho⟩ : Fin order.val)≠oldPoint then
        (Fintype.equivFin (selected ⊕ {other : Fin order.val // other≠oldPoint}) (Sum.inr ⟨⟨slot.val-4,ho⟩,hd⟩)).val
      else 0
    else 0
  else 0















end
end AFT.RationalNumerics

end

end

section

section





































































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.finiteLaw
end AFT.BetaReference.finiteLaw
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.integerCDFPrefix
end AFT.BetaReference.integerCDFPrefix
namespace AFT.BetaReference.integerCDFTerm
end AFT.BetaReference.integerCDFTerm
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BetaReference.safeGridValue
end AFT.BetaReference.safeGridValue
namespace AFT.BinaryCDFSampler
end AFT.BinaryCDFSampler
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.HistogramGenerating
end AFT.HistogramGenerating
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.ParameterProgram
end AFT.ParameterProgram
namespace AFT.ParameterProgram.beta
end AFT.ParameterProgram.beta
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.pending_primary_count
end AFT.RationalNumerics.pending_primary_count
namespace AFT.RationalNumerics.rationalSelectedCoefficient
end AFT.RationalNumerics.rationalSelectedCoefficient
namespace AFT.RationalNumerics.selectedInverseProgram
end AFT.RationalNumerics.selectedInverseProgram
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryInverseMatrix
end AFT.RepresentedPolynomial.primaryInverseMatrix
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBetaBufferedTail
end AFT.V7Calibration.actualBetaBufferedTail
namespace AFT.V7Calibration.actualBetaGridError
end AFT.V7Calibration.actualBetaGridError
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualBoundaryCoefficient
end AFT.V7Calibration.actualBoundaryCoefficient
namespace AFT.V7Calibration.actualBoundaryCoefficientProgram
end AFT.V7Calibration.actualBoundaryCoefficientProgram
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualBoundaryUniformProgram
end AFT.V7Calibration.actualBoundaryUniformProgram
namespace AFT.V7Calibration.actualCanonicalBasisProgram
end AFT.V7Calibration.actualCanonicalBasisProgram
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualDensityInverseEntry
end AFT.V7Calibration.actualDensityInverseEntry
namespace AFT.V7Calibration.actualDensityInverseProgram
end AFT.V7Calibration.actualDensityInverseProgram
namespace AFT.V7Calibration.actualDimension_positive
end AFT.V7Calibration.actualDimension_positive
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorCountProgram
end AFT.V7Calibration.actualInteriorCountProgram
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualInteriorUniformProgram
end AFT.V7Calibration.actualInteriorUniformProgram
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryProgram
end AFT.V7Calibration.actualPrimaryProgram
namespace AFT.V7Calibration.actualPrimaryReciprocalProgram
end AFT.V7Calibration.actualPrimaryReciprocalProgram
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualReferenceProgram
end AFT.V7Calibration.actualReferenceProgram
namespace AFT.V7Calibration.actualReferenceZeroChargeHistogram
end AFT.V7Calibration.actualReferenceZeroChargeHistogram
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualShiftedBodyProgram
end AFT.V7Calibration.actualShiftedBodyProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridCutoff
end AFT.V7Calibration.betaGridCutoff
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridRejectedMass
end AFT.V7Calibration.betaGridRejectedMass
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedDensityColumn
end AFT.V7Calibration.fixedPairedDensityColumn
namespace AFT.V7Calibration.fixedPairedDensityProgram
end AFT.V7Calibration.fixedPairedDensityProgram
namespace AFT.V7Calibration.fixedPairedDensityProgramError
end AFT.V7Calibration.fixedPairedDensityProgramError
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedKernelProgramError
end AFT.V7Calibration.fixedPairedKernelProgramError
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentInverseColumn
end AFT.V7Calibration.independentInverseColumn
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.modulus_population_upper
end AFT.V7Calibration.modulus_population_upper
namespace AFT.V7Calibration.pairedRootReference
end AFT.V7Calibration.pairedRootReference
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix


/-! # Finite syntax for the literal independent nonlinear kernel replacements -/
namespace AFT.RationalNumerics

structure KernelShape where
  primary : ℕ
  body : ℕ
  deriving DecidableEq

inductive PendingKernelCode (Leaf : Type*) where
  | leaf : Leaf → PendingKernelCode Leaf
  | higher : PendingKernelCode Leaf → ℕ → Fin 16 → PendingKernelCode Leaf











noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance pendingKernelSyntaxFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _









end
end AFT.RationalNumerics

end

section


















namespace AFT
end AFT
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.OrderedSeedTable
end AFT.RationalNumerics.OrderedSeedTable
namespace AFT.RationalNumerics.orderedSeedExpansion
end AFT.RationalNumerics.orderedSeedExpansion
namespace AFT.RationalNumerics.orderedSeedExpansion.match_1
end AFT.RationalNumerics.orderedSeedExpansion.match_1
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.seedExpansion
end AFT.RepresentedPolynomial.seedExpansion
namespace AFT.RepresentedPolynomial.seedExpansion.match_1
end AFT.RepresentedPolynomial.seedExpansion.match_1



/-! # An executable pending expansion for the actual nonlinear numerator -/
namespace AFT.RationalNumerics











structure PendingProgramState (Leaf : Type*) where
  kernel : PendingKernelCode Leaf
  pending : Finset ℕ













noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance pendingExpansionProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _







end
end AFT.RationalNumerics

end

section














/-! # Natural-index storage for finite pending-coordinate sets -/
namespace AFT.RationalNumerics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Restrict a stored set of natural indices to the current finite order. -/
def finitePending (order : ℕ) (pending : Finset ℕ) : Finset (Fin order) :=
  Finset.univ.filter (fun point => point.val∈pending)

@[simp] theorem mem_finitePending {order : ℕ} {pending : Finset ℕ} {point : Fin order} :
    point∈finitePending order pending ↔ point.val∈pending := by
  simp only [finitePending,Finset.mem_filter,Finset.mem_univ,true_and]











@[simp] theorem finitePending_range (order : ℕ) : finitePending order (Finset.range order)=Finset.univ := by
  ext point
  simp only [mem_finitePending,Finset.mem_range,point.isLt,Finset.mem_univ]

end
end AFT.RationalNumerics

end

section
























































namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix



/-! # Extracting distinct public placements from a polynomial

Squarefree public-position monomials retain exactly the injective placements.
The two falling-factorial denominators are kept separately, including the
zero-denominator convention when a pool is too small.
-/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
local instance extractionSumDecEq {First Second : Type*} : DecidableEq (First⊕Second) := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {Slot Position Primary Body PP BP : Type*}
  [Fintype Slot] [DecidableEq Slot] [Fintype Position] [DecidableEq Position]
  [Fintype Primary] [DecidableEq Primary] [Fintype Body] [DecidableEq Body]
  [Fintype PP] [DecidableEq PP] [Fintype BP] [DecidableEq BP]









def poolCoefficientWeight (powers : (PP⊕BP) →₀ ℕ) : ℝ :=
  if ∀ position,powers position≤1 then
    (((Fintype.card PP).descFactorial (∑ position : PP,powers (.inl position)) : ℝ)*
      ((Fintype.card BP).descFactorial (∑ position : BP,powers (.inr position)) : ℝ))⁻¹
  else 0

/-- The linear coefficient extractor kills collisions and normalizes each
role by its original distinct-placement count. -/
def poolCoefficientExtraction : Table (PP⊕BP) →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ poolCoefficientWeight).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

omit [DecidableEq PP] [DecidableEq BP] in
@[simp] theorem poolCoefficientExtraction_monomial (powers : (PP⊕BP) →₀ ℕ) (scalar : ℝ) :
    poolCoefficientExtraction (MvPolynomial.monomial powers scalar)=
      scalar*poolCoefficientWeight powers := by
  exact Finsupp.linearCombination_single ℝ scalar powers















variable {Color : Type*} [Fintype Color]







end
end AFT.RepresentedPolynomial

end

section



























































































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.finiteLaw
end AFT.BetaReference.finiteLaw
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.integerCDFPrefix
end AFT.BetaReference.integerCDFPrefix
namespace AFT.BetaReference.integerCDFTerm
end AFT.BetaReference.integerCDFTerm
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BetaReference.safeGridValue
end AFT.BetaReference.safeGridValue
namespace AFT.BinaryCDFSampler
end AFT.BinaryCDFSampler
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSignedSum
end AFT.GaussianSignedSum
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.HistogramGenerating
end AFT.HistogramGenerating
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.ParameterProgram
end AFT.ParameterProgram
namespace AFT.ParameterProgram.beta
end AFT.ParameterProgram.beta
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.KernelShape
end AFT.RationalNumerics.KernelShape
namespace AFT.RationalNumerics.KernelShape.join
end AFT.RationalNumerics.KernelShape.join
namespace AFT.RationalNumerics.OrderedSeedTable
end AFT.RationalNumerics.OrderedSeedTable
namespace AFT.RationalNumerics.OrderedSeedTable.correction
end AFT.RationalNumerics.OrderedSeedTable.correction
namespace AFT.RationalNumerics.OrderedSeedTable.correction.match_1
end AFT.RationalNumerics.OrderedSeedTable.correction.match_1
namespace AFT.RationalNumerics.OrderedSeedTable.multiply
end AFT.RationalNumerics.OrderedSeedTable.multiply
namespace AFT.RationalNumerics.OrderedSeedTable.power
end AFT.RationalNumerics.OrderedSeedTable.power
namespace AFT.RationalNumerics.OrderedSeedTable.power.match_1
end AFT.RationalNumerics.OrderedSeedTable.power.match_1
namespace AFT.RationalNumerics.OrderedSeedTable.relabel
end AFT.RationalNumerics.OrderedSeedTable.relabel
namespace AFT.RationalNumerics.OrderedSeedTable.truncate
end AFT.RationalNumerics.OrderedSeedTable.truncate
namespace AFT.RationalNumerics.ParametricSeedTable
end AFT.RationalNumerics.ParametricSeedTable
namespace AFT.RationalNumerics.ParametricSeedTable.substitute
end AFT.RationalNumerics.ParametricSeedTable.substitute
namespace AFT.RationalNumerics.ParametricSeedTable.sum
end AFT.RationalNumerics.ParametricSeedTable.sum
namespace AFT.RationalNumerics.ParametricSeedTable.truncate
end AFT.RationalNumerics.ParametricSeedTable.truncate
namespace AFT.RationalNumerics.ParametricSeedTerm
end AFT.RationalNumerics.ParametricSeedTerm
namespace AFT.RationalNumerics.PendingKernelCode
end AFT.RationalNumerics.PendingKernelCode
namespace AFT.RationalNumerics.PendingKernelCode.denote
end AFT.RationalNumerics.PendingKernelCode.denote
namespace AFT.RationalNumerics.PendingKernelCode.shape
end AFT.RationalNumerics.PendingKernelCode.shape
namespace AFT.RationalNumerics.PendingKernelCode.shape.match_1
end AFT.RationalNumerics.PendingKernelCode.shape.match_1
namespace AFT.RationalNumerics.PendingProgramState
end AFT.RationalNumerics.PendingProgramState
namespace AFT.RationalNumerics.PendingProgramState.denote
end AFT.RationalNumerics.PendingProgramState.denote
namespace AFT.RationalNumerics.correction_succ_linear
end AFT.RationalNumerics.correction_succ_linear
namespace AFT.RationalNumerics.countedOrderedJointKernel
end AFT.RationalNumerics.countedOrderedJointKernel
namespace AFT.RationalNumerics.independentQuotientDecode
end AFT.RationalNumerics.independentQuotientDecode
namespace AFT.RationalNumerics.independentQuotientFactors
end AFT.RationalNumerics.independentQuotientFactors
namespace AFT.RationalNumerics.joinedKernelIndex
end AFT.RationalNumerics.joinedKernelIndex
namespace AFT.RationalNumerics.orderedControlIndex
end AFT.RationalNumerics.orderedControlIndex
namespace AFT.RationalNumerics.orderedIndependentColumnFactors
end AFT.RationalNumerics.orderedIndependentColumnFactors
namespace AFT.RationalNumerics.orderedIndependentUpperTable
end AFT.RationalNumerics.orderedIndependentUpperTable
namespace AFT.RationalNumerics.orderedJointKernel
end AFT.RationalNumerics.orderedJointKernel
namespace AFT.RationalNumerics.orderedJointKernel.match_1
end AFT.RationalNumerics.orderedJointKernel.match_1
namespace AFT.RationalNumerics.orderedJointSeed
end AFT.RationalNumerics.orderedJointSeed
namespace AFT.RationalNumerics.orderedJointShape
end AFT.RationalNumerics.orderedJointShape
namespace AFT.RationalNumerics.orderedJointShape.match_1
end AFT.RationalNumerics.orderedJointShape.match_1
namespace AFT.RationalNumerics.orderedSeedExpansion
end AFT.RationalNumerics.orderedSeedExpansion
namespace AFT.RationalNumerics.orderedSeedExpansion.match_1
end AFT.RationalNumerics.orderedSeedExpansion.match_1
namespace AFT.RationalNumerics.pendingProgramChoices
end AFT.RationalNumerics.pendingProgramChoices
namespace AFT.RationalNumerics.pendingProgramHigher
end AFT.RationalNumerics.pendingProgramHigher
namespace AFT.RationalNumerics.pendingProgramLinear
end AFT.RationalNumerics.pendingProgramLinear
namespace AFT.RationalNumerics.shapeSeed
end AFT.RationalNumerics.shapeSeed
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.CanonicalColumnDomain
end AFT.RepresentedPolynomial.CanonicalColumnDomain
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.canonicalRestrictedColumn
end AFT.RepresentedPolynomial.canonicalRestrictedColumn
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductForms
end AFT.RepresentedPolynomial.controlProductForms
namespace AFT.RepresentedPolynomial.controlProductForms.match_1
end AFT.RepresentedPolynomial.controlProductForms.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.gaussianCoefficient
end AFT.RepresentedPolynomial.gaussianCoefficient
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.initialPendingInput
end AFT.RepresentedPolynomial.initialPendingInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.kernelPolynomial
end AFT.RepresentedPolynomial.kernelPolynomial
namespace AFT.RepresentedPolynomial.leadingGaussianValue
end AFT.RepresentedPolynomial.leadingGaussianValue
namespace AFT.RepresentedPolynomial.leadingSeedTensor
end AFT.RepresentedPolynomial.leadingSeedTensor
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.physicalFirstProfile
end AFT.RepresentedPolynomial.physicalFirstProfile
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryInverseMatrix
end AFT.RepresentedPolynomial.primaryInverseMatrix
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.referenceCoefficientSeed
end AFT.RepresentedPolynomial.referenceCoefficientSeed
namespace AFT.RepresentedPolynomial.referenceCoefficientTable
end AFT.RepresentedPolynomial.referenceCoefficientTable
namespace AFT.RepresentedPolynomial.referenceInverseTable
end AFT.RepresentedPolynomial.referenceInverseTable
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.seedExpansion
end AFT.RepresentedPolynomial.seedExpansion
namespace AFT.RepresentedPolynomial.seedExpansion.match_1
end AFT.RepresentedPolynomial.seedExpansion.match_1
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBetaBufferedTail
end AFT.V7Calibration.actualBetaBufferedTail
namespace AFT.V7Calibration.actualBetaGridError
end AFT.V7Calibration.actualBetaGridError
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyInputProgram
end AFT.V7Calibration.actualBodyInputProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyRawInput
end AFT.V7Calibration.actualBodyRawInput
namespace AFT.V7Calibration.actualBodyRawInputProgram
end AFT.V7Calibration.actualBodyRawInputProgram
namespace AFT.V7Calibration.actualBodyReciprocalFactors
end AFT.V7Calibration.actualBodyReciprocalFactors
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualBoundaryCoefficient
end AFT.V7Calibration.actualBoundaryCoefficient
namespace AFT.V7Calibration.actualBoundaryCoefficientProgram
end AFT.V7Calibration.actualBoundaryCoefficientProgram
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualBoundaryUniformProgram
end AFT.V7Calibration.actualBoundaryUniformProgram
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualDensityInverseEntry
end AFT.V7Calibration.actualDensityInverseEntry
namespace AFT.V7Calibration.actualDensityInverseProgram
end AFT.V7Calibration.actualDensityInverseProgram
namespace AFT.V7Calibration.actualDimension_positive
end AFT.V7Calibration.actualDimension_positive
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorCountProgram
end AFT.V7Calibration.actualInteriorCountProgram
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualInteriorUniformProgram
end AFT.V7Calibration.actualInteriorUniformProgram
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedChannel
end AFT.V7Calibration.actualPairedChannel
namespace AFT.V7Calibration.actualPairedInputFactors
end AFT.V7Calibration.actualPairedInputFactors
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPairedReciprocalFactors
end AFT.V7Calibration.actualPairedReciprocalFactors
namespace AFT.V7Calibration.actualPairedSelections
end AFT.V7Calibration.actualPairedSelections
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryProgram
end AFT.V7Calibration.actualPrimaryProgram
namespace AFT.V7Calibration.actualPrimaryReciprocalProgram
end AFT.V7Calibration.actualPrimaryReciprocalProgram
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualReferenceProgram
end AFT.V7Calibration.actualReferenceProgram
namespace AFT.V7Calibration.actualReferenceZeroChargeHistogram
end AFT.V7Calibration.actualReferenceZeroChargeHistogram
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridCutoff
end AFT.V7Calibration.betaGridCutoff
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridRejectedMass
end AFT.V7Calibration.betaGridRejectedMass
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentBodyPositiveMass
end AFT.V7Calibration.independentBodyPositiveMass
namespace AFT.V7Calibration.independentBodyPositiveProfile
end AFT.V7Calibration.independentBodyPositiveProfile
namespace AFT.V7Calibration.independentBodyPositiveProgram
end AFT.V7Calibration.independentBodyPositiveProgram
namespace AFT.V7Calibration.independentBodyReciprocal
end AFT.V7Calibration.independentBodyReciprocal
namespace AFT.V7Calibration.independentGlobalQuotient
end AFT.V7Calibration.independentGlobalQuotient
namespace AFT.V7Calibration.independentInverseColumn
end AFT.V7Calibration.independentInverseColumn
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointHigherTable
end AFT.V7Calibration.independentJointHigherTable
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentNumeratorTable
end AFT.V7Calibration.independentNumeratorTable
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentPairedPositiveMass
end AFT.V7Calibration.independentPairedPositiveMass
namespace AFT.V7Calibration.independentPositiveInputTable
end AFT.V7Calibration.independentPositiveInputTable
namespace AFT.V7Calibration.independentPositiveReciprocal
end AFT.V7Calibration.independentPositiveReciprocal
namespace AFT.V7Calibration.independentRawColumnLinear
end AFT.V7Calibration.independentRawColumnLinear
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.independentUpperColumn
end AFT.V7Calibration.independentUpperColumn
namespace AFT.V7Calibration.integerAnchorDifferenceProfile
end AFT.V7Calibration.integerAnchorDifferenceProfile
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.leadingGaussianFactor
end AFT.V7Calibration.leadingGaussianFactor
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.modulus_population_upper
end AFT.V7Calibration.modulus_population_upper
namespace AFT.V7Calibration.pendingKernelForms
end AFT.V7Calibration.pendingKernelForms
namespace AFT.V7Calibration.pendingKernelPolynomial
end AFT.V7Calibration.pendingKernelPolynomial
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.pendingNumeratorTable
end AFT.V7Calibration.pendingNumeratorTable
namespace AFT.V7Calibration.pendingOtherForms
end AFT.V7Calibration.pendingOtherForms
namespace AFT.V7Calibration.pendingOtherKernelForms
end AFT.V7Calibration.pendingOtherKernelForms
namespace AFT.V7Calibration.pendingPhysicalForms
end AFT.V7Calibration.pendingPhysicalForms
namespace AFT.V7Calibration.pendingPhysicalPolynomial
end AFT.V7Calibration.pendingPhysicalPolynomial
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.finiteCorrection
end AFT.finiteCorrection
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix



/-! # The actual independent upper map with explicit real scalar expressions -/
namespace AFT.RationalNumerics
open V7Calibration

/-- Rational literals in a finite structural column become scalar expression
nodes. This does not approximate any real source coefficient. -/
def ParametricSeedTable.ofOrdered {Scalar Code : Type*} (table : OrderedSeedTable Code) : ParametricSeedTable Scalar Code :=
  table.map (fun term => ⟨.rational term.coefficient,term.factors⟩)



@[simp] theorem ParametricSeedTable.ofOrdered_length {Scalar Code : Type*} (table : OrderedSeedTable Code) :
    (ofOrdered (Scalar := Scalar) table).length=table.length := List.length_map _

@[simp] theorem ParametricSeedTable.scale_length {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (table : ParametricSeedTable Scalar Code) : (table.scale scalar).length=table.length := List.length_map _



noncomputable section
open RepresentedPolynomial



end

noncomputable section
open RepresentedPolynomial GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {Scalar Leaf Output : Type*} {bound : ℕ}
variable (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Fin (Parameters.modulus n)) → ℝ)



end
end AFT.RationalNumerics

end

end

section

section
































































































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.coordinateInverseKernel
end AFT.MixedKernel.coordinateInverseKernel
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.ParametricSeedTable
end AFT.RationalNumerics.ParametricSeedTable
namespace AFT.RationalNumerics.ParametricSeedTable.ScalarSafe
end AFT.RationalNumerics.ParametricSeedTable.ScalarSafe
namespace AFT.RationalNumerics.ParametricSeedTable.rename
end AFT.RationalNumerics.ParametricSeedTable.rename
namespace AFT.RationalNumerics.ParametricSeedTable.substitute
end AFT.RationalNumerics.ParametricSeedTable.substitute
namespace AFT.RationalNumerics.ParametricSeedTable.sum
end AFT.RationalNumerics.ParametricSeedTable.sum
namespace AFT.RationalNumerics.ParametricSeedTable.truncate
end AFT.RationalNumerics.ParametricSeedTable.truncate
namespace AFT.RationalNumerics.ParametricSeedTerm
end AFT.RationalNumerics.ParametricSeedTerm
namespace AFT.RationalNumerics.ScalarProgram
end AFT.RationalNumerics.ScalarProgram
namespace AFT.RationalNumerics.ScalarProgram.exactInverseSyntax
end AFT.RationalNumerics.ScalarProgram.exactInverseSyntax
namespace AFT.RationalNumerics.boundaryDensityEntry
end AFT.RationalNumerics.boundaryDensityEntry
namespace AFT.RationalNumerics.parametricWholeBoundaryTable
end AFT.RationalNumerics.parametricWholeBoundaryTable
namespace AFT.RationalNumerics.wholeBoundaryDecode
end AFT.RationalNumerics.wholeBoundaryDecode
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryInteriorFactor
end AFT.RepresentedPolynomial.boundaryInteriorFactor
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.complementaryPrimaryForm
end AFT.RepresentedPolynomial.complementaryPrimaryForm
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductChannel
end AFT.RepresentedPolynomial.controlProductChannel
namespace AFT.RepresentedPolynomial.controlProductChannel.match_1
end AFT.RepresentedPolynomial.controlProductChannel.match_1
namespace AFT.RepresentedPolynomial.controlProductForms
end AFT.RepresentedPolynomial.controlProductForms
namespace AFT.RepresentedPolynomial.controlProductForms.match_1
end AFT.RepresentedPolynomial.controlProductForms.match_1
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.groupedInputEquiv
end AFT.RepresentedPolynomial.groupedInputEquiv
namespace AFT.RepresentedPolynomial.indexedOutput
end AFT.RepresentedPolynomial.indexedOutput
namespace AFT.RepresentedPolynomial.initialPendingInput
end AFT.RepresentedPolynomial.initialPendingInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.kernelPolynomial
end AFT.RepresentedPolynomial.kernelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.mixedMonomialSeed
end AFT.RepresentedPolynomial.mixedMonomialSeed
namespace AFT.RepresentedPolynomial.mixedProductSeed
end AFT.RepresentedPolynomial.mixedProductSeed
namespace AFT.RepresentedPolynomial.physicalFirstProfile
end AFT.RepresentedPolynomial.physicalFirstProfile
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryInverseMatrix
end AFT.RepresentedPolynomial.primaryInverseMatrix
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.referenceCoefficientSeed
end AFT.RepresentedPolynomial.referenceCoefficientSeed
namespace AFT.RepresentedPolynomial.referenceCoefficientTable
end AFT.RepresentedPolynomial.referenceCoefficientTable
namespace AFT.RepresentedPolynomial.referenceInverseTable
end AFT.RepresentedPolynomial.referenceInverseTable
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RepresentedPolynomial.wholeBoundarySeed
end AFT.RepresentedPolynomial.wholeBoundarySeed
namespace AFT.RepresentedPolynomial.wholeBoundaryTable
end AFT.RepresentedPolynomial.wholeBoundaryTable
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualBoundaryComplementProgram
end AFT.V7Calibration.actualBoundaryComplementProgram
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualDensityInverseProgram
end AFT.V7Calibration.actualDensityInverseProgram
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInitialBackgroundCorrection
end AFT.V7Calibration.actualInitialBackgroundCorrection
namespace AFT.V7Calibration.actualInteriorMassProgram
end AFT.V7Calibration.actualInteriorMassProgram
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualInteriorReciprocalProgram
end AFT.V7Calibration.actualInteriorReciprocalProgram
namespace AFT.V7Calibration.actualInteriorTest
end AFT.V7Calibration.actualInteriorTest
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairedChannel
end AFT.V7Calibration.actualPairedChannel
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryReciprocalProgram
end AFT.V7Calibration.actualPrimaryReciprocalProgram
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualReferenceBoundaryRate
end AFT.V7Calibration.actualReferenceBoundaryRate
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualUnactivatedInverseProgram
end AFT.V7Calibration.actualUnactivatedInverseProgram
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_background_product_boundary_eventually
end AFT.V7Calibration.actual_background_product_boundary_eventually
namespace AFT.V7Calibration.actual_background_product_boundary_eventually.match_1_1
end AFT.V7Calibration.actual_background_product_boundary_eventually.match_1_1
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentBodyPositiveMass
end AFT.V7Calibration.independentBodyPositiveMass
namespace AFT.V7Calibration.independentBodyReciprocal
end AFT.V7Calibration.independentBodyReciprocal
namespace AFT.V7Calibration.independentGlobalQuotient
end AFT.V7Calibration.independentGlobalQuotient
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointHigherTable
end AFT.V7Calibration.independentJointHigherTable
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentPairedPositiveMass
end AFT.V7Calibration.independentPairedPositiveMass
namespace AFT.V7Calibration.independentPositiveInputTable
end AFT.V7Calibration.independentPositiveInputTable
namespace AFT.V7Calibration.independentPositiveReciprocal
end AFT.V7Calibration.independentPositiveReciprocal
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.independentUpperColumn
end AFT.V7Calibration.independentUpperColumn
namespace AFT.V7Calibration.integerAnchorDifferenceProfile
end AFT.V7Calibration.integerAnchorDifferenceProfile
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.pendingLinearState
end AFT.V7Calibration.pendingLinearState
namespace AFT.V7Calibration.pendingOtherForms
end AFT.V7Calibration.pendingOtherForms
namespace AFT.V7Calibration.pendingPhysicalForms
end AFT.V7Calibration.pendingPhysicalForms
namespace AFT.V7Calibration.pendingPhysicalPolynomial
end AFT.V7Calibration.pendingPhysicalPolynomial
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.boundaryAverage_square_le
end AFT.boundaryAverage_square_le
namespace AFT.boundaryCollapse_density_energy_le
end AFT.boundaryCollapse_density_energy_le
namespace AFT.canonicalInteriorProfiles
end AFT.canonicalInteriorProfiles
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix



/-! Literal values are bounded in magnitude as integers, so runtime-dependent
literals can be generated by counted integer loops, rather than stored by an
existential encoding theorem. -/
namespace AFT.RationalNumerics

def RationalLiteralBound (value : ℚ) (bound : ℕ) : Prop :=
  value.num.natAbs≤bound ∧ value.den≤bound

namespace RationalLiteralBound





















end RationalLiteralBound

namespace ScalarProgram
variable {Scalar : Type*}

def LiteralBound (bound : ℕ) : ScalarProgram Scalar → Prop
  | .rational value => RationalLiteralBound value bound
  | .atom _ => True
  | .add first second | .multiply first second => first.LiteralBound bound ∧ second.LiteralBound bound
  | .negate term | .inverse term => term.LiteralBound bound


end ScalarProgram

namespace ParametricSeedTable
variable {Scalar Code Other : Type*}







































end ParametricSeedTable
end AFT.RationalNumerics

end

section






















/-! # Runtime encoding of polynomially bounded rational literals

The input rational is an already constructed numerator/denominator record.
Both integers are encoded by the actual counter algorithms, and the binary
quotient is normalized by the actual rational implementation. This module
charges encoding, not the earlier construction of the rational record.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics Polynomial

def encodeSmallRational (input : ℚ) : RationalResult :=
  let numerator := ofUnaryInteger input.num
  let denominator := ofCounter input.den
  let result := quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

theorem encodeSmallRational_value (input : ℚ) :
    (encodeSmallRational input).data.decode=input := by
  simp only [encodeSmallRational,quotient_value,ofUnaryInteger_value,ofCounter_value,
    Rat.num_div_den]

def smallRationalEncodingWork (bound : ℕ) : ℕ :=
  120*(bound+1)^2+2*primitiveWorkBound bound+10







noncomputable def smallRationalEncodingPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  120*(bound+1)^2+20000000*(bound+2)^3+10





end AFT.BinaryArithmetic.RationalBits

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `AFT.BinaryArithmetic.RationalBits.smallRationalEncodingPolynomial
  pure ()

end

section























/-! # Counted compilation and execution of stored scalar programs

Compilation traverses the given scalar syntax and encodes every literal.
The input syntax and its rational records must already have been generated;
their generation costs are separate from the proved compilation cost.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic

namespace StoredScalarProgram
variable {Scalar Value : Type*}

def compileCounted (encode : ℚ → CountedValue Value) :
    ScalarProgram Scalar → CountedValue (StoredScalarProgram Scalar Value)
  | .rational value =>
      let result := encode value
      ⟨.literal result.value,result.work+1⟩
  | .atom code => ⟨.atom code,1⟩
  | .add first second =>
      let left := compileCounted encode first
      let right := compileCounted encode second
      ⟨.add left.value right.value,left.work+right.work+1⟩
  | .multiply first second =>
      let left := compileCounted encode first
      let right := compileCounted encode second
      ⟨.multiply left.value right.value,left.work+right.work+1⟩
  | .negate term =>
      let input := compileCounted encode term
      ⟨.negate input.value,input.work+1⟩
  | .inverse term =>
      let input := compileCounted encode term
      ⟨.inverse input.value,input.work+1⟩

theorem compileCounted_value (encode : ℚ → CountedValue Value) (program : ScalarProgram Scalar) :
    (compileCounted encode program).value=compile (fun value =>(encode value).value) program := by
  induction program <;> simp_all only [compileCounted,compile]

theorem compileCounted_meaning (encode : ℚ → CountedValue Value) (decode : Value → ℚ)
    (hcode : ∀ value,decode (encode value).value=value) (program : ScalarProgram Scalar) :
    (compileCounted encode program).value.meaning decode=program := by
  rw [compileCounted_value]
  exact compile_meaning _ _ hcode program



end StoredScalarProgram

namespace ScalarProgram
variable {Scalar : Type*}

def binaryCompile (program : ScalarProgram Scalar) : CountedValue (StoredScalarProgram Scalar RationalBits) :=
  StoredScalarProgram.compileCounted (fun value =>
    let result := RationalBits.encodeSmallRational value
    ⟨result.data,result.work⟩) program

theorem binaryCompile_meaning (program : ScalarProgram Scalar) :
    (program.binaryCompile).value.meaning RationalBits.decode=program :=
  StoredScalarProgram.compileCounted_meaning _ _ RationalBits.encodeSmallRational_value program



/-- Both runtime literal compilation and numeric evaluation are included.
No decoding or existential choice is executed by this function. -/
def compileBinaryRun (leaf : Scalar → CountedValue RationalBits) (program : ScalarProgram Scalar) :
    CountedValue RationalBits :=
  let compiled := program.binaryCompile
  let result := compiled.value.binaryRun leaf
  ⟨result.value,compiled.work+result.work+1⟩

theorem compileBinaryRun_value (leaf : Scalar → CountedValue RationalBits) (program : ScalarProgram Scalar) :
    (program.compileBinaryRun leaf).value.decode=program.run (fun code =>(leaf code).value.decode) := by
  simp only [compileBinaryRun,StoredScalarProgram.binaryRun_value,binaryCompile_meaning]



end ScalarProgram
end AFT.RationalNumerics

end

section










namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! # A placed joint score through the complete independent public channel -/
namespace AFT.FiniteDist
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance weightedPoolSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _




variable {Selected Rest Pool Color : Type*} [Fintype Selected] [Fintype Rest]
  [Fintype Pool] [Fintype Color]



def placementPartition (embedding : Selected ↪ Pool) :
    Selected ⊕ {slot : Pool // slot∉Finset.univ.map embedding} ≃ Pool :=
  (Equiv.sumCongr (placementEquiv embedding) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun slot => slot∈Finset.univ.map embedding))

omit [Fintype Pool] in
@[simp] theorem placementPartition_inl (embedding : Selected ↪ Pool) (slot : Selected) :
    placementPartition embedding (.inl slot)=embedding slot := rfl

omit [Fintype Pool] in
@[simp] theorem placementPartition_inr (embedding : Selected ↪ Pool)
    (slot : {slot : Pool // slot∉Finset.univ.map embedding}) :
    placementPartition embedding (.inr slot)=slot.val := rfl





end
end AFT.FiniteDist

end

section










namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! # Exact completion of retained public coordinates by their product laws -/
namespace AFT.FiniteDist
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance completionSumDecEq {A B : Type*} : DecidableEq (A ⊕ B) := Classical.decEq _
local instance completionSubtypeDecEq {A : Type*} {p : A → Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {Selected Pool Color : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]











def completionCoordinate (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : Pool) : FiniteDist Color :=
  match (placementPartition embedding).symm slot with
  | .inl index => pointLaw (selected index)
  | .inr index => reference index.val

omit [Fintype Pool] in
@[simp] theorem completionCoordinate_selected (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : Selected) :
    completionCoordinate embedding reference selected (embedding slot)=pointLaw (selected slot) := by
  unfold completionCoordinate
  rw [← placementPartition_inl embedding slot,Equiv.symm_apply_apply]

omit [Fintype Pool] in
@[simp] theorem completionCoordinate_other (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : {slot : Pool // slot∉Finset.univ.map embedding}) :
    completionCoordinate embedding reference selected slot.val=reference slot.val := by
  unfold completionCoordinate
  rw [← placementPartition_inr embedding slot,Equiv.symm_apply_apply]
  rfl





end
end AFT.FiniteDist

end

section
















namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox




/-! # Exact rational core restriction and canonicalization for pair certificates -/
namespace AFT.RationalNumerics
open scoped BigOperators
variable {Color : Type*} [Fintype Color] [DecidableEq Color]



def rationalCanonicalPair (reference : Color → ℚ) (mass : Color → Color → ℚ) (first second : Color) : ℚ :=
  mass first second-reference first*(∑ x,mass x second)-(∑ y,mass first y)*reference second+
    (∑ x,∑ y,mass x y)*reference first*reference second



noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false















end
end AFT.RationalNumerics

namespace AFT.V7Calibration
open GaussianSource RationalNumerics





noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false





end
end AFT.V7Calibration

end

section

























































namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.PolynomialFamily
end AFT.RationalNumerics.PolynomialFamily
namespace AFT.RationalNumerics.UniformRationalApproximation
end AFT.RationalNumerics.UniformRationalApproximation
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix


/-! A natural-number indexed implementation of finite pair canonicalization. -/
namespace AFT.RationalNumerics
open scoped BigOperators

def rationalCanonicalPairProgram (colors : ℕ) (reference : ℕ → ℚ) (mass : ℕ → ℕ → ℚ)
    (first second : ℕ) : ℚ :=
  mass first second-reference first*(∑ point∈Finset.range colors,mass point second)-
    (∑ point∈Finset.range colors,mass first point)*reference second+
    (∑ first∈Finset.range colors,∑ second∈Finset.range colors,mass first second)*reference first*reference second



end AFT.RationalNumerics

end

section





















/-! Literal magnitude and scalar-leaf heights discharge all intermediate
operand obligations in the counted binary scalar compiler and evaluator. -/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic Polynomial



namespace ScalarProgram
variable {Scalar : Type*}









noncomputable def compilationWorkPolynomial (nodeBound literalBound leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  nodeBound*(RationalBits.smallRationalEncodingPolynomial literalBound+leafWork+
    10000000*(nodeBound*(leafBits+2*literalBound+1)+2)^3+2)+1



end ScalarProgram
end AFT.RationalNumerics

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `AFT.RationalNumerics.ScalarProgram.compilationWorkPolynomial
  pure ()

end

section



/-!
# The current manuscript's public parameter family

These definitions follow `sec:df-parameter-choice`, not the frozen V7
parameters. They are independent of the accuracy order. The least-prime
choice and its polynomial size are proved using Bertrand's theorem.
This file does not claim a polynomial-time implementation of prime search
or of the affine sampler.
-/

namespace CurrentAFT.Parameters

def base (security : ℕ) : ℕ := security + 2
def scale (security : ℕ) : ℕ := base security ^ 8
def primeThreshold (security : ℕ) : ℕ := 2 ^ 16 * scale security ^ 8

theorem base_ge_two (security : ℕ) : 2 ≤ base security := by simp [base]

theorem base_pos (security : ℕ) : 0 < base security := by simp [base]

theorem primeThreshold_eq (security : ℕ) :
    primeThreshold security = 65536 * base security ^ 64 := by
  simp [primeThreshold, scale, ← pow_mul]

/- The checked witness contains both the actual least-prime search value
and its defining properties. Its opacity prevents the kernel from trying
to evaluate that search while comparing finite-alphabet instances. -/
 opaque leastPrimeWitness (security : ℕ) :
    {prime : ℕ // (primeThreshold security ≤ prime ∧ prime.Prime) ∧
      ∀ candidate, primeThreshold security ≤ candidate → candidate.Prime → prime ≤ candidate} :=
  ⟨Nat.find (Nat.exists_infinite_primes (primeThreshold security)),
    Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security)),
    fun _ hthreshold hprime => Nat.find_min' _ ⟨hthreshold, hprime⟩⟩

def modulus (security : ℕ) : ℕ := (leastPrimeWitness security).val

theorem modulus_spec (security : ℕ) :
    primeThreshold security ≤ modulus security ∧ (modulus security).Prime :=
  (leastPrimeWitness security).property.1

theorem modulus_least (security prime : ℕ)
    (hthreshold : primeThreshold security ≤ prime) (hprime : prime.Prime) :
    modulus security ≤ prime :=
  (leastPrimeWitness security).property.2 prime hthreshold hprime



theorem modulus_upper (security : ℕ) :
    modulus security ≤ 2 * primeThreshold security := by
  have hthreshold : primeThreshold security ≠ 0 := by
    rw [primeThreshold_eq]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos (base_pos security) _))
  obtain ⟨prime, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (primeThreshold security) hthreshold
  exact (modulus_least security prime hlower.le hprime).trans hupper

theorem modulus_bounds (security : ℕ) :
    65536 * base security ^ 64 ≤ modulus security ∧
      modulus security ≤ 131072 * base security ^ 64 := by
  constructor
  · simpa only [primeThreshold_eq] using (modulus_spec security).1
  · have h := modulus_upper security
    rw [primeThreshold_eq] at h
    omega

def bodySize (security : ℕ) : ℕ := modulus security * scale security ^ 12
def legCount (security : ℕ) : ℕ := scale security ^ 16
def dimension (security : ℕ) : ℕ := bodySize security + 2 * legCount security
def sourceWidth (security : ℕ) : ℕ := base security
def sourceCutoff (security : ℕ) : ℕ := base security ^ 2
def safeMargin (security : ℕ) : ℕ := 3 * sourceCutoff security
def anchorWidth (security : ℕ) : ℕ := scale security ^ 6

theorem bodySize_eq (security : ℕ) :
    bodySize security = modulus security * base security ^ 96 := by
  simp [bodySize, scale, ← pow_mul]

theorem legCount_eq (security : ℕ) : legCount security = base security ^ 128 := by
  simp [legCount, scale, ← pow_mul]

/-- Explicit polynomial bounds, with constants independent of accuracy. -/
theorem dimension_bounds (security : ℕ) :
    65536 * base security ^ 160 ≤ dimension security ∧
      dimension security ≤ 131074 * base security ^ 160 := by
  have hmod := modulus_bounds security
  have hpowers : base security ^ 128 ≤ base security ^ 160 :=
    Nat.pow_le_pow_right (by have := base_ge_two security; omega) (by omega)
  have hbody := Nat.mul_le_mul_right (base security ^ 96) hmod.1
  have hbodyUpper := Nat.mul_le_mul_right (base security ^ 96) hmod.2
  have hproduct : base security ^ 64 * base security ^ 96 = base security ^ 160 := by
    rw [← pow_add]
  rw [mul_assoc, hproduct] at hbody hbodyUpper
  simp only [dimension, bodySize_eq, legCount_eq]
  constructor <;> omega

/-- Calibration, unlike public parameters, may depend on the fixed order. -/
def calibrationOrder (accuracyOrder : ℕ) : ℕ := 4 * accuracyOrder + 267







-- Residue alphabets depend on this least-prime value. Keep the search
-- abstract during automatic typeclass normalization; explicit rewriting
-- with its definition remains available.
attribute [irreducible] modulus

end CurrentAFT.Parameters

end

section








namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments



/-!
# Canonical density kernels for the current two public-control alphabets

This file realizes `def:df-control-coordinates` as actual finite density
kernels. Primary controls use all residue colors; body controls use the safe
palette. Positive arities are centered in every slot and separately symmetric,
and degree zero is a separate real scalar. These are public controls under
the uncharged proposal at a fixed placement, not independent hidden endpoints.

The explicit single-slot centering projections and distinct-index two-pool
averages below prove their claimed mean identities by finite sums. The paired
lift uses the manuscript's density-to-profile anchor kernel and compensator
density ratio. No actual response stability, protected-cycle independence,
coordinate basis, disjoint-slot multiplication theorem, or sampler complexity
is assumed or asserted here. Reference laws remain parameters until the
current positive-proposal construction supplies them.
-/

namespace CurrentAFT.ControlCoordinates

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) :=
  Classical.decEq _









variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

/-- Density relative to the product reference; the two input alphabets differ. -/
abbrev DensityKernel (primaryDegree bodyDegree : ℕ) :=
  (Fin primaryDegree → Primary) → (Fin bodyDegree → Body) → ℝ

def PrimaryCenteredAt (primary : FiniteDist Primary) {r s : ℕ}
    (index : Fin r) (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ colors centers, ∑ color, primary.weight color *
    kernel (Function.update colors index color) centers = 0

def BodyCenteredAt (body : FiniteDist Body) {r s : ℕ}
    (index : Fin s) (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ colors centers, ∑ center, body.weight center *
    kernel colors (Function.update centers index center) = 0

def SeparatelySymmetric {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ (primaryOrder : Equiv.Perm (Fin r)) (bodyOrder : Equiv.Perm (Fin s)) colors centers,
    kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers

/-- The actual finite coefficient fiber at arity `(r,s)`. No tensor
factorization or independence of the kernel's arguments is required. -/
def canonicalKernels (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ) :
    Submodule ℝ (DensityKernel (Primary := Primary) (Body := Body) r s) where
  carrier := {kernel | (∀ index, PrimaryCenteredAt primary index kernel) ∧
    (∀ index, BodyCenteredAt body index kernel) ∧ SeparatelySymmetric kernel}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      simp
    · intro index colors centers
      simp
    · intro primaryOrder bodyOrder colors centers
      rfl
  add_mem' := by
    intro first second hfirst hsecond
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.1 index colors centers, hsecond.1 index colors centers, add_zero]
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.2.1 index colors centers, hsecond.2.1 index colors centers, add_zero]
    · intro primaryOrder bodyOrder colors centers
      simp only [Pi.add_apply, hfirst.2.2 primaryOrder bodyOrder colors centers,
        hsecond.2.2 primaryOrder bodyOrder colors centers]
  smul_mem' := by
    intro scalar kernel hkernel
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      change (∑ color, primary.weight color *
        (scalar * kernel (Function.update colors index color) centers)) = 0
      calc
        _ = scalar * ∑ color, primary.weight color *
            kernel (Function.update colors index color) centers := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hkernel.1 index colors centers, mul_zero]
    · intro index colors centers
      change (∑ center, body.weight center *
        (scalar * kernel colors (Function.update centers index center))) = 0
      calc
        _ = scalar * ∑ center, body.weight center *
            kernel colors (Function.update centers index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hkernel.2.1 index colors centers, mul_zero]
    · intro primaryOrder bodyOrder colors centers
      simp only [Pi.smul_apply, hkernel.2.2 primaryOrder bodyOrder colors centers]

/-- All positive arities up to the fixed calibration order. -/
abbrev PositiveArity (order : ℕ) :=
  {arity : Fin (order + 1) × Fin (order + 1) //
    1 ≤ arity.1.val + arity.2.val ∧ arity.1.val + arity.2.val ≤ order}

/-- The scalar is the complete degree-zero coefficient; positive degrees are
actual canonical kernel fibers rather than unconstrained coordinate arrays. -/
abbrev CoefficientSpace (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :=
  ℝ × ((arity : PositiveArity order) →
    canonicalKernels primary body arity.val.1.val arity.val.2.val)

instance coefficientSpace_finiteDimensional (primary : FiniteDist Primary)
    (body : FiniteDist Body) (order : ℕ) :
    FiniteDimensional ℝ (CoefficientSpace primary body order) := by infer_instance

















/-- The two different control alphabets have their specified independent
product-reference laws. This says nothing about endpoint independence. -/
def kernelMean (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : ℝ :=
  ((FiniteDist.independent (fun _ : Fin r => primary)).prod
    (FiniteDist.independent (fun _ : Fin s => body))).expectation
      (fun inputs => kernel inputs.1 inputs.2)









/-- The density-to-profile anchor action in the paired lift. The anchor is a
public Markov kernel into the safe body alphabet, not an observed hidden root. -/
def anchorProfile (primary : FiniteDist Primary) (anchor : Primary → FiniteDist Body)
    (score : Primary → ℝ) (center : Body) : ℝ :=
  ∑ color, primary.weight color * score color * (anchor color).weight center



/-- The manuscript's first-order paired density lift, including the true body
reference denominator. -/
def pairedLift (primary : FiniteDist Primary) (body : FiniteDist Body)
    (anchor : Primary → FiniteDist Body) (activation : ℝ) (score : Primary → ℝ)
    (inputs : Primary × Body) : ℝ :=
  score inputs.1 - activation * anchorProfile primary anchor score inputs.2 / body.weight inputs.2





/-- The actual ordered distinct-index average. Its two falling-factorial
normalizers retain the distinct primary-group and ordinary-body populations. -/
def twoPoolUStatistic {r s : ℕ} (primaryPool bodyPool : ℕ)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    DensityKernel (Primary := Primary) (Body := Body) primaryPool bodyPool :=
  fun colors centers =>
    (∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
      kernel (colors ∘ selection.1) (centers ∘ selection.2)) /
        ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ))















end

end CurrentAFT.ControlCoordinates

end

section









/-!
# The actual sign-dependent diffuse endpoint marginals

The interval is the manuscript's inward-anchor interval, and the endpoint
is drawn from the genuine integer trimmed slice, with its varying slice
denominator. The finite seed jointly records the independent public blur
and protected second input. No circular-window replacement is made.
-/

set_option backward.isDefEq.respectTransparency false

namespace CurrentAFT.DiffuseProfiles

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*} [Fintype Seed]

/-- Positive sign uses `[width,2*width)`. Negative sign uses
`[-2*width+1,-width+1)`, the reflection of the same uniform integer set. -/
def intervalStart (positive : Bool) (width : ℕ) (blur : ℤ) : ℤ :=
  (if positive then (width : ℤ) else -2 * (width : ℤ) + 1) + blur

/-- The full diffuse marginal includes public blur and the protected
second leg input before averaging. -/
def profile (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ) : Fin modulus → ℝ :=
  fun color => TrimmedSlice.mixedLaw modulus trim
    (fun seed => intervalStart positive width (blur seed)) second seedLaw.weight width color.val

theorem interval_bound (positive : Bool) (width : ℕ)
    (blur blurBound shift : ℤ) (hblur : |blur| ≤ blurBound)
    (hshift : shift ∈ anchorInterval (intervalStart positive width blur) width) :
    |shift| ≤ 2 * (width : ℤ) + blurBound := by
  simp only [anchorInterval, Finset.mem_Ico, intervalStart] at hshift
  have hb := abs_le.mp hblur
  cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hshift <;>
    apply abs_le.mpr <;> constructor <;> omega

theorem profile_nonneg (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ) (color : Fin modulus) :
    0 ≤ profile modulus width trim positive seedLaw blur second color :=
  TrimmedSlice.mixedLaw_nonneg _ _ _ _ _ _ _ seedLaw.nonneg

theorem profile_mass (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width) (htrim : 0 ≤ trim)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus) :
    ∑ color, profile modulus width trim positive seedLaw blur second color = 1 := by
  exact TrimmedSlice.mixedLaw_palette_mass modulus trim (2 * (width : ℤ) + blurBound)
    secondBound width hwidth.ne' _ second seedLaw.weight seedLaw.sum_one htrim
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega)

theorem profile_upper (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus)
    (color : Fin modulus) :
    profile modulus width trim positive seedLaw blur second color ≤
      1 / ((modulus : ℝ) - (2 * (trim : ℝ) + 2 * width + blurBound + secondBound)) := by
  have h := TrimmedSlice.mixedLaw_le modulus trim (2 * (width : ℤ) + blurBound)
    secondBound _ second seedLaw.weight width hwidth.ne' seedLaw.nonneg seedLaw.sum_one
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega) color.val
  unfold profile
  convert h using 1 <;> push_cast <;> ring

theorem profile_l1_uniform (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width) (htrim : 0 ≤ trim)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus) :
    (∑ color : Fin modulus, |profile modulus width trim positive seedLaw blur second color -
      (modulus : ℝ)⁻¹|) ≤
      2 * (2 * (trim : ℝ) + 2 * width + blurBound + secondBound) / modulus := by
  have h := TrimmedSlice.mixedLaw_palette_l1_le modulus trim (2 * (width : ℤ) + blurBound)
    secondBound width hwidth.ne' _ second seedLaw.weight seedLaw.nonneg seedLaw.sum_one htrim
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega)
  unfold profile
  convert h using 1 <;> push_cast <;> ring

/-- The protected scalar law is the actual clipped Gaussian at the current
public width and strict cutoff, not the older V7 activation model. -/
def scalarLaw (security : ℕ) :
    FiniteDist (GaussianSource.Window (Parameters.sourceCutoff security - 1)) :=
  GaussianSource.windowGaussian (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1)

/-- The public blur is the difference of two independently drawn protected
edge scalars, exactly the one-coordinate body-cycle marginal. -/
def edgeCutoff (security : ℕ) : ℕ := (Parameters.sourceCutoff security - 1) / 2

def edgeLaw (security : ℕ) : FiniteDist (GaussianSource.Window (edgeCutoff security)) :=
  GaussianSource.windowGaussian (Parameters.sourceWidth security) (edgeCutoff security)

abbrev ActualSeed (security : ℕ) :=
  (GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security)) ×
    GaussianSource.Window (Parameters.sourceCutoff security - 1)

def actualSeedLaw (security : ℕ) : FiniteDist (ActualSeed security) :=
  ((edgeLaw security).prod (edgeLaw security)).prod (scalarLaw security)

def actualBlur (security : ℕ) (seed : ActualSeed security) : ℤ := seed.1.1 - seed.1.2

def actualSecond (security : ℕ) (seed : ActualSeed security) : ℤ := seed.2

def actualProfile (security : ℕ) (positive : Bool) : Fin (Parameters.modulus security) → ℝ :=
  profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)

theorem actualBlur_bound (security : ℕ) (seed : ActualSeed security) :
    |actualBlur security seed| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h1 := Finset.mem_Icc.mp seed.1.1.property
  have h2 := Finset.mem_Icc.mp seed.1.2.property
  have hcut : 0 < Parameters.sourceCutoff security := by
    unfold Parameters.sourceCutoff
    exact pow_pos (Parameters.base_pos security) _
  unfold actualBlur edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem actualSecond_bound (security : ℕ) (seed : ActualSeed security) :
    |actualSecond security seed| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h := Finset.mem_Icc.mp seed.2.property
  have hcut : 0 < Parameters.sourceCutoff security := by
    unfold Parameters.sourceCutoff
    exact pow_pos (Parameters.base_pos security) _
  unfold actualSecond
  apply abs_le.mpr
  constructor <;> omega

/-- The manuscript's conservative deletion length. -/
def deletion (security : ℕ) : ℕ :=
  2 + 2 * Parameters.anchorWidth security + 2 * Parameters.sourceCutoff security

theorem anchorWidth_eq (security : ℕ) : Parameters.anchorWidth security =
    Parameters.base security ^ 48 := by
  simp [Parameters.anchorWidth, Parameters.scale, ← pow_mul]

theorem deletion_clearance (security : ℕ) : deletion security < Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := (by have := Parameters.base_ge_two security; omega)
  have ha : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    rw [anchorWidth_eq]
    exact Nat.pow_le_pow_right hb (by omega)
  have hc : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hp : 1 ≤ Parameters.base security ^ 64 := one_le_pow₀ hb
  have hq := (Parameters.modulus_bounds security).1
  unfold deletion
  omega

 theorem actual_clearance (security : ℕ) :
    2 * (1 : ℤ) + 2 * Parameters.anchorWidth security +
      ((Parameters.sourceCutoff security : ℤ) - 1) +
        ((Parameters.sourceCutoff security : ℤ) - 1) < Parameters.modulus security := by
  have h := deletion_clearance security
  unfold deletion at h
  omega

theorem actualProfile_mass (security : ℕ) (positive : Bool) :
    ∑ color, actualProfile security positive color = 1 := by
  apply profile_mass _ _ _ _ _ _ _
    ((Parameters.sourceCutoff security : ℤ) - 1)
      ((Parameters.sourceCutoff security : ℤ) - 1)
  · rw [anchorWidth_eq]
    exact pow_pos (Parameters.base_pos security) _
  · norm_num
  · exact actualBlur_bound security
  · exact actualSecond_bound security
  · exact actual_clearance security

theorem actualProfile_upper (security : ℕ) (positive : Bool)
    (color : Fin (Parameters.modulus security)) :
    actualProfile security positive color ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  have h := profile_upper (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)
    ((Parameters.sourceCutoff security : ℤ) - 1) ((Parameters.sourceCutoff security : ℤ) - 1)
    (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _)
    (actualBlur_bound security) (actualSecond_bound security) (actual_clearance security) color
  apply h.trans
  apply one_div_le_one_div_of_le
  · exact sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  · simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_natCast,
      Int.cast_one]
    linarith

theorem actualProfile_l1_uniform (security : ℕ) (positive : Bool) :
    (∑ color : Fin (Parameters.modulus security), |actualProfile security positive color -
      (Parameters.modulus security : ℝ)⁻¹|) ≤
      2 * (deletion security : ℝ) / Parameters.modulus security := by
  have h := profile_l1_uniform (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)
    ((Parameters.sourceCutoff security : ℤ) - 1) ((Parameters.sourceCutoff security : ℤ) - 1)
    (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _) (by norm_num)
    (actualBlur_bound security) (actualSecond_bound security) (actual_clearance security)
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    Int.cast_one]
  linarith

/-- The marked activation is one half of the actual clipped scalar's zero atom. -/
def activation (security : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (scalarLaw security).weight
    (GaussianSource.windowZero (Parameters.sourceCutoff security - 1))

theorem activation_pos (security : ℕ) : 0 < activation security :=
  mul_pos (by norm_num) (GaussianSource.windowGaussian_positive _ _ _)

theorem activation_le_half (security : ℕ) : activation security ≤ 1 / 2 := by
  have h := Finset.single_le_sum (f := (scalarLaw security).weight)
    (fun point _ => (scalarLaw security).nonneg point)
    (Finset.mem_univ (GaussianSource.windowZero (Parameters.sourceCutoff security - 1)))
  rw [FiniteDist.sum_one] at h
  unfold activation
  linarith

theorem activation_lower (security : ℕ) :
    1 / (2 * (1 + 2 / Real.pi) * Parameters.base security) ≤ activation security := by
  have h := GaussianSource.windowGaussian_zero_lower (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1)
    (by exact_mod_cast (show 1 ≤ Parameters.base security by
      have := Parameters.base_ge_two security; omega))
  change 1 / (2 * (1 + 2 / Real.pi) * Parameters.base security) ≤
    (1 / 2 : ℝ) * (GaussianSource.windowGaussian (Parameters.sourceWidth security)
      (Parameters.sourceCutoff security - 1)).weight _
  calc
    _ = (1 / 2 : ℝ) * (1 / ((1 + 2 / Real.pi) * Parameters.sourceWidth security)) := by
      simp only [Parameters.sourceWidth, one_div, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The concrete rank-one numerator of the first histogram response. -/
def signProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (1 - activation security) *
    (actualProfile security true color - actualProfile security false color)

theorem signProfile_mass (security : ℕ) : ∑ color, signProfile security color = 0 := by
  simp only [signProfile, ← Finset.mul_sum, Finset.sum_sub_distrib, actualProfile_mass,
    sub_self, mul_zero]

theorem signProfile_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    |signProfile security color| ≤ 1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  have h1 := actualProfile_upper security true color
  have h2 := actualProfile_upper security false color
  have hn1 := profile_nonneg (Parameters.modulus security) (Parameters.anchorWidth security) 1 true
    (actualSeedLaw security) (actualBlur security) (actualSecond security) color
  have hn2 := profile_nonneg (Parameters.modulus security) (Parameters.anchorWidth security) 1 false
    (actualSeedLaw security) (actualBlur security) (actualSecond security) color
  change 0 ≤ actualProfile security true color at hn1
  change 0 ≤ actualProfile security false color at hn2
  have ha0 := (activation_pos security).le
  have ha1 := activation_le_half security
  rw [signProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
  have hdiff : |actualProfile security true color - actualProfile security false color| ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - activation security ≤ 1)
    (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff)

theorem signProfile_l1 (security : ℕ) :
    (∑ color, |signProfile security color|) ≤
      4 * (deletion security : ℝ) / Parameters.modulus security := by
  have hdiff := Finset.sum_le_sum (s := Finset.univ) (fun color _ =>
    abs_sub_le (actualProfile security true color) ((Parameters.modulus security : ℝ)⁻¹)
      (actualProfile security false color))
  simp_rw [abs_sub_comm ((Parameters.modulus security : ℝ)⁻¹)] at hdiff
  rw [Finset.sum_add_distrib] at hdiff
  have h1 := actualProfile_l1_uniform security true
  have h2 := actualProfile_l1_uniform security false
  have ha0 := (activation_pos security).le
  have ha1 := activation_le_half security
  calc
    _ = (1 - activation security) *
        ∑ color, |actualProfile security true color - actualProfile security false color| := by
      simp only [signProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security),
        Finset.mul_sum]
    _ ≤ ∑ color, |actualProfile security true color - actualProfile security false color| := by
      nlinarith [Finset.sum_nonneg (fun color (_ : color ∈ Finset.univ) =>
        abs_nonneg (actualProfile security true color - actualProfile security false color))]
    _ ≤ _ := (hdiff.trans (add_le_add h1 h2)).trans_eq (by ring)

end

end CurrentAFT.DiffuseProfiles

end

end

section

section







/-!
# The actual current rank-one first response

The sign profile and activation in this file are the actual trimmed-slice
diffuse profiles and clipped Gaussian zero atom of `DiffuseProfiles`.
The elementary estimates for these concrete distributions, together with
the current public sizes, imply the perturbation and inverse bounds.

The reference primary law only supplies its normalized mass and the
elementary lower atom bound. No response norm or inverse is assumed.
The weighted norm is stated as its genuine finite square sum, without
introducing a potentially incompatible norm instance on the palette.
The physical paired-channel factorization is a separate obligation.
-/

namespace CurrentAFT.FirstResponse

open AFT DiffuseProfiles
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff DiffuseProfiles.actualProfile DiffuseProfiles.signProfile
  DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

/-- Comparison with the exact palette midpoint, using doubled integer
coordinates so no division or rounding convention is implicit. -/
def anchorSign (security : ℕ) (color : Palette security) : ℝ :=
  if 2 * color.val < Parameters.modulus security - 1 then -1
  else if Parameters.modulus security - 1 < 2 * color.val then 1 else 0

theorem anchorSign_abs_le_one (security : ℕ) (color : Palette security) :
    |anchorSign security color| ≤ 1 := by
  unfold anchorSign
  split_ifs <;> norm_num

theorem modulus_pos (security : ℕ) : (0 : ℝ) < Parameters.modulus security := by
  exact_mod_cast (Parameters.modulus_spec security).2.pos

theorem base_pos (security : ℕ) : (0 : ℝ) < Parameters.base security := by
  exact_mod_cast Parameters.base_pos security

/-- A direct bound on the actual deletion length, using the current
anchor width `base^48` and source cutoff `base^2`. -/
theorem deletion_le_six_anchor (security : ℕ) :
    deletion security ≤ 6 * Parameters.base security ^ 48 := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hconstant : 1 ≤ Parameters.base security ^ 48 := one_le_pow₀ hb
  have hcutoff : Parameters.base security ^ 2 ≤ Parameters.base security ^ 48 :=
    Nat.pow_le_pow_right hb (by omega)
  simp only [deletion, anchorWidth_eq, Parameters.sourceCutoff]
  omega

/-- This quantitative budget comes from the actual modulus lower bound;
it is stronger than the smallness needed for a stable first inverse. -/
theorem deletion_budget (security : ℕ) :
    256 * deletion security * Parameters.base security ^ 12 ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  calc
    _ ≤ 256 * (6 * Parameters.base security ^ 48) * Parameters.base security ^ 12 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (deletion_le_six_anchor security))
    _ = 1536 * (Parameters.base security ^ 48 * Parameters.base security ^ 12) := by ring
    _ = 1536 * Parameters.base security ^ 60 := by rw [← pow_add]
    _ ≤ 65536 * Parameters.base security ^ 64 :=
      Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right hb (by omega))
    _ ≤ _ := (Parameters.modulus_bounds security).1

theorem two_deletion_le_modulus (security : ℕ) :
    2 * deletion security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : 1 ≤ Parameters.base security ^ 12 := one_le_pow₀ hb
  calc
    2 * deletion security ≤ (256 * deletion security) * Parameters.base security ^ 12 :=
      (by omega : 2 * deletion security ≤ 256 * deletion security).trans
        (Nat.le_mul_of_pos_right _ (by omega))
    _ ≤ _ := deletion_budget security

/-- A simpler consequence useful for the proposal's pointwise losses. -/
theorem deletion_linear_budget (security : ℕ) :
    64 * deletion security * Parameters.base security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : Parameters.base security ≤ Parameters.base security ^ 12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 12 by omega)
  exact (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num : 64 ≤ 256)) hpower).trans
    (deletion_budget security)

/-- The current clipped Gaussian activation has the elementary inverse
scale `4*base`; this is derived from its actual zero-atom estimate. -/
theorem activation_lower_simple (security : ℕ) :
    1 / (4 * (Parameters.base security : ℝ)) ≤ activation security := by
  have hb := base_pos security
  have hpi : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi
  apply le_trans _ (activation_lower security)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem activation_inverse_le (security : ℕ) :
    1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
  have hb := base_pos security
  have h := one_div_le_one_div_of_le
    (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ))) (activation_lower_simple security)
  simpa only [one_div_one_div] using h

theorem signProfile_l1_le_half_activation (security : ℕ) :
    (∑ color, |signProfile security color|) ≤ activation security / 2 := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : Parameters.base security ≤ Parameters.base security ^ 12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 12 by omega)
  have hbudgetNat : 32 * deletion security * Parameters.base security ≤ Parameters.modulus security :=
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num : 32 ≤ 256)) hpower).trans
      (deletion_budget security)
  have hbudget : 32 * (deletion security : ℝ) * Parameters.base security ≤ Parameters.modulus security := by
    exact_mod_cast hbudgetNat
  have hq := modulus_pos security
  have hb0 := base_pos security
  calc
    _ ≤ 4 * (deletion security : ℝ) / Parameters.modulus security := signProfile_l1 security
    _ ≤ 1 / (8 * (Parameters.base security : ℝ)) := by
      apply (div_le_div_iff₀ hq (by positivity)).mpr
      nlinarith only [hbudget]
    _ = (1 / (4 * (Parameters.base security : ℝ))) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (activation_lower_simple security) (by norm_num)

theorem signProfile_l1_lt_activation (security : ℕ) :
    (∑ color, |signProfile security color|) < activation security := by
  have h := signProfile_l1_le_half_activation security
  have ha := activation_pos security
  linarith





/-- This response uses the actual current diffuse profile, not an
uninterpreted perturbation parameter or the older V7 physical model. -/
def response (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  primaryRankOperator (activation security) (signProfile security) (profileSignMap (anchorSign security))

def responseEquiv (security : ℕ) : (Palette security → ℝ) ≃ₗ[ℝ] (Palette security → ℝ) :=
  finitePrimaryRankEquiv (activation security) (signProfile security) (anchorSign security)
    (anchorSign_abs_le_one security) (signProfile_l1_lt_activation security)

theorem responseEquiv_forward (security : ℕ) (profile : Palette security → ℝ) :
    responseEquiv security profile = response security profile := rfl



theorem response_preserves_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ color, response security profile color) = ∑ color, profile color := by
  simp only [response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, signProfile_mass, mul_zero, add_zero]

theorem response_inverse_preserves_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ color, (responseEquiv security).symm profile color) = ∑ color, profile color := by
  have h := response_preserves_mass security ((responseEquiv security).symm profile)
  have hresponse : response security ((responseEquiv security).symm profile) = profile :=
    (responseEquiv security).apply_symm_apply profile
  rw [hresponse] at h
  exact h.symm

theorem signProfile_majorant (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (color : Palette security) : |signProfile security color| ≤ 4 * primary color := by
  have hq := modulus_pos security
  have hdelete : 2 * (deletion security : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast two_deletion_le_modulus security
  calc
    _ ≤ 1 / ((Parameters.modulus security : ℝ) - deletion security) := signProfile_upper security color
    _ ≤ 1 / ((Parameters.modulus security : ℝ) / 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = 4 * (1 / (2 * (Parameters.modulus security : ℝ))) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (hprimary color) (by norm_num)

 theorem actual_correction_coefficient_le (security : ℕ) :
    4 * (∑ color, |signProfile security color|) / activation security ^ 2 ≤
      1 / (Parameters.base security : ℝ) ^ 10 := by
  have hq := modulus_pos security
  have hb := base_pos security
  have hsum0 : 0 ≤ ∑ color, |signProfile security color| := Finset.sum_nonneg (fun color _ => abs_nonneg _)
  have hinv := activation_inverse_le security
  have hinv0 : 0 ≤ 1 / activation security := (one_div_pos.mpr (activation_pos security)).le
  have hinvsq : (1 / activation security) ^ 2 ≤ (4 * (Parameters.base security : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hinv0 hinv _
  have hsum := mul_le_mul_of_nonneg_left (signProfile_l1 security) (by norm_num : (0 : ℝ) ≤ 4)
  have hbudget : 256 * (deletion security : ℝ) * (Parameters.base security : ℝ) ^ 12 ≤
      Parameters.modulus security := by exact_mod_cast deletion_budget security
  calc
    _ = (4 * ∑ color, |signProfile security color|) * (1 / activation security) ^ 2 := by ring
    _ ≤ (16 * (deletion security : ℝ) / Parameters.modulus security) *
        (4 * (Parameters.base security : ℝ)) ^ 2 := by
      apply mul_le_mul _ hinvsq (sq_nonneg _) (by positivity)
      exact hsum.trans_eq (by ring)
    _ = (256 * (deletion security : ℝ) * (Parameters.base security : ℝ) ^ 2) /
        Parameters.modulus security := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      nlinarith only [hbudget]

/-- The concrete first response has squared perturbation at most
`base^-10` in every normalized reference with the stated atom bound. -/
theorem response_defect_square_le (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    profileSquareNorm primary (response security profile - profile) ≤
      (1 / (Parameters.base security : ℝ) ^ 10) * profileSquareNorm primary profile := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  have hdifference : response security profile - profile =
      (signFunctional (anchorSign security) profile / activation security) • signProfile security := by
    change primaryRankOperator (activation security) (signProfile security)
      (profileSignMap (anchorSign security)) profile - profile = _
    rw [primaryRankOperator_apply]
    change profile + ((activation security)⁻¹ * signFunctional (anchorSign security) profile) •
      signProfile security - profile = _
    rw [show (activation security)⁻¹ * signFunctional (anchorSign security) profile =
      signFunctional (anchorSign security) profile / activation security by ring]
    abel
  rw [hdifference]
  exact (rankCorrection_profileSquareNorm_le primary (signProfile security) (anchorSign security) profile
    (activation security) 4 hp hmass (anchorSign_abs_le_one security) (by norm_num)
    (signProfile_majorant security primary hprimary)).trans
      (mul_le_mul_of_nonneg_right (actual_correction_coefficient_le security)
        (profileSquareNorm_nonneg primary profile (fun color => (hp color).le)))

/-- The operator-norm statement written directly in its genuine
weighted profile norm: the defect is at most `base^-5`. -/
theorem response_defect_norm_le (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    Real.sqrt (profileSquareNorm primary (response security profile - profile)) ≤
      Real.sqrt (profileSquareNorm primary profile) / (Parameters.base security : ℝ) ^ 5 := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow, Real.sq_sqrt hn, ← pow_mul]
  convert response_defect_square_le security primary hprimary hmass profile using 1
  ring

/-- The actual explicit inverse has norm at most two in the same
weighted profile norm, uniformly in the reference primary law. -/
theorem response_inverse_norm_le_two (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    Real.sqrt (profileSquareNorm primary ((responseEquiv security).symm profile)) ≤
      2 * Real.sqrt (profileSquareNorm primary profile) := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  let preimage := (responseEquiv security).symm profile
  have hresponse : response security preimage = profile := (responseEquiv security).apply_symm_apply profile
  have hdefect := response_defect_norm_le security primary hprimary hmass preimage
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by linarith
  have hpower : (2 : ℝ) ≤ (Parameters.base security : ℝ) ^ 5 :=
    hb2.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 5 by omega))
  have hdefectHalf :
      Real.sqrt (profileSquareNorm primary (response security preimage - preimage)) ≤
        Real.sqrt (profileSquareNorm primary preimage) / 2 :=
    hdefect.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hpower)
  have hsplit : preimage = profile + -(response security preimage - preimage) := by rw [hresponse]; abel
  have htriangle := profileSquareNorm_sqrt_add_le primary profile
    (-(response security preimage - preimage)) hp
  rw [← hsplit] at htriangle
  have hnegative : profileSquareNorm primary (-(response security preimage - preimage)) =
      profileSquareNorm primary (response security preimage - preimage) := by
    simp only [profileSquareNorm, Pi.neg_apply, neg_sq]
  rw [hnegative] at htriangle
  change Real.sqrt (profileSquareNorm primary preimage) ≤ _
  linarith

end

end CurrentAFT.FirstResponse

end

section





/-!
# The actual inward anchor kernel

The index is uniform on `Fin A`, representing the integer interval
`A,...,2*A-1`. Its sign is inward away from the palette midpoint;
at the midpoint a fresh fair Boolean chooses either sign. The smoothed
kernel adds an independent draw from the actual protected scalar law.

Probability normalization, safe support, and column height are derived
from these finite draws. They are not assumptions on an abstract kernel.
-/

namespace CurrentAFT.InwardAnchor

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.scalarLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Index (security : ℕ) := Fin (Parameters.anchorWidth security)
abbrev ScalarSample (security : ℕ) := GaussianSource.Window (Parameters.sourceCutoff security - 1)

theorem anchorWidth_pos (security : ℕ) : 0 < Parameters.anchorWidth security := by
  rw [anchorWidth_eq]
  exact pow_pos (Parameters.base_pos security) _

local instance anchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(anchorWidth_pos security).ne'⟩

theorem sourceCutoff_pos (security : ℕ) : 0 < Parameters.sourceCutoff security := by
  unfold Parameters.sourceCutoff
  exact pow_pos (Parameters.base_pos security) _

theorem four_cutoffs_le_anchor (security : ℕ) :
    4 * Parameters.sourceCutoff security ≤ Parameters.anchorWidth security := by
  have hb : 2 ≤ Parameters.base security := Parameters.base_ge_two security
  have hb1 : 1 ≤ Parameters.base security := by omega
  have hb2 : 4 ≤ Parameters.base security ^ 2 := by nlinarith
  have hfactor : 4 ≤ Parameters.base security ^ 46 :=
    hb2.trans (Nat.pow_le_pow_right hb1 (by omega))
  rw [anchorWidth_eq, Parameters.sourceCutoff]
  calc
    _ ≤ Parameters.base security ^ 46 * Parameters.base security ^ 2 :=
      Nat.mul_le_mul_right _ hfactor
    _ = _ := by rw [← pow_add]

theorem modulus_room (security : ℕ) :
    6 * Parameters.anchorWidth security + 1 ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have ha : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    rw [anchorWidth_eq]
    exact Nat.pow_le_pow_right hb (by omega)
  have hpower : 1 ≤ Parameters.base security ^ 64 := one_le_pow₀ hb
  have hq := (Parameters.modulus_bounds security).1
  omega

/-- The Boolean is read only at the midpoint. -/
def positiveDirection (security : ℕ) (color : Palette security) (coin : Bool) : Bool :=
  if 2 * color.val < Parameters.modulus security - 1 then false
  else if Parameters.modulus security - 1 < 2 * color.val then true else coin

def offset (security : ℕ) (index : Index security) : ℤ :=
  (Parameters.anchorWidth security : ℤ) + index.val

def integerPoint (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ) : ℤ :=
  (Parameters.modulus security : ℤ) - 1 - color.val +
    (if positiveDirection security color coin then offset security index else -offset security index) + shift

theorem direction_left (security : ℕ) (color : Palette security) (coin : Bool)
    (hdirection : positiveDirection security color coin = false) :
    2 * (color.val : ℤ) ≤ (Parameters.modulus security : ℤ) - 1 := by
  have hq := (Parameters.modulus_spec security).2.pos
  by_contra h
  have hhigh : Parameters.modulus security - 1 < 2 * color.val := by omega
  have hlow : ¬2 * color.val < Parameters.modulus security - 1 := by omega
  simp [positiveDirection, hlow, hhigh] at hdirection

theorem direction_right (security : ℕ) (color : Palette security) (coin : Bool)
    (hdirection : positiveDirection security color coin = true) :
    (Parameters.modulus security : ℤ) - 1 ≤ 2 * (color.val : ℤ) := by
  have hq := (Parameters.modulus_spec security).2.pos
  by_contra h
  have hlow : 2 * color.val < Parameters.modulus security - 1 := by omega
  simp [positiveDirection, hlow] at hdirection

/-- All anchor samples remain safe after every protected scalar shift. -/
theorem integerPoint_safe (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    (Parameters.safeMargin security : ℤ) ≤ integerPoint security color coin index shift ∧
      integerPoint security color coin index shift <
        (Parameters.modulus security : ℤ) - Parameters.safeMargin security := by
  have hroom : 6 * (Parameters.anchorWidth security : ℤ) + 1 ≤ Parameters.modulus security := by
    exact_mod_cast modulus_room security
  have hfour : 4 * (Parameters.sourceCutoff security : ℤ) ≤ Parameters.anchorWidth security := by
    exact_mod_cast four_cutoffs_le_anchor security
  have hmargin : (Parameters.safeMargin security : ℤ) +
      ((Parameters.sourceCutoff security : ℤ) - 1) ≤ Parameters.anchorWidth security := by
    rw [Parameters.safeMargin]
    push_cast
    omega
  have hindex := index.isLt
  have hoffsetLower : (Parameters.anchorWidth security : ℤ) ≤ offset security index := by
    unfold offset
    omega
  have hoffsetUpper : offset security index < 2 * (Parameters.anchorWidth security : ℤ) := by
    unfold offset
    omega
  cases hdirection : positiveDirection security color coin
  · simpa only [integerPoint, hdirection, Bool.false_eq_true, if_false, sub_eq_add_neg] using
      publicAnchor_left_safe (Parameters.modulus security) (Parameters.anchorWidth security) color.val
        (offset security index) shift (Parameters.safeMargin security)
        ((Parameters.sourceCutoff security : ℤ) - 1) hroom (Int.natCast_nonneg _)
        (direction_left security color coin hdirection) hoffsetLower hoffsetUpper hshift hmargin
  · simpa only [integerPoint, hdirection, if_true] using
      publicAnchor_right_safe (Parameters.modulus security) (Parameters.anchorWidth security) color.val
        (offset security index) shift (Parameters.safeMargin security)
        ((Parameters.sourceCutoff security : ℤ) - 1) hroom (by exact_mod_cast color.isLt)
        (direction_right security color coin hdirection) hoffsetLower hoffsetUpper hshift hmargin

def SafeColor (security : ℕ) (color : Palette security) : Prop :=
  (Parameters.safeMargin security : ℤ) ≤ color.val ∧
    (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security

/-- Reduction to the actual finite palette is performed only after the
integer support theorem; it never wraps an unsafe anchor around the palette. -/
def point (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) : Palette security :=
  ⟨(integerPoint security color coin index shift).toNat, by
    have hs := integerPoint_safe security color coin index shift hshift
    have hm : (0 : ℤ) ≤ Parameters.safeMargin security := Int.natCast_nonneg _
    omega⟩

theorem point_value (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    ((point security color coin index shift hshift).val : ℤ) =
      integerPoint security color coin index shift := by
  have hs := integerPoint_safe security color coin index shift hshift
  have hn : 0 ≤ integerPoint security color coin index shift :=
    (Int.natCast_nonneg _).trans hs.1
  exact Int.toNat_of_nonneg hn

theorem point_safe (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    SafeColor security (point security color coin index shift hshift) := by
  unfold SafeColor
  rw [point_value]
  exact integerPoint_safe security color coin index shift hshift

theorem point_index_injective (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    Function.Injective (fun index => point security color coin index shift hshift) := by
  intro first second hequal
  have h := congrArg (fun output : Palette security => (output.val : ℤ)) hequal
  change ((point security color coin first shift hshift).val : ℤ) =
    ((point security color coin second shift hshift).val : ℤ) at h
  rw [point_value, point_value] at h
  unfold integerPoint offset at h
  split_ifs at h <;> apply Fin.ext <;> omega

/-- One sign column is the pushforward of the actual uniform anchor index. -/
def fixedCoinLaw (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    FiniteDist (Palette security) :=
  (FiniteDist.uniform (Index security)).map (fun index => point security color coin index shift hshift)

/-- The complete midpoint convention uses one independent fair coin. -/
def shiftedAnchorLaw (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    FiniteDist (Palette security) :=
  (FiniteDist.uniform Bool).mix (fun coin => fixedCoinLaw security color coin shift hshift)





theorem scalar_bound (security : ℕ) (sample : ScalarSample security) :
    |(sample : ℤ)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h := Finset.mem_Icc.mp sample.property
  have hcut := sourceCutoff_pos security
  apply abs_le.mpr
  constructor <;> omega

/-- The current smoothed anchor is convolution by an independent actual
protected Gaussian scalar, implemented by its actual finite source draw. -/
def smoothedAnchorLaw (security : ℕ) (color : Palette security) : FiniteDist (Palette security) :=
  (scalarLaw security).mix (fun sample => shiftedAnchorLaw security color sample (scalar_bound security sample))



theorem smoothedAnchorLaw_mass (security : ℕ) (color : Palette security) :
    ∑ output, (smoothedAnchorLaw security color).weight output = 1 := FiniteDist.sum_one _

theorem fixedCoinLaw_zero_outside (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) (hunsafe : ¬SafeColor security output) :
    (fixedCoinLaw security color coin shift hshift).weight output = 0 := by
  rw [fixedCoinLaw, FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro index _
  have hne : point security color coin index shift hshift ≠ output := by
    intro hequal
    apply hunsafe
    rw [← hequal]
    exact point_safe security color coin index shift hshift
  simp only [if_neg hne]

theorem shiftedAnchorLaw_zero_outside (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) (hunsafe : ¬SafeColor security output) :
    (shiftedAnchorLaw security color shift hshift).weight output = 0 := by
  simp only [shiftedAnchorLaw, FiniteDist.mix_weight,
    fixedCoinLaw_zero_outside security color _ shift hshift output hunsafe, mul_zero, Finset.sum_const_zero]



theorem smoothedAnchorLaw_zero_outside (security : ℕ) (color output : Palette security)
    (hunsafe : ¬SafeColor security output) : (smoothedAnchorLaw security color).weight output = 0 := by
  simp only [smoothedAnchorLaw, FiniteDist.mix_weight,
    shiftedAnchorLaw_zero_outside security color _ _ output hunsafe, mul_zero, Finset.sum_const_zero]

theorem fixedCoinLaw_height (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (fixedCoinLaw security color coin shift hshift).weight output ≤
      1 / (Parameters.anchorWidth security : ℝ) := by
  rw [fixedCoinLaw, FiniteDist.map_weight]
  by_cases hexists : ∃ index, point security color coin index shift hshift = output
  · obtain ⟨index, hindex⟩ := hexists
    have heq (other : Index security) : point security color coin other shift hshift = output ↔ other = index := by
      constructor
      · intro hother
        exact point_index_injective security color coin shift hshift (hother.trans hindex.symm)
      · rintro rfl
        exact hindex
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true, FiniteDist.uniform_weight,
      Fintype.card_fin, one_div]
    exact le_rfl
  · have hnone (index : Index security) : point security color coin index shift hshift ≠ output :=
      fun hpoint => hexists ⟨index, hpoint⟩
    simp only [if_neg (hnone _), Finset.sum_const_zero]
    positivity

theorem shiftedAnchorLaw_height (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (shiftedAnchorLaw security color shift hshift).weight output ≤
      1 / (Parameters.anchorWidth security : ℝ) := by
  rw [shiftedAnchorLaw, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun coin _ => mul_le_mul_of_nonneg_left
        (fixedCoinLaw_height security color coin shift hshift output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]



theorem smoothedAnchorLaw_height (security : ℕ) (color output : Palette security) :
    (smoothedAnchorLaw security color).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  rw [smoothedAnchorLaw, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ sample, (scalarLaw security).weight sample * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun sample _ => mul_le_mul_of_nonneg_left
        (shiftedAnchorLaw_height security color sample (scalar_bound security sample) output)
          (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

 theorem integer_fiber_sum_le_one (security : ℕ) (value : ℤ) :
    (∑ color : Palette security, if (color.val : ℤ) = value then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hexists : ∃ color : Palette security, (color.val : ℤ) = value
  · obtain ⟨color, hcolor⟩ := hexists
    have heq (other : Palette security) : (other.val : ℤ) = value ↔ other = color := by
      constructor
      · intro hother
        apply Fin.ext
        omega
      · rintro rfl
        exact hcolor
    simp [heq]
  · have hnone (color : Palette security) : ¬(color.val : ℤ) = value :=
      fun hcolor => hexists ⟨color, hcolor⟩
    simp [hnone]

/-- For a fixed index and coin, each output can arise from at most one
input in each of the two inward directions. This includes the midpoint. -/
theorem point_row_count_le_two (security : ℕ) (coin : Bool) (index : Index security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color : Palette security,
      if point security color coin index shift hshift = output then (1 : ℝ) else 0) ≤ 2 := by
  let positiveInput : ℤ := (Parameters.modulus security : ℤ) - 1 + offset security index + shift - output.val
  let negativeInput : ℤ := (Parameters.modulus security : ℤ) - 1 - offset security index + shift - output.val
  have hpoint (color : Palette security) :
      (if point security color coin index shift hshift = output then (1 : ℝ) else 0) ≤
        (if (color.val : ℤ) = positiveInput then (1 : ℝ) else 0) +
          (if (color.val : ℤ) = negativeInput then (1 : ℝ) else 0) := by
    by_cases hequal : point security color coin index shift hshift = output
    · have hvalue := congrArg (fun point : Palette security => (point.val : ℤ)) hequal
      change ((point security color coin index shift hshift).val : ℤ) = (output.val : ℤ) at hvalue
      rw [point_value] at hvalue
      unfold integerPoint at hvalue
      cases hdirection : positiveDirection security color coin
      · simp only [hdirection, Bool.false_eq_true, if_false] at hvalue
        have hinput : (color.val : ℤ) = negativeInput := by dsimp [negativeInput]; omega
        simp only [if_pos hequal, if_pos hinput]
        split_ifs <;> norm_num
      · simp only [hdirection, if_true] at hvalue
        have hinput : (color.val : ℤ) = positiveInput := by dsimp [positiveInput]; omega
        simp only [if_pos hequal, if_pos hinput]
        split_ifs <;> norm_num
    · simp only [if_neg hequal]
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ color : Palette security,
        ((if (color.val : ℤ) = positiveInput then (1 : ℝ) else 0) +
          (if (color.val : ℤ) = negativeInput then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith [integer_fiber_sum_le_one security positiveInput,
        integer_fiber_sum_le_one security negativeInput]

/-- The actual sign-column has row sum at most two, with no loss
depending on the palette or anchor width. -/
theorem fixedCoinLaw_row_sum_le_two (security : ℕ) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color, (fixedCoinLaw security color coin shift hshift).weight output) ≤ 2 := by
  simp only [fixedCoinLaw, FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin]
  rw [Finset.sum_comm]
  calc
    _ = ∑ index : Index security, (Parameters.anchorWidth security : ℝ)⁻¹ *
        ∑ color : Palette security,
          if point security color coin index shift hshift = output then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      split_ifs <;> simp
    _ ≤ ∑ _index : Index security, (Parameters.anchorWidth security : ℝ)⁻¹ * 2 :=
      Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left
        (point_row_count_le_two security coin index shift hshift output) (by positivity))
    _ = 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have ha : (Parameters.anchorWidth security : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (anchorWidth_pos security).ne'
      field_simp

theorem shiftedAnchorLaw_row_sum_le_two (security : ℕ)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color, (shiftedAnchorLaw security color shift hshift).weight output) ≤ 2 := by
  simp only [shiftedAnchorLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * 2 :=
      Finset.sum_le_sum (fun coin _ => mul_le_mul_of_nonneg_left
        (fixedCoinLaw_row_sum_le_two security coin shift hshift output) (FiniteDist.nonneg _ _))
    _ = 2 := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]



theorem smoothedAnchorLaw_row_sum_le_two (security : ℕ) (output : Palette security) :
    (∑ color, (smoothedAnchorLaw security color).weight output) ≤ 2 := by
  simp only [smoothedAnchorLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ sample, (scalarLaw security).weight sample * 2 :=
      Finset.sum_le_sum (fun sample _ => mul_le_mul_of_nonneg_left
        (shiftedAnchorLaw_row_sum_le_two security sample (scalar_bound security sample) output)
          (FiniteDist.nonneg _ _))
    _ = 2 := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end

end CurrentAFT.InwardAnchor

end

section







/-!
# The current proposal's actual primary numerator

The protected Gaussian roots and scalar are used before forming cyclic
body profiles. The diffuse profiles retain the true integer slices. The
primary numerator is the current two-profile balancing equation, without
the frozen V7 beta repair. Positivity is derived from its scalar deletion
budget; the actual budget is a separate arithmetic expression, not an
assumed operator norm or an assumed calibrated solution.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.base DiffuseProfiles.actualProfile
  DiffuseProfiles.signProfile DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw

instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem safe_clearance (security : ℕ) :
    4 * Parameters.safeMargin security < Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hc : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hp : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
  have hq := (Parameters.modulus_bounds security).1
  unfold Parameters.safeMargin
  omega

def safeLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) :=
  TrimmedSlice.finiteLaw (Parameters.modulus security) (Parameters.safeMargin security) 0
    (by positivity) (by have := safe_clearance security; simp only [abs_zero]; omega)

def safeHeight (security : ℕ) : ℝ :=
  1 / ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)

theorem safeHeight_pos (security : ℕ) : 0 < safeHeight security := by
  unfold safeHeight
  apply one_div_pos.mpr
  have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
  push_cast at h
  linarith

theorem safeLaw_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color ≤ safeHeight security := by
  rw [safeLaw, TrimmedSlice.finiteLaw_weight]
  have h := TrimmedSlice.law_le_of_shift_bound (Parameters.modulus security)
    (Parameters.safeMargin security) 0 0 color.val (by simp)
    (by have := safe_clearance security; omega)
  simpa only [safeHeight, Int.cast_natCast, Int.cast_zero, sub_zero] using h

/-- Cyclic translation of the actual finite palette, as an explicit equivalence. -/
noncomputable def shiftEquiv (security : ℕ) (shift : ℤ) :
    Fin (Parameters.modulus security) ≃ Fin (Parameters.modulus security) :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.trans
    ((Equiv.addRight (shift : ZMod (Parameters.modulus security))).trans
      (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm)

/-- `false` gives the root-convolved safe law; `true` also includes the
independent protected leg/queue scalar convolution. -/
def bodyLaw (security : ℕ) (includeScalar : Bool) :
    FiniteDist (Fin (Parameters.modulus security)) :=
  (actualSeedLaw security).mix fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))

theorem bodyLaw_upper (security : ℕ) (includeScalar : Bool)
    (color : Fin (Parameters.modulus security)) :
    (bodyLaw security includeScalar).weight color ≤ safeHeight security := by
  unfold bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ ≤ ∑ seed, (actualSeedLaw security).weight seed * safeHeight security :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (safeLaw_upper security _) ((actualSeedLaw security).nonneg seed)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def diffuseMean (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (actualProfile security true color + actualProfile security false color) / 2

theorem diffuseMean_nonneg (security : ℕ) (color : Fin (Parameters.modulus security)) :
    0 ≤ diffuseMean security color := by
  unfold diffuseMean DiffuseProfiles.actualProfile
  apply div_nonneg _ (by norm_num)
  exact add_nonneg (profile_nonneg _ _ _ _ _ _ _ _) (profile_nonneg _ _ _ _ _ _ _ _)

theorem diffuseMean_mass (security : ℕ) : ∑ color, diffuseMean security color = 1 := by
  simp only [diffuseMean, ← Finset.sum_div, Finset.sum_add_distrib, actualProfile_mass]
  norm_num

theorem diffuseMean_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    diffuseMean security color ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  unfold diffuseMean
  linarith [actualProfile_upper security true color, actualProfile_upper security false color]

def freeMass (security : ℕ) : ℝ :=
  Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

def markMass (security : ℕ) : ℝ := Parameters.legCount security * activation security

theorem markMass_pos (security : ℕ) : 0 < markMass security := by
  apply mul_pos _ (activation_pos security)
  exact Nat.cast_pos.mpr (by rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _)

theorem population_room (security : ℕ) :
    Parameters.modulus security + 2 * Parameters.legCount security ≤ Parameters.bodySize security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hq := (Parameters.modulus_bounds security).1
  have hpow : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hfour : 4 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hlegs : 4 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hfour
    simpa only [Parameters.legCount_eq, Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  have htwo : 2 ≤ Parameters.base security ^ 96 := by
    have h := Nat.le_self_pow (show 96 ≠ 0 by omega) (Parameters.base security)
    have := Parameters.base_ge_two security
    omega
  have hbody : 2 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) htwo
    simpa only [Parameters.bodySize_eq, mul_comm _ 2] using h
  omega

theorem freeMass_nonneg (security : ℕ) : 0 ≤ freeMass security := by
  have h := Nat.cast_le (α := ℝ).mpr (population_room security)
  push_cast at h
  unfold freeMass
  linarith

/-- The manuscript's actual primary balancing numerator. -/
def primaryProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color =>
    ((Parameters.dimension security : ℝ) / Parameters.modulus security -
      (freeMass security + markMass security) * (bodyLaw security false).weight color -
      ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
        (bodyLaw security true).weight color -
      2 * Parameters.legCount security * (1 - activation security) * diffuseMean security color) /
      markMass security

theorem primaryProfile_mass (security : ℕ) : ∑ color, primaryProfile security color = 1 := by
  have hq : (Parameters.modulus security : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Parameters.modulus_spec security).2.ne_zero
  have hmark := (markMass_pos security).ne'
  have ha := (activation_pos security).ne'
  have hl : (Parameters.legCount security : ℝ) ≠ 0 :=
    (mul_ne_zero_iff.mp hmark).1
  simp only [primaryProfile, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    FiniteDist.sum_one, diffuseMean_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  unfold freeMass markMass
  simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hq, hl, ha]
  ring

/-- A computable scalar deletion budget for the actual numerator. -/
def baselineLoss (security : ℕ) : ℝ :=
  (((Parameters.bodySize security : ℝ) + markMass security) *
      (2 * Parameters.safeMargin security)) /
      (markMass security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) +
    2 * (1 - activation security) * deletion security /
      (activation security * ((Parameters.modulus security : ℝ) - deletion security))

theorem primaryProfile_lower (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (1 - baselineLoss security) / Parameters.modulus security ≤ primaryProfile security color := by
  have hmark := markMass_pos security
  have hq : (0 : ℝ) < Parameters.modulus security :=
    Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
  have hsafe : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hdiff : (0 : ℝ) < Parameters.modulus security - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hc0 : 0 ≤ freeMass security + markMass security :=
    add_nonneg (freeMass_nonneg security) hmark.le
  have hc1 : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hc2 : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) := by
    exact mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have h0 := mul_le_mul_of_nonneg_left (bodyLaw_upper security false color) hc0
  have h1 := mul_le_mul_of_nonneg_left (bodyLaw_upper security true color) hc1
  have h2 := mul_le_mul_of_nonneg_left (diffuseMean_upper security color) hc2
  rw [mul_one_div] at h2
  have hidentity : ((1 - baselineLoss security) / Parameters.modulus security) * markMass security =
      (Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + markMass security) * safeHeight security -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) * safeHeight security -
        2 * Parameters.legCount security * (1 - activation security) /
          ((Parameters.modulus security : ℝ) - deletion security) := by
    unfold baselineLoss safeHeight freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have ha := (activation_pos security).ne'
    have hl : (Parameters.legCount security : ℝ) ≠ 0 :=
      (mul_ne_zero_iff.mp (markMass_pos security).ne').1
    field_simp
    ring
  unfold primaryProfile
  apply (le_div_iff₀ hmark).mpr
  rw [hidentity]
  linarith

end

end CurrentAFT.ProposalPrimary

end

section





/-!
# Positivity of the actual current primary proposal

All scalar budgets are discharged from the fixed public sizes and the
actual clipped Gaussian activation. No positivity or small-response
certificate is supplied as a premise. This closes the primary atom bound
needed by the concrete first-response stability theorem.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.base DiffuseProfiles.activation
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile

theorem safe_strip_budget (security : ℕ) :
    32 * Parameters.safeMargin security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hp : Parameters.base security ^ 2 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hq := (Parameters.modulus_bounds security).1
  simp only [Parameters.safeMargin, Parameters.sourceCutoff]
  omega

theorem body_deletion_budget (security : ℕ) :
    64 * Parameters.base security * Parameters.bodySize security *
      (2 * Parameters.safeMargin security) ≤
        Parameters.legCount security * Parameters.modulus security := by
  have hlarge : 384 ≤ Parameters.base security ^ 29 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 29
    norm_num at h
    omega
  have hpower : Parameters.base security * Parameters.base security ^ 96 *
      Parameters.base security ^ 2 = Parameters.base security ^ 99 := by
    calc
      _ = Parameters.base security ^ (1 + 96 + 2) := by simp only [pow_add, pow_one]
      _ = _ := rfl
  rw [Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.safeMargin,
    Parameters.sourceCutoff]
  calc
    _ = 384 * Parameters.modulus security * (Parameters.base security *
        Parameters.base security ^ 96 * Parameters.base security ^ 2) := by ring
    _ = 384 * Parameters.modulus security * Parameters.base security ^ 99 := by rw [hpower]
    _ ≤ Parameters.base security ^ 29 * Parameters.modulus security *
        Parameters.base security ^ 99 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlarge)
    _ = _ := by rw [show 128 = 99 + 29 by omega, pow_add]; ac_rfl

theorem mark_body_budget (security : ℕ) :
    16 * (Parameters.bodySize security : ℝ) * (2 * Parameters.safeMargin security) ≤
      markMass security * Parameters.modulus security := by
  have hb := FirstResponse.base_pos security
  have ha := (activation_pos security).le
  have hactivation : 1 ≤ (4 * (Parameters.base security : ℝ)) * activation security := by
    have h := (div_le_iff₀ (show 0 < 4 * (Parameters.base security : ℝ) by positivity)).mp
      (FirstResponse.activation_lower_simple security)
    simpa only [mul_comm] using h
  have hbudget : 64 * (Parameters.base security : ℝ) * Parameters.bodySize security *
      (2 * Parameters.safeMargin security) ≤
        (Parameters.legCount security : ℝ) * Parameters.modulus security := by
    exact_mod_cast body_deletion_budget security
  have hscaled : (4 * (Parameters.base security : ℝ)) *
      (16 * Parameters.bodySize security * (2 * Parameters.safeMargin security)) ≤
        (4 * Parameters.base security) * (markMass security * Parameters.modulus security) := by
    calc
      _ = 64 * (Parameters.base security : ℝ) * Parameters.bodySize security *
          (2 * Parameters.safeMargin security) := by ring
      _ ≤ (Parameters.legCount security : ℝ) * Parameters.modulus security := hbudget
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hactivation
          (show 0 ≤ (Parameters.legCount security : ℝ) * Parameters.modulus security by positivity)
        simpa only [one_mul, markMass, mul_assoc, mul_left_comm, mul_comm] using h
  by_contra hnot
  have hdiff : 0 < 16 * (Parameters.bodySize security : ℝ) * (2 * Parameters.safeMargin security) -
      markMass security * Parameters.modulus security := sub_pos.mpr (lt_of_not_ge hnot)
  have hpositive := mul_pos (show 0 < 4 * (Parameters.base security : ℝ) by positivity) hdiff
  nlinarith only [hscaled, hpositive]

theorem activated_deletion_budget (security : ℕ) :
    16 * (deletion security : ℝ) ≤ activation security * Parameters.modulus security := by
  have hactivation : 1 ≤ (4 * (Parameters.base security : ℝ)) * activation security := by
    have hb := FirstResponse.base_pos security
    have h := (div_le_iff₀ (show 0 < 4 * (Parameters.base security : ℝ) by positivity)).mp
      (FirstResponse.activation_lower_simple security)
    simpa only [mul_comm] using h
  have hbudget : 64 * (deletion security : ℝ) * Parameters.base security ≤
      Parameters.modulus security := by exact_mod_cast FirstResponse.deletion_linear_budget security
  calc
    _ ≤ 16 * (deletion security : ℝ) * (4 * Parameters.base security * activation security) := by
      nlinarith [mul_le_mul_of_nonneg_left hactivation (show 0 ≤ 16 * (deletion security : ℝ) by positivity)]
    _ = (64 * (deletion security : ℝ) * Parameters.base security) * activation security := by ring
    _ ≤ (Parameters.modulus security : ℝ) * activation security :=
      mul_le_mul_of_nonneg_right hbudget (activation_pos security).le
    _ = _ := by ring

/-- The two actual deletion contributions are each at most one quarter. -/
theorem baselineLoss_le_half (security : ℕ) : baselineLoss security ≤ 1 / 2 := by
  have hq := FirstResponse.modulus_pos security
  have hm := markMass_pos security
  have ha := activation_pos security
  have hs0 : 0 ≤ (2 * Parameters.safeMargin security : ℝ) := by positivity
  have hd0 : 0 ≤ (deletion security : ℝ) := by positivity
  have hstrip : 16 * (2 * Parameters.safeMargin security : ℝ) ≤ Parameters.modulus security := by
    have h := Nat.cast_le (α := ℝ).mpr (safe_strip_budget security)
    push_cast at h
    nlinarith
  have hsafe : 0 < (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    linarith
  have hdiff : 0 < (Parameters.modulus security : ℝ) - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hbody := mark_body_budget security
  have hscaledStrip := mul_le_mul_of_nonneg_left hstrip hm.le
  have hmarkq : 0 ≤ markMass security * (Parameters.modulus security : ℝ) := by positivity
  have hfirst : (((Parameters.bodySize security : ℝ) + markMass security) *
      (2 * Parameters.safeMargin security)) /
      (markMass security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) ≤
        1 / 4 := by
    apply (div_le_iff₀ (mul_pos hm hsafe)).mpr
    nlinarith only [hbody, hscaledStrip, hmarkq]
  have hsecond : 2 * (1 - activation security) * deletion security /
      (activation security * ((Parameters.modulus security : ℝ) - deletion security)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos ha hdiff)).mpr
    have hbudget := activated_deletion_budget security
    have hproduct := mul_nonneg ha.le hd0
    nlinarith only [hbudget, hproduct]
  unfold baselineLoss
  linarith

theorem primaryProfile_atom_lower (security : ℕ)
    (color : Fin (Parameters.modulus security)) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ primaryProfile security color := by
  have hq := FirstResponse.modulus_pos security
  apply le_trans _ (primaryProfile_lower security color)
  have h := baselineLoss_le_half security
  apply (div_le_div_iff₀ (by positivity) hq).mpr
  nlinarith

/-- The actual primary law is a probability distribution, with no positivity
certificate or analytic smallness assumption passed to the definition. -/
def primaryLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) where
  weight := primaryProfile security
  nonneg color := (show (0 : ℝ) ≤ 1 / (2 * (Parameters.modulus security : ℝ)) from by
    have := FirstResponse.modulus_pos security
    positivity).trans (primaryProfile_atom_lower security color)
  sum_one := primaryProfile_mass security

/-- Actual-reference first response, now with its elementary atom and mass
premises discharged by the concrete current primary proposal. -/
theorem actual_first_response_stable (security : ℕ)
    (profile : Fin (Parameters.modulus security) → ℝ) :
    Real.sqrt (profileSquareNorm (primaryLaw security).weight
      (FirstResponse.response security profile - profile)) ≤
        Real.sqrt (profileSquareNorm (primaryLaw security).weight profile) /
          (Parameters.base security : ℝ) ^ 5 ∧
    Real.sqrt (profileSquareNorm (primaryLaw security).weight
      ((FirstResponse.responseEquiv security).symm profile)) ≤
        2 * Real.sqrt (profileSquareNorm (primaryLaw security).weight profile) := by
  exact ⟨FirstResponse.response_defect_norm_le security _ (primaryProfile_atom_lower security)
    (primaryLaw security).sum_one profile,
    FirstResponse.response_inverse_norm_le_two security _ (primaryProfile_atom_lower security)
      (primaryLaw security).sum_one profile⟩

end

end CurrentAFT.ProposalPrimary

end

section







/-!
# The actual compensated safe-center proposal

The center law is formed from the already constructed primary law and the
actual inward smoothed anchor. Its positivity follows from current public
sizes, not from an assumed law or an assumed operator estimate.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base DiffuseProfiles.activation
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile InwardAnchor.smoothedAnchorLaw

 theorem finite_safe_law_weight (modulus margin : ℕ) (hclear : 2 * margin < modulus)
    (color : Fin modulus) :
    (TrimmedSlice.finiteLaw modulus margin 0 (Int.natCast_nonneg _)
      (by simp only [abs_zero]; omega)).weight color =
      if (margin : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - margin then
        1 / ((modulus : ℝ) - 2 * margin) else 0 := by
  have hcard : ((TrimmedSlice.slice modulus margin 0).card : ℤ) =
        (modulus : ℤ) - 2 * margin := by
    rw [TrimmedSlice.slice_card]
    simp only [abs_zero, sub_zero]
    omega
  have hcardReal : ((TrimmedSlice.slice modulus margin 0).card : ℝ) =
        (modulus : ℝ) - 2 * margin := by
    exact_mod_cast hcard
  have hsafe : (color.val : ℤ) ∈ TrimmedSlice.slice modulus margin 0 ↔
      (margin : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - margin := by
    rw [TrimmedSlice.mem_slice]
    omega
  rw [TrimmedSlice.finiteLaw_weight]
  simp only [TrimmedSlice.law, hsafe, hcardReal, one_div]

theorem safeLaw_weight (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color =
      if InwardAnchor.SafeColor security color then safeHeight security else 0 := by
  have h := finite_safe_law_weight (Parameters.modulus security) (Parameters.safeMargin security)
    (by have := safe_clearance security; omega) color
  by_cases hsafe : InwardAnchor.SafeColor security color
  · have hsafe' : (Parameters.safeMargin security : ℤ) ≤ color.val ∧
        (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security := hsafe
    simpa only [safeLaw, safeHeight, if_pos hsafe, if_pos hsafe'] using h
  · have hsafe' : ¬((Parameters.safeMargin security : ℤ) ≤ color.val ∧
        (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security) := hsafe
    simpa only [safeLaw, safeHeight, if_neg hsafe, if_neg hsafe'] using h

theorem bodySize_pos (security : ℕ) : (0 : ℝ) < Parameters.bodySize security := by
  apply Nat.cast_pos.mpr
  rw [Parameters.bodySize_eq]
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (pow_pos (Parameters.base_pos security) _)

theorem freeMass_lower (security : ℕ) : (Parameters.bodySize security : ℝ) / 2 ≤ freeMass security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hfour : 4 ≤ Parameters.base security ^ 96 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 96
    norm_num at h
    omega
  have hq : 4 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) hfour
    simpa only [Parameters.bodySize_eq, mul_comm _ 4] using h
  have hpow : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hmod := (Parameters.modulus_bounds security).1
  have hroot : 4 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hleg : 4 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hroot
    simpa only [Parameters.bodySize_eq, Parameters.legCount_eq, mul_assoc, ← pow_add] using h
  have hqr : 4 * (Parameters.modulus security : ℝ) ≤ Parameters.bodySize security := by exact_mod_cast hq
  have hlr : 4 * (Parameters.legCount security : ℝ) ≤ Parameters.bodySize security := by exact_mod_cast hleg
  unfold freeMass
  linarith

theorem freeMass_pos (security : ℕ) : 0 < freeMass security :=
  (half_pos (bodySize_pos security)).trans_le (freeMass_lower security)

def compensation (security : ℕ) : ℝ := markMass security / freeMass security

theorem compensation_nonneg (security : ℕ) : 0 ≤ compensation security :=
  div_nonneg (markMass_pos security).le (freeMass_pos security).le

theorem compensation_le_leg_body (security : ℕ) :
    compensation security ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := by
  have hf := freeMass_pos security
  have hb := bodySize_pos security
  have hnum : markMass security ≤ (Parameters.legCount security : ℝ) / 2 := by
    unfold markMass
    nlinarith [mul_le_mul_of_nonneg_left (activation_le_half security)
      (Nat.cast_nonneg (Parameters.legCount security))]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / freeMass security :=
      div_le_div_of_nonneg_right hnum hf.le
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / ((Parameters.bodySize security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (freeMass_lower security)
    _ = _ := by ring

theorem compensation_le_one (security : ℕ) : compensation security ≤ 1 := by
  apply (compensation_le_leg_body security).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)

theorem anchor_center_budget (security : ℕ) :
    2 * Parameters.legCount security * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by
  have hpower : 2 ≤ Parameters.base security ^ 16 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 16
    norm_num at h
    omega
  rw [Parameters.legCount_eq, Parameters.bodySize_eq, anchorWidth_eq]
  calc
    _ ≤ (Parameters.base security ^ 16) * Parameters.base security ^ 128 * Parameters.modulus security :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpower)
    _ = _ := by
      rw [show 128 = 96 + 32 by omega, show 48 = 32 + 16 by omega,
        pow_add, pow_add]
      ring

theorem centerLoss_le_half (security : ℕ) :
    compensation security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security) /
      Parameters.anchorWidth security ≤ 1 / 2 := by
  have hb := bodySize_pos security
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hs : 0 ≤ (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hbudget : 2 * (Parameters.legCount security : ℝ) * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by exact_mod_cast anchor_center_budget security
  calc
    _ ≤ (((Parameters.legCount security : ℝ) / Parameters.bodySize security) *
        ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) /
          Parameters.anchorWidth security :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (compensation_le_leg_body security) hs) ha.le
    _ ≤ (((Parameters.legCount security : ℝ) / Parameters.bodySize security) * Parameters.modulus security) /
        Parameters.anchorWidth security := by
      apply div_le_div_of_nonneg_right _ ha.le
      have hm0 : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_left (by linarith only [hm0])
        (div_nonneg (Nat.cast_nonneg (Parameters.legCount security)) hb.le)
    _ = ((Parameters.legCount security : ℝ) * Parameters.modulus security) /
        ((Parameters.bodySize security : ℝ) * Parameters.anchorWidth security) := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hb ha)).mpr
      linarith

def anchorPrimaryLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) :=
  (primaryLaw security).mix (InwardAnchor.smoothedAnchorLaw security)

theorem anchorPrimaryLaw_height (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (anchorPrimaryLaw security).weight color ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold anchorPrimaryLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.smoothedAnchorLaw_height security primary color) ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem anchorPrimaryLaw_zero_outside (security : ℕ) (color : Fin (Parameters.modulus security))
    (hunsafe : ¬InwardAnchor.SafeColor security color) : (anchorPrimaryLaw security).weight color = 0 := by
  simp only [anchorPrimaryLaw, FiniteDist.mix_weight,
    InwardAnchor.smoothedAnchorLaw_zero_outside security _ color hunsafe, mul_zero, Finset.sum_const_zero]

def centerProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (1 + compensation security) * (safeLaw security).weight color -
    compensation security * (anchorPrimaryLaw security).weight color

theorem centerProfile_mass (security : ℕ) : ∑ color, centerProfile security color = 1 := by
  simp only [centerProfile, Finset.sum_sub_distrib, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  ring

theorem centerProfile_zero_outside (security : ℕ) (color : Fin (Parameters.modulus security))
    (hunsafe : ¬InwardAnchor.SafeColor security color) : centerProfile security color = 0 := by
  simp only [centerProfile, safeLaw_weight, if_neg hunsafe,
    anchorPrimaryLaw_zero_outside security color hunsafe, mul_zero, sub_zero]

theorem centerProfile_bounds (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color / 2 ≤ centerProfile security color ∧
      centerProfile security color ≤ (1 + compensation security) * (safeLaw security).weight color := by
  have hc := compensation_nonneg security
  have hanchor := (anchorPrimaryLaw security).nonneg color
  constructor
  · by_cases hsafe : InwardAnchor.SafeColor security color
    · have hA : (0 : ℝ) < Parameters.anchorWidth security :=
        Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
      have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
        have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
        push_cast at h
        linarith
      have hcost : compensation security / Parameters.anchorWidth security ≤ safeHeight security / 2 := by
        have h := (div_le_iff₀ hA).mp (centerLoss_le_half security)
        unfold safeHeight
        calc
          _ ≤ 1 / (2 * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) := by
            apply (div_le_div_iff₀ hA (by positivity)).mpr
            nlinarith only [h]
          _ = _ := by simp only [one_div, mul_inv_rev]; ring
      have hanchorCost := mul_le_mul_of_nonneg_left (anchorPrimaryLaw_height security color) hc
      rw [mul_one_div] at hanchorCost
      rw [safeLaw_weight, if_pos hsafe]
      unfold centerProfile
      rw [safeLaw_weight, if_pos hsafe]
      nlinarith only [hcost, hanchorCost, mul_nonneg hc (safeHeight_pos security).le]
    · simp only [safeLaw_weight, if_neg hsafe, zero_div, centerProfile_zero_outside security color hsafe, le_refl]
  · unfold centerProfile
    exact sub_le_self _ (mul_nonneg hc hanchor)

def centerLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) where
  weight := centerProfile security
  nonneg color := (div_nonneg ((safeLaw security).nonneg color) (by norm_num)).trans
    (centerProfile_bounds security color).1
  sum_one := centerProfile_mass security

theorem centerLaw_height (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (centerLaw security).weight color ≤ 4 / (Parameters.modulus security : ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have hc0 := compensation_nonneg security
  have hc1 := compensation_le_one security
  have hsafe := safeLaw_upper security color
  have hden : (Parameters.modulus security : ℝ) / 2 ≤
      Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hheight : safeHeight security ≤ 2 / (Parameters.modulus security : ℝ) := by
    unfold safeHeight
    have h := one_div_le_one_div_of_le (by positivity : 0 < (Parameters.modulus security : ℝ) / 2) hden
    simpa only [one_div_div] using h
  have hupper := (centerProfile_bounds security color).2
  change centerProfile security color ≤ _
  have hsafeNonneg := (safeLaw security).nonneg color
  calc
    _ ≤ (1 + compensation security) * (safeLaw security).weight color := hupper
    _ ≤ 2 * (safeLaw security).weight color := by nlinarith
    _ ≤ 2 * (2 / (Parameters.modulus security : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsafe.trans hheight) (by norm_num)
    _ = _ := by ring

end

end CurrentAFT.ProposalPrimary

end

section







/-!
# Actual proposal deviations and its smoothed-anchor mean

Every body profile below is the actual cyclic pushforward mixture from
`ProposalPrimary`, and both diffuse profiles are the genuine trimmed-slice
mixtures. Their complete L1 estimates are substituted into the actual
balancing numerator. The anchor mean then uses the finite kernel whose
height and row sum were derived from its actual random draws.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.dimension Parameters.safeMargin
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile primaryLaw safeLaw bodyLaw

theorem safeLaw_l1_uniform (security : ℕ) :
    (∑ color, |(safeLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) =
      4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  have hwidth : 2 * (Parameters.safeMargin security : ℤ) + |(0 : ℤ)| < Parameters.modulus security := by
    have h := safe_clearance security
    simp only [abs_zero]
    omega
  have h := TrimmedSlice.law_palette_l1 (Parameters.modulus security)
    (Parameters.safeMargin security) 0 (Int.natCast_nonneg _) hwidth
  simp only [safeLaw, TrimmedSlice.finiteLaw_weight]
  convert h using 1
  push_cast
  ring

theorem shifted_safeLaw_l1_uniform (security : ℕ) (shift : ℤ) :
    (∑ color, |((safeLaw security).map (shiftEquiv security shift)).weight color -
      (Parameters.modulus security : ℝ)⁻¹|) =
        4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  simp only [FiniteDist.map_equiv_weight]
  rw [(shiftEquiv security shift).symm.sum_comp
    (fun color => |(safeLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|)]
  exact safeLaw_l1_uniform security

/-- The actual root and scalar convolutions are mixtures of cyclic
equivalences, so the entire L1 error has no root-support factor. -/
theorem bodyLaw_l1_uniform (security : ℕ) (includeScalar : Bool) :
    (∑ color, |(bodyLaw security includeScalar).weight color -
      (Parameters.modulus security : ℝ)⁻¹|) ≤
        4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  let shifted (seed : ActualSeed security) := (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))
  have hpoint (color) : (bodyLaw security includeScalar).weight color -
      (Parameters.modulus security : ℝ)⁻¹ =
      ∑ seed, (actualSeedLaw security).weight seed *
        ((shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹) := by
    simp only [bodyLaw, FiniteDist.mix_weight, shifted, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  calc
    _ ≤ ∑ color, ∑ seed, (actualSeedLaw security).weight seed *
        |(shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hpoint]
      simpa only [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)] using
        Finset.abs_sum_le_sum_abs (fun seed => (actualSeedLaw security).weight seed *
          ((shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹)) Finset.univ
    _ = ∑ seed, (actualSeedLaw security).weight seed *
        (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [← Finset.mul_sum]
      congr 1
      exact shifted_safeLaw_l1_uniform security _
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffuseMean_l1_uniform (security : ℕ) :
    (∑ color, |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) ≤
      2 * (deletion security : ℝ) / Parameters.modulus security := by
  have hpoint (color : Fin (Parameters.modulus security)) :
      |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹| ≤
      (|actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹| +
        |actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹|) / 2 := by
    rw [show diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹ =
      ((actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹) +
        (actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹)) / 2 by
      unfold diffuseMean; ring]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  calc
    _ ≤ ∑ color,
        (|actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹| +
          |actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹|) / 2 :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      linarith [actualProfile_l1_uniform security true, actualProfile_l1_uniform security false]

/-- The explicit L1 budget printed in the current proposal proof. -/
def primaryDeviationBudget (security : ℕ) : ℝ :=
  4 * ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security /
    (markMass security * Parameters.modulus security) +
  4 * (1 - activation security) * deletion security /
    (activation security * Parameters.modulus security)

theorem primaryLaw_l1_uniform (security : ℕ) :
    (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) ≤
      primaryDeviationBudget security := by
  have hq := FirstResponse.modulus_pos security
  have hm := markMass_pos security
  have ha := activation_pos security
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hfirst : 0 ≤ freeMass security + markMass security :=
    add_nonneg (freeMass_nonneg security) hm.le
  have hsecond : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hthird : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) :=
    mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have hidentity (color : Fin (Parameters.modulus security)) :
      (primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹ =
      -((freeMass security + markMass security) *
          ((bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹) +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          ((bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹) +
        2 * Parameters.legCount security * (1 - activation security) *
          (diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹)) / markMass security := by
    simp only [primaryLaw]
    unfold primaryProfile freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  have hpoint (color : Fin (Parameters.modulus security)) :
      |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹| ≤
      ((freeMass security + markMass security) *
          |(bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹| +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          |(bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹| +
        2 * Parameters.legCount security * (1 - activation security) *
          |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) / markMass security := by
    rw [hidentity, abs_div, abs_neg, abs_of_pos hm]
    apply div_le_div_of_nonneg_right _ hm.le
    have htriangle := (abs_add_le
      ((freeMass security + markMass security) *
        ((bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹) +
       ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
        ((bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹))
      (2 * Parameters.legCount security * (1 - activation security) *
        (diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    simpa only [abs_mul, abs_of_nonneg hfirst, abs_of_nonneg hsecond,
      abs_of_nonneg hthird] using htriangle
  calc
    _ ≤ ∑ color,
        ((freeMass security + markMass security) *
            |(bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹| +
          ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
            |(bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹| +
          2 * Parameters.legCount security * (1 - activation security) *
            |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) / markMass security :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ ((freeMass security + markMass security) *
          (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) +
        2 * Parameters.legCount security * (1 - activation security) *
          (2 * (deletion security : ℝ) / Parameters.modulus security)) / markMass security := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      apply div_le_div_of_nonneg_right _ hm.le
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (bodyLaw_l1_uniform security false) hfirst)
        (mul_le_mul_of_nonneg_left (bodyLaw_l1_uniform security true) hsecond))
        (mul_le_mul_of_nonneg_left (diffuseMean_l1_uniform security) hthird)
    _ = primaryDeviationBudget security := by
      unfold primaryDeviationBudget freeMass markMass
      field_simp
      ring

/-- The actual smoothed-anchor image of the current primary law. -/
def anchorPrimaryMean (security : ℕ) (output : Fin (Parameters.modulus security)) : ℝ :=
  ∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight output * (primaryLaw security).weight color

theorem anchorPrimaryMean_nonneg (security : ℕ) (output : Fin (Parameters.modulus security)) :
    0 ≤ anchorPrimaryMean security output :=
  Finset.sum_nonneg (fun color _ => mul_nonneg
    ((InwardAnchor.smoothedAnchorLaw security color).nonneg output) ((primaryLaw security).nonneg color))

theorem anchorPrimaryMean_mass (security : ℕ) : ∑ output, anchorPrimaryMean security output = 1 := by
  unfold anchorPrimaryMean
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  exact FiniteDist.sum_one _

/-- Row sum and height of the actual kernel give the primary-mean
height, using the full L1 deviation of that same primary law. -/
theorem anchorPrimaryMean_height (security : ℕ) (output : Fin (Parameters.modulus security)) :
    anchorPrimaryMean security output ≤ 2 / (Parameters.modulus security : ℝ) +
      (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
        Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (color : Fin (Parameters.modulus security)) :
      (InwardAnchor.smoothedAnchorLaw security color).weight output * (primaryLaw security).weight color ≤
      (InwardAnchor.smoothedAnchorLaw security color).weight output * (Parameters.modulus security : ℝ)⁻¹ +
      (1 / (Parameters.anchorWidth security : ℝ)) *
        |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹| := by
    have hdeviation := mul_le_mul_of_nonneg_left
      (le_abs_self ((primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹))
      ((InwardAnchor.smoothedAnchorLaw security color).nonneg output)
    have hheight := mul_le_mul_of_nonneg_right
      (InwardAnchor.smoothedAnchorLaw_height security color output)
      (abs_nonneg ((primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹))
    nlinarith only [hdeviation, hheight]
  calc
    _ ≤ ∑ color,
        ((InwardAnchor.smoothedAnchorLaw security color).weight output * (Parameters.modulus security : ℝ)⁻¹ +
        (1 / (Parameters.anchorWidth security : ℝ)) *
          |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      have hrow := mul_le_mul_of_nonneg_right
        (InwardAnchor.smoothedAnchorLaw_row_sum_le_two security output) (inv_nonneg.mpr hq.le)
      have hsame : (1 / (Parameters.anchorWidth security : ℝ)) *
          (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) =
        (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
          Parameters.anchorWidth security := by ring
      rw [hsame]
      simpa only [div_eq_mul_inv] using add_le_add hrow
        (le_refl ((∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
          Parameters.anchorWidth security))

theorem anchorPrimaryMean_height_budget (security : ℕ) (output : Fin (Parameters.modulus security)) :
    anchorPrimaryMean security output ≤ 2 / (Parameters.modulus security : ℝ) +
      primaryDeviationBudget security / Parameters.anchorWidth security :=
  (anchorPrimaryMean_height security output).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right (primaryLaw_l1_uniform security)
      (Nat.cast_nonneg _)))

/-- The current numerical sizes absorb the large body population into
the genuine anchor width. This is an arithmetic theorem for that family. -/
theorem body_margin_anchor_budget (security : ℕ) :
    Parameters.bodySize security * Parameters.safeMargin security ≤
      24 * Parameters.legCount security * Parameters.anchorWidth security := by
  have hlarge : 16384 ≤ Parameters.base security ^ 14 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 14
    norm_num at h
    exact h
  have hq := (Parameters.modulus_bounds security).2
  rw [Parameters.bodySize_eq, Parameters.safeMargin, Parameters.sourceCutoff,
    Parameters.legCount_eq, anchorWidth_eq]
  calc
    _ = 3 * Parameters.modulus security * Parameters.base security ^ 98 := by ring
    _ ≤ 3 * (131072 * Parameters.base security ^ 64) * Parameters.base security ^ 98 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
    _ = 393216 * Parameters.base security ^ 162 := by ring
    _ ≤ (24 * Parameters.base security ^ 14) * Parameters.base security ^ 162 :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem safeMargin_le_anchorWidth (security : ℕ) :
    Parameters.safeMargin security ≤ Parameters.anchorWidth security := by
  have h := InwardAnchor.four_cutoffs_le_anchor security
  rw [Parameters.safeMargin]
  omega

theorem markMass_le_legCount (security : ℕ) :
    markMass security ≤ Parameters.legCount security := by
  have hactivation : activation security ≤ 1 := (activation_le_half security).trans (by norm_num)
  simpa only [markMass, mul_one] using mul_le_mul_of_nonneg_left hactivation
    (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)

theorem body_mark_margin_anchor_budget (security : ℕ) :
    ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security ≤
      25 * Parameters.legCount security * Parameters.anchorWidth security := by
  have hbody : (Parameters.bodySize security : ℝ) * Parameters.safeMargin security ≤
      24 * Parameters.legCount security * Parameters.anchorWidth security := by
    exact_mod_cast body_margin_anchor_budget security
  have hmargin : (Parameters.safeMargin security : ℝ) ≤ Parameters.anchorWidth security := by
    exact_mod_cast safeMargin_le_anchorWidth security
  have hmark := mul_le_mul_of_nonneg_right (markMass_le_legCount security)
    (Nat.cast_nonneg (Parameters.safeMargin security) : (0 : ℝ) ≤ Parameters.safeMargin security)
  have hleg := mul_le_mul_of_nonneg_left hmargin
    (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)
  nlinarith only [hbody, hmark, hleg]

/-- The actual primary mean obeys a dimension-free activated height
bound. Every input is the concrete law already constructed above. -/
theorem activated_anchorPrimaryMean_height (security : ℕ)
    (output : Fin (Parameters.modulus security)) :
    activation security * anchorPrimaryMean security output ≤
      128 / (Parameters.modulus security : ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have ha := activation_pos security
  have hwidth : (0 : ℝ) < Parameters.anchorWidth security :=
    Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hlegs : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hmargin := body_mark_margin_anchor_budget security
  have hdelete : (deletion security : ℝ) ≤ 6 * Parameters.anchorWidth security := by
    have h := FirstResponse.deletion_le_six_anchor security
    rw [← anchorWidth_eq] at h
    exact_mod_cast h
  have hfirst : 4 * ((Parameters.bodySize security : ℝ) + markMass security) *
      Parameters.safeMargin security /
        ((Parameters.legCount security : ℝ) * Parameters.anchorWidth security) ≤ 100 := by
    apply (div_le_iff₀ (mul_pos hlegs hwidth)).mpr
    nlinarith only [hmargin]
  have hsecond : 4 * (1 - activation security) * deletion security /
      (Parameters.anchorWidth security : ℝ) ≤ 24 := by
    apply (div_le_iff₀ hwidth).mpr
    have hproduct := mul_nonneg ha.le (Nat.cast_nonneg (deletion security) : (0 : ℝ) ≤ deletion security)
    nlinarith only [hdelete, hproduct]
  have hidentity : activation security *
      (2 / (Parameters.modulus security : ℝ) + primaryDeviationBudget security /
        Parameters.anchorWidth security) * Parameters.modulus security =
      2 * activation security +
        4 * ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security /
          ((Parameters.legCount security : ℝ) * Parameters.anchorWidth security) +
        4 * (1 - activation security) * deletion security / Parameters.anchorWidth security := by
    unfold primaryDeviationBudget markMass
    field_simp
    ring
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (anchorPrimaryMean_height_budget security output) ha.le) hq.le
  apply (le_div_iff₀ hq).mpr
  rw [hidentity] at hscaled
  have halower := activation_le_half security
  linarith

end

end CurrentAFT.ProposalPrimary

end

end

section

section







/-!
# The actual paired primary and compensator score

The two control laws, the smoothed inward anchor, and the activation are
the concrete current proposal. The zero center weights outside the safe
interval are retained: the actual anchor kernel vanishes there as well.
No positive lower bound is required at those forbidden atoms.

Finite Cauchy--Schwarz and the proved activated anchor height give the
compensator variance bound. Independence of the two public controls then
gives the complete paired variance. The joint-input extensions average
these actual estimates and never divide by root probabilities.
-/

namespace CurrentAFT.PairedResponse

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.safeMargin DiffuseProfiles.activation primaryLaw centerLaw
  InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def anchorWeightedScore (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  ∑ primary, (InwardAnchor.smoothedAnchorLaw security primary).weight center *
    (primaryLaw security).weight primary * score primary

def anchorScoreEnergy (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  ∑ primary, (InwardAnchor.smoothedAnchorLaw security primary).weight center *
    (primaryLaw security).weight primary * score primary ^ 2

def compensatorScore (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  activation security * anchorWeightedScore security score center / (centerLaw security).weight center

/-- The actual public score reads one primary and its independent
compensator, with the same coefficient function in both summands. -/
def pairedScore (security : ℕ) (score : Palette security → ℝ)
    (primary center : Palette security) : ℝ :=
  score primary - compensatorScore security score center

theorem anchorWeightedScore_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, anchorWeightedScore security score center) =
      ∑ primary, (primaryLaw security).weight primary * score primary := by
  unfold anchorWeightedScore
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, InwardAnchor.smoothedAnchorLaw_mass, one_mul]

theorem anchorScoreEnergy_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, anchorScoreEnergy security score center) =
      ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 := by
  unfold anchorScoreEnergy
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, InwardAnchor.smoothedAnchorLaw_mass, one_mul]

theorem anchorWeightedScore_zero_outside (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) (hunsafe : ¬InwardAnchor.SafeColor security center) :
    anchorWeightedScore security score center = 0 := by
  simp only [anchorWeightedScore, InwardAnchor.smoothedAnchorLaw_zero_outside security _ center hunsafe,
    zero_mul, Finset.sum_const_zero]

theorem centerLaw_safe_atom_lower (security : ℕ) (center : Palette security)
    (hsafe : InwardAnchor.SafeColor security center) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (centerLaw security).weight center := by
  have hq := FirstResponse.modulus_pos security
  have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hheight : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le hden
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  have hlower := (centerProfile_bounds security center).1
  rw [safeLaw_weight, if_pos hsafe] at hlower
  simp only [centerLaw]
  calc
    _ = (1 / (Parameters.modulus security : ℝ)) / 2 := by ring
    _ ≤ safeHeight security / 2 := div_le_div_of_nonneg_right hheight (by norm_num)
    _ ≤ _ := hlower

theorem centerLaw_zero_implies_anchorScore_zero (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) (hzero : (centerLaw security).weight center = 0) :
    anchorWeightedScore security score center = 0 := by
  by_cases hsafe : InwardAnchor.SafeColor security center
  · have hlower := centerLaw_safe_atom_lower security center hsafe
    have hq := FirstResponse.modulus_pos security
    rw [hzero] at hlower
    have hpositive : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ)) := by positivity
    linarith
  · exact anchorWeightedScore_zero_outside security score center hsafe

theorem compensatorScore_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center) =
      activation security * ∑ primary, (primaryLaw security).weight primary * score primary := by
  calc
    _ = ∑ center, activation security * anchorWeightedScore security score center := by
      apply Finset.sum_congr rfl
      intro center _
      unfold compensatorScore
      by_cases hz : (centerLaw security).weight center = 0
      · rw [hz, centerLaw_zero_implies_anchorScore_zero security score center hz]
        ring
      · field_simp
    _ = _ := by rw [← Finset.mul_sum, anchorWeightedScore_mass]

theorem pairedScore_mean_zero (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      pairedScore security score primary center) = 0 := by
  have hcompensator : (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0 := by
    rw [compensatorScore_mass, hcentered, mul_zero]
  have hrow (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center) = (primaryLaw security).weight primary * score primary := by
    unfold pairedScore
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [show (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center * score primary) =
      (primaryLaw security).weight primary * score primary * ∑ center, (centerLaw security).weight center by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
    rw [FiniteDist.sum_one, mul_one]
    have hzero : (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        compensatorScore security score center) = 0 := by
      rw [show (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
          compensatorScore security score center) = (primaryLaw security).weight primary *
            ∑ center, (centerLaw security).weight center * compensatorScore security score center by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
      rw [hcompensator, mul_zero]
    rw [hzero, sub_zero]
  simp_rw [hrow]
  exact hcentered

/-- The actual kernel comparison, including its zero rows outside safe
support, is derived from the actual activated anchor height. -/
theorem activated_anchor_center_comparison (security : ℕ) (center : Palette security) :
    activation security * anchorPrimaryMean security center ≤ 256 * (centerLaw security).weight center := by
  by_cases hsafe : InwardAnchor.SafeColor security center
  · have h := activated_anchorPrimaryMean_height security center
    have hcenter := mul_le_mul_of_nonneg_left (centerLaw_safe_atom_lower security center hsafe)
      (show (0 : ℝ) ≤ 256 by norm_num)
    have hq := FirstResponse.modulus_pos security
    have hsame : 256 * (1 / (2 * (Parameters.modulus security : ℝ))) =
        128 / (Parameters.modulus security : ℝ) := by ring
    rw [hsame] at hcenter
    exact h.trans hcenter
  · have hzero : anchorPrimaryMean security center = 0 := by
      simp only [anchorPrimaryMean, InwardAnchor.smoothedAnchorLaw_zero_outside security _ center hsafe,
        zero_mul, Finset.sum_const_zero]
    rw [hzero, mul_zero]
    exact mul_nonneg (by norm_num) ((centerLaw security).nonneg center)

theorem anchorWeightedScore_square_le (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    anchorWeightedScore security score center ^ 2 ≤
      anchorPrimaryMean security center * anchorScoreEnergy security score center := by
  unfold anchorWeightedScore anchorPrimaryMean anchorScoreEnergy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro primary _
    exact mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
      ((primaryLaw security).nonneg primary)
  · intro primary _
    exact mul_nonneg (mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
      ((primaryLaw security).nonneg primary)) (sq_nonneg _)
  · intro primary _
    ring

theorem compensator_point_energy_le (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    activation security ^ 2 * (anchorWeightedScore security score center ^ 2 /
      (centerLaw security).weight center) ≤
        256 * activation security * anchorScoreEnergy security score center := by
  have henergy : 0 ≤ anchorScoreEnergy security score center :=
    Finset.sum_nonneg (fun primary _ =>
      mul_nonneg (mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
        ((primaryLaw security).nonneg primary)) (sq_nonneg _))
  by_cases hz : (centerLaw security).weight center = 0
  · rw [hz, div_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (activation_pos security).le) henergy
  · have hb : 0 < (centerLaw security).weight center :=
      lt_of_le_of_ne ((centerLaw security).nonneg center) (Ne.symm hz)
    have hCS := mul_le_mul_of_nonneg_left (anchorWeightedScore_square_le security score center)
      (sq_nonneg (activation security))
    have hrow := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (activated_anchor_center_comparison security center) (activation_pos security).le) henergy
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hb).mpr
    nlinarith only [hCS, hrow]

theorem compensator_energy_le (security : ℕ) (score : Palette security → ℝ) :
    activation security ^ 2 * profileSquareNorm (centerLaw security).weight
      (anchorWeightedScore security score) ≤
        256 * activation security * ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ center, 256 * activation security * anchorScoreEnergy security score center :=
      Finset.sum_le_sum (fun center _ => compensator_point_energy_le security score center)
    _ = _ := by rw [← Finset.mul_sum, anchorScoreEnergy_mass]









end

end CurrentAFT.PairedResponse

end

section










/-!
# The actual positive reference controls

The primary and center laws constructed from the current numerical parameters
are supplied to the canonical coefficient space. Restricting the center law
to the safe alphabet discards only zero atoms. The inward anchor has the same
support, so its restriction is still a probability kernel. In particular,
positivity of these reference laws is a theorem, not an input certificate.
-/

namespace CurrentAFT.ActualControls

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

abbrev SafePalette (security : ℕ) :=
  {color : Palette security // InwardAnchor.SafeColor security color}

/-- Restriction to a support containing every positive atom preserves mass. -/
def supportedLaw {State : Type*} [Fintype State] (law : FiniteDist State)
    (safe : State → Prop) (hzero : ∀ state, ¬safe state → law.weight state = 0) :
    FiniteDist {state // safe state} where
  weight state := law.weight state.val
  nonneg state := law.nonneg state.val
  sum_one := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype safe law.weight
    have houtside : (∑ state : {state // ¬safe state}, law.weight state.val) = 0 := by
      apply Finset.sum_eq_zero
      intro state _
      exact hzero state.val state.property
    rw [houtside, add_zero, law.sum_one] at hsplit
    exact hsplit

theorem supportedLaw_expectation {State : Type*} [Fintype State]
    (law : FiniteDist State) (safe : State → Prop)
    (hzero : ∀ state, ¬safe state → law.weight state = 0) (test : State → ℝ) :
    (supportedLaw law safe hzero).expectation (fun state => test state.val) =
      law.expectation test := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype safe
    (fun state => law.weight state * test state)
  have houtside : (∑ state : {state // ¬safe state}, law.weight state.val * test state.val) = 0 := by
    apply Finset.sum_eq_zero
    intro state _
    rw [hzero state.val state.property, zero_mul]
  rw [houtside, add_zero] at hsplit
  exact hsplit

def bodyReference (security : ℕ) : FiniteDist (SafePalette security) :=
  supportedLaw (centerLaw security) (InwardAnchor.SafeColor security)
    (fun color hunsafe => by
      simp only [centerLaw]
      exact centerProfile_zero_outside security color hunsafe)

def anchorReference (security : ℕ) (color : Palette security) :
    FiniteDist (SafePalette security) :=
  supportedLaw (InwardAnchor.smoothedAnchorLaw security color)
    (InwardAnchor.SafeColor security)
    (InwardAnchor.smoothedAnchorLaw_zero_outside security color)

theorem primaryReference_positive (security : ℕ) (color : Palette security) :
    0 < (primaryLaw security).weight color := by
  have hq := FirstResponse.modulus_pos security
  exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
    (by simpa only [primaryLaw] using primaryProfile_atom_lower security color)

theorem bodyReference_lower (security : ℕ) (color : SafePalette security) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (bodyReference security).weight color :=
  PairedResponse.centerLaw_safe_atom_lower security color.val color.property

theorem bodyReference_positive (security : ℕ) (color : SafePalette security) :
    0 < (bodyReference security).weight color := by
  have hq := FirstResponse.modulus_pos security
  exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
    (bodyReference_lower security color)

theorem bodyReference_upper (security : ℕ) (color : SafePalette security) :
    (bodyReference security).weight color ≤ 4 / (Parameters.modulus security : ℝ) :=
  centerLaw_height security color.val

/-- This is the actual coefficient space with the two proved positive laws. -/
abbrev Coefficients (security order : ℕ) :=
  ControlCoordinates.CoefficientSpace (primaryLaw security) (bodyReference security) order

instance coefficients_finiteDimensional (security order : ℕ) :
    FiniteDimensional ℝ (Coefficients security order) := by infer_instance



















end

end CurrentAFT.ActualControls

end

section







/-!
# The actual fringe and its primary certificate

The fringe is the gap between the true root-convolved safe profile and
the safe-interval height. A strengthened estimate on the actual primary
numerator dominates that gap by the actual compensation times primary
law. This proves the weighted Hilbert bounds, rather than postulating a
small background coefficient. The certificate is then constructed with
the explicit current first-response inverse.
-/

namespace CurrentAFT.FringeCertificate

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.dimension Parameters.safeMargin
  DiffuseProfiles.activation centerLaw primaryProfile safeLaw bodyLaw
  FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def uniformProfile (security : ℕ) : Palette security → ℝ :=
  fun _ => (Parameters.modulus security : ℝ)⁻¹

def fringe (security : ℕ) (color : Palette security) : ℝ :=
  safeHeight security - (bodyLaw security false).weight color

def fringeMass (security : ℕ) : ℝ :=
  2 * Parameters.safeMargin security /
    ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)

theorem fringe_nonneg (security : ℕ) (color : Palette security) : 0 ≤ fringe security color :=
  sub_nonneg.mpr (bodyLaw_upper security false color)

theorem fringe_sum_height (security : ℕ) :
    (∑ color, fringe security color) = (Parameters.modulus security : ℝ) * safeHeight security - 1 := by
  simp only [fringe, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, FiniteDist.sum_one]

theorem fringeMass_height (security : ℕ) :
    fringeMass security = (Parameters.modulus security : ℝ) * safeHeight security - 1 := by
  have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  unfold fringeMass safeHeight
  field_simp
  ring

theorem fringe_sum (security : ℕ) : ∑ color, fringe security color = fringeMass security := by
  rw [fringe_sum_height, fringeMass_height]

theorem fringeMass_nonneg (security : ℕ) : 0 ≤ fringeMass security := by
  rw [← fringe_sum]
  exact Finset.sum_nonneg (fun color _ => fringe_nonneg security color)

/-- Keeping the true `B0` term in the primary balancing numerator
gives the fringe contribution before any coarse pointwise replacement. -/
theorem primaryProfile_fringe_lower (security : ℕ) (color : Palette security) :
    ((freeMass security + markMass security) / markMass security) * fringe security color +
      (1 - baselineLoss security) / Parameters.modulus security ≤ (primaryLaw security).weight color := by
  have hm := markMass_pos security
  have hq := FirstResponse.modulus_pos security
  have ha := activation_pos security
  have hlegs : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hsafe : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hdiff : (0 : ℝ) < Parameters.modulus security - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hc1 : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hc2 : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) :=
    mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have h1 := mul_le_mul_of_nonneg_left (bodyLaw_upper security true color) hc1
  have h2 := mul_le_mul_of_nonneg_left (diffuseMean_upper security color) hc2
  rw [mul_one_div] at h2
  have hidentity :
      (((freeMass security + markMass security) / markMass security) * fringe security color +
        (1 - baselineLoss security) / Parameters.modulus security) * markMass security =
      (Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + markMass security) * (bodyLaw security false).weight color -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) * safeHeight security -
        2 * Parameters.legCount security * (1 - activation security) /
          ((Parameters.modulus security : ℝ) - deletion security) := by
    unfold fringe baselineLoss safeHeight freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  simp only [primaryLaw]
  unfold primaryProfile
  apply (le_div_iff₀ hm).mpr
  rw [hidentity]
  linarith

/-- The actual fringe is pointwise dominated by compensation times
the actual normalized primary law. -/
theorem fringe_majorant (security : ℕ) (color : Palette security) :
    fringe security color ≤ compensation security * (primaryLaw security).weight color := by
  have hc := compensation_nonneg security
  have hf := freeMass_pos security
  have hm := markMass_pos security
  have hq := FirstResponse.modulus_pos security
  have hresidual : 0 ≤ (1 - baselineLoss security) / Parameters.modulus security :=
    div_nonneg (by linarith [baselineLoss_le_half security]) hq.le
  have h := mul_le_mul_of_nonneg_left (primaryProfile_fringe_lower security color) hc
  have hcoefficient : compensation security *
      ((freeMass security + markMass security) / markMass security) = 1 + compensation security := by
    unfold compensation
    field_simp
  rw [mul_add, ← mul_assoc, hcoefficient] at h
  have hfringe := mul_nonneg hc (fringe_nonneg security color)
  have hconstant := mul_nonneg hc hresidual
  nlinarith only [h, hfringe, hconstant]

theorem fringe_profileSquareNorm_le (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (fringe security) ≤
      compensation security * fringeMass security := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color)
  have h := signProfile_square_bound (primaryLaw security).weight (fringe security)
    (compensation security) hp (fun color => by
      rw [abs_of_nonneg (fringe_nonneg security color)]
      exact fringe_majorant security color)
  simpa only [abs_of_nonneg (fringe_nonneg security _), fringe_sum] using h

def bodyDeviation (security : ℕ) : Palette security → ℝ :=
  fun color => (bodyLaw security false).weight color - uniformProfile security color

theorem bodyDeviation_mass (security : ℕ) : ∑ color, bodyDeviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [bodyDeviation, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem bodyDeviation_formula (security : ℕ) :
    bodyDeviation security = fringeMass security • uniformProfile security - fringe security := by
  funext color
  have hq := (FirstResponse.modulus_pos security).ne'
  rw [fringeMass_height]
  simp only [bodyDeviation, fringe, uniformProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem uniformProfile_square_le_two (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (uniformProfile security) ≤ 2 := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (color : Palette security) :
      uniformProfile security color ^ 2 / (primaryLaw security).weight color ≤
        2 / (Parameters.modulus security : ℝ) := by
    have hinv := one_div_le_one_div_of_le
      (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ)))
      (primaryProfile_atom_lower security color)
    have hcancel : 1 / (1 / (2 * (Parameters.modulus security : ℝ))) =
        2 * Parameters.modulus security := by simp only [one_div_one_div]
    rw [hcancel] at hinv
    calc
      _ ≤ uniformProfile security color ^ 2 * (2 * Parameters.modulus security) := by
        simpa only [one_div, div_eq_mul_inv, one_mul, primaryLaw] using mul_le_mul_of_nonneg_left hinv
          (sq_nonneg (uniformProfile security color))
      _ = _ := by unfold uniformProfile; field_simp
  unfold profileSquareNorm
  calc
    _ ≤ ∑ _color : Palette security, 2 / (Parameters.modulus security : ℝ) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = 2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

theorem profileSquareNorm_sub_le_two (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (first - second) ≤
      2 * profileSquareNorm (primaryLaw security).weight first +
        2 * profileSquareNorm (primaryLaw security).weight second := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 ≤ (primaryLaw security).weight color := (primaryLaw security).nonneg color
  have hpoint (color : Palette security) :
      (first color - second color) ^ 2 / (primaryLaw security).weight color ≤
        2 * (first color ^ 2 / (primaryLaw security).weight color) +
          2 * (second color ^ 2 / (primaryLaw security).weight color) := by
    have hscalar : (first color - second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
      nlinarith [sq_nonneg (first color + second color)]
    exact (div_le_div_of_nonneg_right hscalar (hp color)).trans_eq (by ring)
  simpa only [profileSquareNorm, Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)

/-- The actual root-convolved safe profile has its stronger weighted
Hilbert budget, rather than merely an unweighted boundary-mass estimate. -/
theorem bodyDeviation_profileSquareNorm_le (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (bodyDeviation security) ≤
      4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security := by
  rw [bodyDeviation_formula]
  have h := profileSquareNorm_sub_le_two security
    (fringeMass security • uniformProfile security) (fringe security)
  rw [profileSquareNorm_smul] at h
  have hu := mul_le_mul_of_nonneg_left (uniformProfile_square_le_two security)
    (sq_nonneg (fringeMass security))
  have hf := fringe_profileSquareNorm_le security
  nlinarith only [h, hu, hf]

/-- The primary profile certificate is obtained by an actual finite
linear inverse, then divided by the actual activation. -/
def primaryCertificateProfile (security : ℕ) : Palette security → ℝ :=
  (activation security)⁻¹ • (FirstResponse.responseEquiv security).symm (bodyDeviation security)

def primaryCertificateDensity (security : ℕ) (color : Palette security) : ℝ :=
  primaryCertificateProfile security color / (primaryLaw security).weight color

theorem primaryCertificateProfile_mass (security : ℕ) :
    ∑ color, primaryCertificateProfile security color = 0 := by
  simp only [primaryCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    FirstResponse.response_inverse_preserves_mass, bodyDeviation_mass, mul_zero]

theorem primaryCertificateDensity_centered (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color) = 0 := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : (primaryLaw security).weight color ≠ 0 :=
    ne_of_gt ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color))
  simp only [primaryCertificateDensity, mul_div_cancel₀ _ (hp _)]
  exact primaryCertificateProfile_mass security



theorem primaryCertificateDensity_square_bound (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      (4 / activation security ^ 2) *
        (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) := by
  have hq := FirstResponse.modulus_pos security
  have hpositive (profile : Palette security → ℝ) : 0 ≤ profileSquareNorm (primaryLaw security).weight profile :=
    profileSquareNorm_nonneg _ _ (primaryLaw security).nonneg
  have hinverse := (actual_first_response_stable security (bodyDeviation security)).2
  have hinverseSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hinverse 2
  rw [mul_pow, Real.sq_sqrt (hpositive _), Real.sq_sqrt (hpositive _)] at hinverseSq
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hinverseSq
  have hscaled := mul_le_mul_of_nonneg_left
    (hinverseSq.trans (mul_le_mul_of_nonneg_left (bodyDeviation_profileSquareNorm_le security) (by norm_num)))
    (sq_nonneg ((activation security)⁻¹))
  have hdensity : (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) =
      profileSquareNorm (primaryLaw security).weight (primaryCertificateProfile security) := by
    exact densityScore_square _ _
  rw [hdensity, primaryCertificateProfile, profileSquareNorm_smul]
  exact hscaled.trans_eq (by ring)

end

end CurrentAFT.FringeCertificate

end

section






namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BodyResponse
end CurrentAFT.BodyResponse
namespace CurrentAFT.BodyResponse.jointBodyInputEnergy
end CurrentAFT.BodyResponse.jointBodyInputEnergy
namespace CurrentAFT.BodyResponse.jointBodyProfile
end CurrentAFT.BodyResponse.jointBodyProfile




/-!
# Concrete stable atoms for the current free-body background

The primary fringe certificate and the safe-centered body certificate
are built from the actual current laws. Explicit current parameter bounds
give quantitative decay of their genuine density L2 norms. Their leading
responses sum exactly to the actual root-convolved center-law deviation.
No background smallness or response stability is assumed in this file.
-/

namespace CurrentAFT.BackgroundCertificates

open AFT DiffuseProfiles ProposalPrimary FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile safeLaw bodyLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

theorem fringeMass_decay (security : ℕ) :
    fringeMass security ≤ 1 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hstrip : 4 * (Parameters.safeMargin security : ℝ) < Parameters.modulus security := by
    exact_mod_cast safe_clearance security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  have hmargin : (Parameters.safeMargin security : ℝ) = 3 * (Parameters.base security : ℝ) ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ (2 * Parameters.safeMargin security : ℝ) / ((Parameters.modulus security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = (12 * (Parameters.base security : ℝ) ^ 2) / Parameters.modulus security := by rw [hmargin]; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : 12 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem compensation_decay (security : ℕ) :
    compensation security ≤ 1 / (Parameters.base security : ℝ) ^ 32 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  calc
    _ ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := compensation_le_leg_body security
    _ = (Parameters.base security : ℝ) ^ 32 / Parameters.modulus security := by
      simp only [Parameters.legCount_eq, Parameters.bodySize_eq, Nat.cast_pow, Nat.cast_mul]
      field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem bodyDeviation_budget_decay (security : ℕ) :
    4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security ≤
      6 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hm := fringeMass_decay security
  have hc := compensation_decay security
  have hmsq := pow_le_pow_left₀ (fringeMass_nonneg security) hm 2
  have hproduct := mul_le_mul hc hm (fringeMass_nonneg security) (by positivity)
  have hpower : 1 / (Parameters.base security : ℝ) ^ 124 ≤ 1 / (Parameters.base security : ℝ) ^ 94 :=
    one_div_le_one_div_of_le (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega))
  have hmsqBound : fringeMass security ^ 2 ≤ 1 / (Parameters.base security : ℝ) ^ 124 :=
    hmsq.trans_eq (by rw [div_pow, one_pow, ← pow_mul])
  have hproductBound : compensation security * fringeMass security ≤
      1 / (Parameters.base security : ℝ) ^ 94 :=
    hproduct.trans_eq (by ring)
  calc
    _ = 4 * fringeMass security ^ 2 + 2 * (compensation security * fringeMass security) := by ring
    _ ≤ 4 * (1 / (Parameters.base security : ℝ) ^ 94) +
        2 * (1 / (Parameters.base security : ℝ) ^ 94) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmsqBound.trans hpower) (by norm_num))
        (mul_le_mul_of_nonneg_left hproductBound (by norm_num))
    _ = _ := by ring

theorem primaryCertificateDensity_square_decay (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      384 / (Parameters.base security : ℝ) ^ 92 := by
  have hb := FirstResponse.base_pos security
  have hbudget0 : 0 ≤ 4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (compensation_nonneg security)) (fringeMass_nonneg security))
  have hinv := FirstResponse.activation_inverse_le security
  have hinvsq := pow_le_pow_left₀ (one_div_pos.mpr (activation_pos security)).le hinv 2
  have hcoefficient : 4 / activation security ^ 2 ≤ 64 * (Parameters.base security : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinvsq (show (0 : ℝ) ≤ 4 by norm_num)
    convert h using 1 <;> first | rfl | ring
  calc
    _ ≤ (4 / activation security ^ 2) *
        (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) :=
      primaryCertificateDensity_square_bound security
    _ ≤ (64 * (Parameters.base security : ℝ) ^ 2) * (6 / (Parameters.base security : ℝ) ^ 94) :=
      mul_le_mul hcoefficient (bodyDeviation_budget_decay security) hbudget0 (by positivity)
    _ = _ := by field_simp; ring

/-- Explicit decay is stronger than the coarse `O(base^-31)` budget. -/
theorem primaryCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      20 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (20 / (Parameters.base security : ℝ) ^ 46) ^ 2 =
      400 / (Parameters.base security : ℝ) ^ 92 := by ring
  rw [hden]
  exact (primaryCertificateDensity_square_decay security).trans
    (div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _))



def bodyCertificateProfile (security : ℕ) : Palette security → ℝ :=
  fun center => (centerLaw security).weight center - (safeLaw security).weight center

def bodyCertificateDensity (security : ℕ) (center : Palette security) : ℝ :=
  bodyCertificateProfile security center / (centerLaw security).weight center

theorem bodyCertificateProfile_mass (security : ℕ) : ∑ center, bodyCertificateProfile security center = 0 := by
  simp only [bodyCertificateProfile, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]



theorem bodyCertificateProfile_zero_of_center_zero (security : ℕ) (center : Palette security)
    (hzero : (centerLaw security).weight center = 0) : bodyCertificateProfile security center = 0 := by
  have hbound := (centerProfile_bounds security center).1
  change (safeLaw security).weight center / 2 ≤ (centerLaw security).weight center at hbound
  rw [hzero] at hbound
  have hsafe : (safeLaw security).weight center = 0 := by
    linarith [(safeLaw security).nonneg center]
  simp only [bodyCertificateProfile, hzero, hsafe, sub_self]

theorem bodyCertificateDensity_profile (security : ℕ) :
    (fun center => (centerLaw security).weight center * bodyCertificateDensity security center) =
      bodyCertificateProfile security := by
  funext center
  by_cases hz : (centerLaw security).weight center = 0
  · simp only [hz, zero_mul, bodyCertificateProfile_zero_of_center_zero security center hz]
  · unfold bodyCertificateDensity
    field_simp

theorem bodyCertificateDensity_centered (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center) = 0 := by
  rw [bodyCertificateDensity_profile]
  exact bodyCertificateProfile_mass security



theorem dominated_profile_square_le (security : ℕ) (reference profile : Palette security → ℝ)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) (href : ∀ color, 0 ≤ reference color)
    (hprofile : ∀ color, 0 ≤ profile color)
    (hdomination : ∀ color, profile color ≤ coefficient * reference color) :
    profileSquareNorm reference profile ≤ coefficient * ∑ color, profile color := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  by_cases hz : reference color = 0
  · rw [hz, div_zero]
    exact mul_nonneg hcoefficient (hprofile color)
  · have hp : 0 < reference color := lt_of_le_of_ne (href color) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right (hdomination color) (hprofile color)
    nlinarith only [h]

theorem safeLaw_center_square_le_two (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (safeLaw security).weight ≤ 2 := by
  have hdom (color : Palette security) : (safeLaw security).weight color ≤
      2 * (centerLaw security).weight color := by
    have h := (centerProfile_bounds security color).1
    change (safeLaw security).weight color / 2 ≤ (centerLaw security).weight color at h
    linarith
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (safeLaw security).weight 2 (by norm_num)
    (centerLaw security).nonneg (safeLaw security).nonneg hdom

theorem anchorPrimaryMean_center_square_le (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) ≤ 256 / activation security := by
  have ha := activation_pos security
  have hdom (color : Palette security) : anchorPrimaryMean security color ≤
      (256 / activation security) * (centerLaw security).weight color := by
    have h := PairedResponse.activated_anchor_center_comparison security color
    have heq : (256 / activation security) * (centerLaw security).weight color =
        (256 * (centerLaw security).weight color) / activation security := by ring
    rw [heq]
    apply (le_div_iff₀ ha).mpr
    nlinarith only [h]
  simpa only [anchorPrimaryMean_mass, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (anchorPrimaryMean security) (256 / activation security)
    (by positivity) (centerLaw security).nonneg (anchorPrimaryMean_nonneg security) hdom

theorem bodyCertificateProfile_formula (security : ℕ) :
    bodyCertificateProfile security = compensation security •
      ((safeLaw security).weight - anchorPrimaryMean security) := by
  have hanchor (color : Palette security) : (anchorPrimaryLaw security).weight color =
      anchorPrimaryMean security color := by
    simp only [anchorPrimaryLaw, FiniteDist.mix_weight, anchorPrimaryMean]
    apply Finset.sum_congr rfl
    intro primary _
    ring
  funext color
  simp only [bodyCertificateProfile, centerLaw, centerProfile, hanchor, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem center_profile_sub_square_le_two (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (centerLaw security).weight (first - second) ≤
      2 * profileSquareNorm (centerLaw security).weight first +
        2 * profileSquareNorm (centerLaw security).weight second := by
  have hpoint (color : Palette security) : (first color - second color) ^ 2 / (centerLaw security).weight color ≤
      2 * (first color ^ 2 / (centerLaw security).weight color) +
        2 * (second color ^ 2 / (centerLaw security).weight color) := by
    have hscalar : (first color - second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
      nlinarith [sq_nonneg (first color + second color)]
    exact (div_le_div_of_nonneg_right hscalar ((centerLaw security).nonneg color)).trans_eq (by ring)
  simpa only [profileSquareNorm, Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)

theorem bodyCertificateDensity_square_bound (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      compensation security ^ 2 * (4 + 512 / activation security) := by
  have hdensity : (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) =
      profileSquareNorm (centerLaw security).weight (bodyCertificateProfile security) := densityScore_square _ _
  rw [hdensity, bodyCertificateProfile_formula, profileSquareNorm_smul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (compensation security))
  have h := center_profile_sub_square_le_two security (safeLaw security).weight (anchorPrimaryMean security)
  have hs := safeLaw_center_square_le_two security
  have ha := anchorPrimaryMean_center_square_le security
  calc
    _ ≤ 2 * profileSquareNorm (centerLaw security).weight (safeLaw security).weight +
        2 * profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) := h
    _ ≤ 2 * 2 + 2 * (256 / activation security) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) (mul_le_mul_of_nonneg_left ha (by norm_num))
    _ = _ := by ring

theorem bodyCertificateDensity_square_decay (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      4096 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hc := pow_le_pow_left₀ (compensation_nonneg security) (compensation_decay security) 2
  have hfactor : 4 + 512 / activation security ≤ 4096 * (Parameters.base security : ℝ) ^ 2 := by
    have hinv := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security)
      (show (0 : ℝ) ≤ 512 by norm_num)
    calc
      _ = 4 + 512 * (1 / activation security) := by ring
      _ ≤ 4 + 512 * (4 * (Parameters.base security : ℝ)) := add_le_add le_rfl hinv
      _ ≤ _ := by nlinarith only [hb1, sq_nonneg ((Parameters.base security : ℝ) - 1)]
  have hfactor0 : 0 ≤ 4 + 512 / activation security := by have := activation_pos security; positivity
  calc
    _ ≤ compensation security ^ 2 * (4 + 512 / activation security) := bodyCertificateDensity_square_bound security
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 32) ^ 2 * (4096 * (Parameters.base security : ℝ) ^ 2) :=
      mul_le_mul hc hfactor hfactor0 (sq_nonneg _)
    _ = _ := by field_simp

theorem bodyCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      64 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (64 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      4096 / (Parameters.base security : ℝ) ^ 62 := by ring
  rw [hden]
  exact bodyCertificateDensity_square_decay security

/-- Root-marginal convolution is the actual mixture of cyclic palette
equivalences induced by the independent protected edge difference. -/
def rootConvolutionProfile (security : ℕ) (profile : Palette security → ℝ) : Palette security → ℝ :=
  fun output => ∑ seed, (actualSeedLaw security).weight seed *
    profile ((shiftEquiv security (actualBlur security seed)).symm output)

def convolvedCenterLaw (security : ℕ) : FiniteDist (Palette security) :=
  (actualSeedLaw security).mix (fun seed => (centerLaw security).map
    (shiftEquiv security (actualBlur security seed)))

def bodyLeadingResponse (security : ℕ) (density : Palette security → ℝ) : Palette security → ℝ :=
  rootConvolutionProfile security (fun center => (centerLaw security).weight center * density center)

theorem bodyLaw_false_weight (security : ℕ) (output : Palette security) :
    (bodyLaw security false).weight output = rootConvolutionProfile security (safeLaw security).weight output := by
  simp only [bodyLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight,
    Bool.false_eq_true, if_false, add_zero, rootConvolutionProfile]

theorem convolvedCenterLaw_weight (security : ℕ) (output : Palette security) :
    (convolvedCenterLaw security).weight output = rootConvolutionProfile security (centerLaw security).weight output := by
  simp only [convolvedCenterLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight, rootConvolutionProfile]







end

end CurrentAFT.BackgroundCertificates

end

section









/-!
# Reflection symmetry and the fair actual inward-anchor sign

The reflection acts simultaneously on the three actual protected Gaussian
scalars. It preserves their joint product weight and reverses both the
public blur and the protected second input. The diffuse profiles and cyclic
body profiles are then reflected before applying the current primary
balancing formula. No frozen-V7 primary law or parameter family is used.

The anchor's direction uses the actual midpoint fair coin. Its exact fair
law is proved from the reflection of the actual constructed primary law,
not supplied as a sign-mixture assumption.
-/

namespace CurrentAFT.ProposalSymmetry

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.activation

def seedNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  ((GaussianSource.windowNegateEquiv (edgeCutoff security)).prodCongr
    (GaussianSource.windowNegateEquiv (edgeCutoff security))).prodCongr
      (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))















def shiftColor (modulus : ℕ) [NeZero modulus] (shift : ℤ) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (shift : ZMod modulus)



























def directionLaw (security : ℕ) : FiniteDist Bool :=
  ((primaryLaw security).prod (FiniteDist.uniform Bool)).map
    (fun input => InwardAnchor.positiveDirection security input.1 input.2)







end

end CurrentAFT.ProposalSymmetry

end

section














/-!
# The first histogram of the actual protected leg reference experiment

The reference law below retains the protected second scalar beside the
ordered endpoint pair. The diffuse law is the true integer trimmed slice,
with its varying denominator. The marked companion uses that same second
scalar with a minus sign, together with the independent actual public blur.
Only laws of outputs are constructed here. Implementing them by one public
law of local affine charts is a separate proof obligation.
-/

namespace CurrentAFT.FirstHistogram

open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  actualSeedLaw actualProfile activation primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Pair (security : ℕ) := Palette security × Palette security
abbrev Scalar (security : ℕ) := InwardAnchor.ScalarSample security
abbrev JointOutput (security : ℕ) := Scalar security × Pair security

 theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

def atom {Color : Type*} [DecidableEq Color] (first second : Color) : ℝ :=
  if first = second then 1 else 0

 theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

def endpointHistogram (security : ℕ) (law : FiniteDist (JointOutput security)) (output : Palette security) : ℝ :=
  law.expectation (fun sample => atom sample.2.1 output + atom sample.2.2 output)

 theorem diffuse_clearance (security : ℕ) :
    2 + (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1)) +
        ((Parameters.sourceCutoff security : ℤ) - 1) < Parameters.modulus security := by
  have h := deletion_clearance security
  simp only [deletion] at h
  omega

/-- A fixed protected seed still retains the same second scalar in the
integer pair sum. The uniform offset ranges over the printed signed
anchor interval. -/
def diffuseSeedPair (security : ℕ) (positive : Bool) (seed : ActualSeed security) : FiniteDist (Pair security) :=
  TrimmedSlice.mixedPairDistribution (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1))
    ((Parameters.sourceCutoff security : ℤ) - 1) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne'
    (fun _ : Unit => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun _ : Unit => actualSecond security seed) (FiniteDist.uniform Unit) (by norm_num)
    (fun _ _ hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin)
    (fun _ => actualSecond_bound security seed) (diffuse_clearance security)

theorem diffuseSeedPair_weight (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (first second : Palette security) :
    (diffuseSeedPair security positive seed).weight (first, second) =
      TrimmedSlice.averagedPair (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) first second := by
  simp [diffuseSeedPair, TrimmedSlice.mixedPairDistribution, TrimmedSlice.mixedPair]

theorem diffuseSeedPair_first (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.1 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, diffuseSeedPair_weight]
  rw [Finset.sum_comm]
  simp only [atom, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold TrimmedSlice.averagedPair TrimmedSlice.averagedLaw TrimmedSlice.intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro offset _
  rw [← Finset.mul_sum, TrimmedSlice.orderedPairSlice_marginal _ _ _ (by norm_num)]

theorem diffuseSeedPair_second (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.2 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  have hsymm (first second : Palette security) :
      (diffuseSeedPair security positive seed).weight (first, second) =
        (diffuseSeedPair security positive seed).weight (second, first) := by
    rw [diffuseSeedPair_weight, diffuseSeedPair_weight]
    simp only [TrimmedSlice.averagedPair, TrimmedSlice.orderedPairSlice_symmetric]
  rw [← diffuseSeedPair_first security positive seed output]
  simp only [FiniteDist.expectation, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [hsymm]

/-- The actual diffuse reference keeps the source increment beside the
pair. Its direction reads the primary color and the fresh midpoint coin. -/
def diffuseReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (FiniteDist.uniform Bool).mix (fun coin =>
    (actualSeedLaw security).mix (fun seed =>
      (diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) seed).map
        (fun pair => (seed.2, pair))))

def diffuseMarginal (security : ℕ) (primary output : Palette security) : ℝ :=
  (FiniteDist.uniform Bool).expectation (fun coin =>
    actualProfile security (InwardAnchor.positiveDirection security primary coin) output)

theorem diffuseReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (diffuseReferenceLaw security primary) output =
      2 * diffuseMarginal security primary output := by
  unfold endpointHistogram diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def,
    FiniteDist.expectation_add, diffuseSeedPair_first, diffuseSeedPair_second]
  unfold diffuseMarginal actualProfile profile TrimmedSlice.mixedLaw
  simp only [FiniteDist.expectation]
  ring

theorem diffuse_histogram_decomposition (security : ℕ) (primary output : Palette security) :
    2 * (1 - activation security) * diffuseMarginal security primary output =
      2 * (1 - activation security) * diffuseMean security output +
        signProfile security output * FirstResponse.anchorSign security primary := by
  unfold diffuseMarginal
  simp only [FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_bool,
    Nat.cast_ofNat, Fintype.sum_bool]
  by_cases hl : 2 * primary.val < Parameters.modulus security - 1
  · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, if_true]
    unfold diffuseMean signProfile
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * primary.val
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false, if_true]
      unfold diffuseMean signProfile
      ring
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false]
      unfold diffuseMean signProfile
      ring

 theorem negativeSecond_bound (security : ℕ) (seed : ActualSeed security) :
    |-(actualSecond security seed)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  simpa only [abs_neg] using actualSecond_bound security seed

/-- Activation fixes the marked endpoint and preserves the same second
source, with its negative sign in the companion. Public blur is sampled
independently from the actual edge-difference law. -/
def markedReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (actualSeedLaw security).mix (fun seed =>
    (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map (fun companion =>
        (seed.2, (primary, shiftEquiv security (actualBlur security seed) companion))))

def markedCompanion (security : ℕ) (primary output : Palette security) : ℝ :=
  (actualSeedLaw security).expectation (fun seed =>
    ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map
      (shiftEquiv security (actualBlur security seed))).weight output)

theorem markedReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (markedReferenceLaw security primary) output =
      atom primary output + markedCompanion security primary output := by
  unfold endpointHistogram markedReferenceLaw markedCompanion
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_add,
    FiniteDist.expectation_const]
  simp only [FiniteDist.expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro seed _
  congr 1
  change (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed) _).expectation
      (fun companion => atom (shiftEquiv security (actualBlur security seed) companion) output) = _
  rw [← expectation_atom ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
    (negativeSecond_bound security seed)).map (shiftEquiv security (actualBlur security seed))) output]
  rw [FiniteDist.expectation_map]
  rfl

/-- The protected reference mixture after averaging the activation event.
Both branches retain the same second-source marginal. -/
def referenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) where
  weight sample := (1 - activation security) * (diffuseReferenceLaw security primary).weight sample +
    activation security * (markedReferenceLaw security primary).weight sample
  nonneg sample := add_nonneg
    (mul_nonneg (by linarith [activation_le_half security]) ((diffuseReferenceLaw security primary).nonneg sample))
    (mul_nonneg (activation_pos security).le ((markedReferenceLaw security primary).nonneg sample))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FiniteDist.sum_one, FiniteDist.sum_one]
    ring

theorem reference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (referenceLaw security primary) output =
      activation security * atom primary output + activation security * markedCompanion security primary output +
        2 * (1 - activation security) * diffuseMean security output +
          signProfile security output * FirstResponse.anchorSign security primary := by
  have hmix : endpointHistogram security (referenceLaw security primary) output =
      (1 - activation security) * endpointHistogram security (diffuseReferenceLaw security primary) output +
        activation security * endpointHistogram security (markedReferenceLaw security primary) output := by
    simp only [endpointHistogram, FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hmix, diffuseReference_histogram, markedReference_histogram]
  have hdiff := diffuse_histogram_decomposition security primary output
  nlinarith only [hdiff]

/-- Reflection of the second source alone preserves the actual product
law and leaves the two public edge scalars fixed. -/
def secondNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  (Equiv.refl _).prodCongr
    (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))

theorem secondNegate_weight (security : ℕ) (seed : ActualSeed security) :
    (actualSeedLaw security).weight (secondNegate security seed) = (actualSeedLaw security).weight seed := by
  simp only [actualSeedLaw, secondNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, FiniteDist.prod_weight, scalarLaw, GaussianSource.windowGaussian_reflection]

theorem secondNegate_blur (security : ℕ) (seed : ActualSeed security) :
    actualBlur security (secondNegate security seed) = actualBlur security seed := rfl

theorem secondNegate_second (security : ℕ) (seed : ActualSeed security) :
    actualSecond security (secondNegate security seed) = -actualSecond security seed := rfl

theorem markedCompanion_convolution (security : ℕ) (primary output : Palette security) :
    markedCompanion security primary output =
      BackgroundCertificates.rootConvolutionProfile security
        (InwardAnchor.smoothedAnchorLaw security primary).weight output := by
  unfold markedCompanion
  simp only [FiniteDist.expectation, FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (actualSeedLaw security).weight seed *
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output) := by
      calc
        _ = ∑ seed, (actualSeedLaw security).weight (secondNegate security seed) *
          (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security (secondNegate security seed))
            (negativeSecond_bound security (secondNegate security seed))).weight
              ((shiftEquiv security (actualBlur security (secondNegate security seed))).symm output) :=
          ((secondNegate security).sum_comp _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro seed _
          simp only [secondNegate_weight, secondNegate_second, secondNegate_blur, neg_neg]
    _ = ((edgeLaw security).prod (edgeLaw security)).expectation (fun edge =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security ((edge.1 : ℤ) - edge.2)).symm output)) := by
      change (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output)) = _
      rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualSecond, actualBlur, InwardAnchor.smoothedAnchorLaw, FiniteDist.mix_weight,
        FiniteDist.expectation]
    _ = _ := by
      change _ = (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security (actualBlur security seed)).symm output))
      conv_rhs => rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualBlur, FiniteDist.expectation_const]



theorem actualSecond_expectation (security : ℕ) (value : Scalar security → ℝ) :
    (actualSeedLaw security).expectation (fun seed => value seed.2) =
      (scalarLaw security).expectation value := by
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  change ((edgeLaw security).prod (edgeLaw security)).expectation
    (fun _ => (scalarLaw security).expectation value) = _
  rw [FiniteDist.expectation_const]

theorem diffuse_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (diffuseReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const,
    actualSecond_expectation]

theorem marked_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (markedReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold markedReferenceLaw
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const]
  exact actualSecond_expectation security value

theorem reference_expectation (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (referenceLaw security primary).expectation value =
      (1 - activation security) * (diffuseReferenceLaw security primary).expectation value +
        activation security * (markedReferenceLaw security primary).expectation value := by
  simp only [FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- The protected attachment increment has its genuine scalar law,
independently of the primary color and the activation branch. -/
theorem reference_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (referenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  rw [reference_expectation, diffuse_attachment_expectation, marked_attachment_expectation]
  ring

def scoreProfile (security : ℕ) (score : Palette security → ℝ) : Palette security → ℝ :=
  fun primary => (primaryLaw security).weight primary * score primary

 theorem sum_atom (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
    (∑ primary, profile primary * atom primary output) = profile output := by
  classical
  simp [atom, mul_ite]

theorem convolution_sum (security : ℕ) (coefficient : Palette security → ℝ)
    (kernel : Palette security → Palette security → ℝ) (output : Palette security) :
    (∑ primary, coefficient primary * BackgroundCertificates.rootConvolutionProfile security (kernel primary) output) =
      BackgroundCertificates.rootConvolutionProfile security
        (fun center => ∑ primary, coefficient primary * kernel primary center) output := by
  unfold BackgroundCertificates.rootConvolutionProfile
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem markedCompanion_score (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ primary, scoreProfile security score primary * markedCompanion security primary output) =
      BackgroundCertificates.rootConvolutionProfile security (anchorWeightedScore security score) output := by
  simp_rw [markedCompanion_convolution]
  rw [convolution_sum]
  congr 1
  funext center
  unfold anchorWeightedScore scoreProfile
  apply Finset.sum_congr rfl
  intro primary _
  ring

def primaryHistogramResponse (security : ℕ) (score : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output

/-- The signed primary response is derived from the concrete joint law.
The independent attachment contributes zero for every centered score. -/
theorem primaryHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (output : Palette security) :
    primaryHistogramResponse security score output =
      activation security * scoreProfile security score output +
        activation security * BackgroundCertificates.rootConvolutionProfile security
          (anchorWeightedScore security score) output +
        signProfile security output * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) := by
  unfold primaryHistogramResponse
  simp_rw [reference_histogram]
  calc
    _ = ∑ primary,
        (activation security * (scoreProfile security score primary * atom primary output) +
          activation security * (scoreProfile security score primary * markedCompanion security primary output) +
          (2 * (1 - activation security) * diffuseMean security output) * scoreProfile security score primary +
          signProfile security output *
            (FirstResponse.anchorSign security primary * scoreProfile security score primary)) := by
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_atom, markedCompanion_score]
      change _ + _ + _ * (∑ primary, (primaryLaw security).weight primary * score primary) + _ = _
      rw [hcentered, mul_zero, add_zero]
      rfl



/-- A reserved compensator center has the actual ordinary body channel,
using the independent protected edge difference. -/
def compensatorBodyLaw (security : ℕ) (center : Palette security) : FiniteDist (Palette security) :=
  (actualSeedLaw security).map (fun seed => shiftEquiv security (actualBlur security seed) center)

theorem compensatorBodyLaw_weight (security : ℕ) (center output : Palette security) :
    (compensatorBodyLaw security center).weight output =
      BackgroundCertificates.rootConvolutionProfile security (atom center) output := by
  unfold compensatorBodyLaw BackgroundCertificates.rootConvolutionProfile
  rw [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro seed _
  have heq : (shiftEquiv security (actualBlur security seed)) center = output ↔
      center = (shiftEquiv security (actualBlur security seed)).symm output := by
    exact (Equiv.eq_symm_apply _).symm
  simp only [heq, atom]
  split_ifs <;> ring

theorem body_score_convolution (security : ℕ) (coefficient : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, coefficient center * (compensatorBodyLaw security center).weight output) =
      BackgroundCertificates.rootConvolutionProfile security coefficient output := by
  simp_rw [compensatorBodyLaw_weight]
  rw [convolution_sum]
  congr 1
  funext center
  exact sum_atom security coefficient center

theorem center_weight_compensator (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    (centerLaw security).weight center * compensatorScore security score center =
      activation security * anchorWeightedScore security score center := by
  unfold compensatorScore
  by_cases hzero : (centerLaw security).weight center = 0
  · rw [hzero, centerLaw_zero_implies_anchorScore_zero security score center hzero]
    ring
  · field_simp

theorem compensatorHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center *
      (compensatorBodyLaw security center).weight output) =
      activation security * BackgroundCertificates.rootConvolutionProfile security
        (anchorWeightedScore security score) output := by
  simp only [center_weight_compensator, mul_assoc, ← Finset.mul_sum]
  rw [body_score_convolution]

/-- The complete first histogram reads the two actual off-body outputs
and the reserved compensator-body output. Any remaining coordinate has a
profile independent of this public pair and is integrated in `other`.
Their hidden roots may be correlated: only first marginals enter here. -/
def completeHistogramResponse (security : ℕ) (score : Palette security → ℝ)
    (other : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
    pairedScore security score primary center *
      (endpointHistogram security (referenceLaw security primary) output +
        (compensatorBodyLaw security center).weight output + other output)

theorem completeHistogramResponse_decomposition (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      primaryHistogramResponse security score output -
        ∑ center, (centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output := by
  have hcompensator : (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0 := by
    rw [compensatorScore_mass, hcentered, mul_zero]
  have hleg (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center *
          endpointHistogram security (referenceLaw security primary) output) =
        scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output := by
    unfold pairedScore scoreProfile
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    calc
      _ = ((primaryLaw security).weight primary * score primary *
            endpointHistogram security (referenceLaw security primary) output) *
              (∑ center, (centerLaw security).weight center) -
          ((primaryLaw security).weight primary * endpointHistogram security (referenceLaw security primary) output) *
            (∑ center, (centerLaw security).weight center * compensatorScore security score center) := by
        simp only [Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro center _ <;> ring
      _ = _ := by rw [FiniteDist.sum_one, hcompensator]; ring
  have hbody : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * (compensatorBodyLaw security center).weight output) =
      -(∑ center, (centerLaw security).weight center * compensatorScore security score center *
        (compensatorBodyLaw security center).weight output) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ center, (((centerLaw security).weight center * (compensatorBodyLaw security center).weight output) *
          (∑ primary, (primaryLaw security).weight primary * score primary) -
        ((centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output) * (∑ primary, (primaryLaw security).weight primary)) := by
        apply Finset.sum_congr rfl
        intro center _
        unfold pairedScore
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro primary _
        ring
      _ = _ := by simp only [hcentered, mul_zero, FiniteDist.sum_one, mul_one, zero_sub, Finset.sum_neg_distrib]
  have hother : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * other output) = 0 := by
    simp only [← Finset.sum_mul, pairedScore_mean_zero security score hcentered, zero_mul]
  unfold completeHistogramResponse
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [hleg]
  rw [hbody, hother, add_zero]
  rfl

/-- The genuine paired primary and compensator cancel the entire actual
companion term. The remaining physical histogram is exactly activation
times the previously constructed rank-one response. -/
theorem completeHistogramResponse_eq_activation_response (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      activation security * FirstResponse.response security (scoreProfile security score) output := by
  rw [completeHistogramResponse_decomposition security score hcentered,
    primaryHistogramResponse_formula security score hcentered, compensatorHistogramResponse_formula]
  simp only [FirstResponse.response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    profileSignMap]
  change _ = activation security * (scoreProfile security score output +
    ((activation security)⁻¹ * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score)) *
      signProfile security output)
  have hactivation := (activation_pos security).ne'
  field_simp
  ring





/-- The unweighted actual leg includes its two off-body outputs and its
attachment output, whose center has the ordinary smoothed body law. -/
def legFirstMean (security : ℕ) (output : Palette security) : ℝ :=
  (∑ primary, (primaryLaw security).weight primary *
      endpointHistogram security (referenceLaw security primary) output) +
    (bodyLaw security true).weight output







end

end CurrentAFT.FirstHistogram

end

section





/-!
# Actual clipped activation and primary heights

A literal subwindow of the same discrete Gaussian lower-bounds its
normalizer. This proves the inverse-width upper bound on the actual
activation, complementing the already proved lower bound. The actual
primary height then follows from its balancing numerator.
-/

namespace CurrentAFT.GaussianHeights

open AFT GaussianSource DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

theorem windowNormalizer_lower (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (width : ℝ) * Real.exp (-Real.pi) ≤ windowNormalizer width cutoff := by
  let point : Fin width → Window cutoff := fun index =>
    ⟨(index.val : ℤ), Finset.mem_Icc.mpr ⟨by omega, by have := index.isLt; omega⟩⟩
  have hinjective : Function.Injective point := by
    intro first second hequal
    apply Fin.ext
    have h := congrArg (fun value : Window cutoff => value.val) hequal
    change (first.val : ℤ) = (second.val : ℤ) at h
    exact_mod_cast h
  have hweight (index : Fin width) : Real.exp (-Real.pi) ≤ weight width (point index) := by
    have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
    have hz : (0 : ℝ) ≤ index.val := Nat.cast_nonneg _
    have hzUpper : (index.val : ℝ) ≤ width := Nat.cast_le.mpr index.isLt.le
    have hsquare : (index.val : ℝ) ^ 2 ≤ (width : ℝ) ^ 2 := by nlinarith
    have hproduct := mul_le_mul_of_nonneg_left hsquare
      (div_nonneg Real.pi_pos.le (sq_nonneg (width : ℝ)))
    have hcancel : Real.pi / (width : ℝ) ^ 2 * (width : ℝ) ^ 2 = Real.pi := by
      field_simp
    rw [hcancel] at hproduct
    unfold weight
    apply Real.exp_le_exp.mpr
    change -Real.pi ≤ -(Real.pi / (width : ℝ) ^ 2) * (index.val : ℝ) ^ 2
    linarith
  have hsubset : Finset.univ.image point ⊆ (Finset.univ : Finset (Window cutoff)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun value _ _ => (weight_pos (width : ℝ) value).le)
  rw [Finset.sum_image (fun first _ second _ hequal => hinjective hequal)] at hsum
  calc
    _ = ∑ _index : Fin width, Real.exp (-Real.pi) := by simp
    _ ≤ ∑ index : Fin width, weight width (point index) :=
      Finset.sum_le_sum (fun index _ => hweight index)
    _ ≤ _ := hsum

theorem windowGaussian_zero_upper (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (windowGaussian width cutoff).weight (windowZero cutoff) ≤ Real.exp Real.pi / width := by
  have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  rw [windowGaussian_zero]
  calc
    _ ≤ 1 / ((width : ℝ) * Real.exp (-Real.pi)) :=
      one_div_le_one_div_of_le (mul_pos hw (Real.exp_pos _))
        (windowNormalizer_lower width cutoff hwidth hcutoff)
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem activation_upper (security : ℕ) :
    DiffuseProfiles.activation security ≤ Real.exp Real.pi / (2 * (Parameters.base security : ℝ)) := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hcutoff : Parameters.base security - 1 ≤ Parameters.sourceCutoff security - 1 := by
    unfold Parameters.sourceCutoff
    have hpower : Parameters.base security ≤ Parameters.base security ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hb (by omega : 1 ≤ 2)
    omega
  have h := mul_le_mul_of_nonneg_left
    (windowGaussian_zero_upper (Parameters.base security) (Parameters.sourceCutoff security - 1)
      (Parameters.base_pos security) hcutoff) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change (1 / 2) * (windowGaussian (Parameters.base security)
    (Parameters.sourceCutoff security - 1)).weight (windowZero _) ≤ _
  exact h.trans_eq (by ring)

theorem primaryProfile_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    primaryProfile security color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  have hfirst : 0 ≤ (freeMass security + markMass security) * (bodyLaw security false).weight color :=
    mul_nonneg (add_nonneg (freeMass_nonneg security) (markMass_pos security).le)
      ((bodyLaw security false).nonneg color)
  have hsecond : 0 ≤ ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
      (bodyLaw security true).weight color :=
    mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ((bodyLaw security true).nonneg color)
  have hthird : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - DiffuseProfiles.activation security) * diffuseMean security color :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by linarith [activation_le_half security])) (diffuseMean_nonneg security color)
  unfold primaryProfile
  calc
    _ ≤ ((Parameters.dimension security : ℝ) / Parameters.modulus security) / markMass security :=
      div_le_div_of_nonneg_right (by linarith) (markMass_pos security).le
    _ = _ := by ring

theorem primaryLaw_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (primaryLaw security).weight color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  simpa only [primaryLaw] using primaryProfile_upper security color

theorem dimension_leg_ratio (security : ℕ) :
    (Parameters.dimension security : ℝ) / Parameters.legCount security ≤
      131074 * (Parameters.base security : ℝ) ^ 32 := by
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos (FirstResponse.base_pos security) _
  apply (div_le_iff₀ hl).mpr
  have hdim : (Parameters.dimension security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  calc
    _ ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := hdim
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow, mul_assoc, ← pow_add]



end

end CurrentAFT.GaussianHeights

end

end


