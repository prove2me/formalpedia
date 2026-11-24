-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzL2EuclideanIdentification
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzL2EuclideanIdentification
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:30.771822+00:00
-- url     : https://prove2.me/theorems/6ad9f371-5b0f-4bb0-91ab-0e2dda70eb4c
-- title:
--   Schwartz L2 Euclidean Identification
-- statement:
--   Definitions and structural lemmas for Schwartz L2 Euclidean Identification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzL2EuclideanIdentification.lean

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
noncomputable section
namespace GlobalTheory.EuclidTransport
variable (l : Type) [Fintype l]
theorem volume_preserving_ofLp' : MeasurePreserving (@WithLp.ofLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp l
theorem volume_preserving_toLp' : MeasurePreserving (@WithLp.toLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_toLp l
def schwartzTransport : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l :=
  ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ).symm)
    (fun φ => by ext x; rfl) (fun φ => by ext x; rfl)
variable {l}
variable (l)
def l2TransportIsometry : Lp ℂ 2 (volume : Measure (l → ℝ)) →ₗᵢ[ℂ] L2 l :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 (l → ℝ)) (volume_preserving_ofLp' l)
theorem l2TransportIso_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2TransportIsometry l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl
theorem l2TransportIso_surjective : Function.Surjective (l2TransportIsometry l) := by
  intro h
  refine ⟨Lp.compMeasurePreserving (@WithLp.toLp 2 (l → ℝ)) (volume_preserving_toLp' l) h, ?_⟩
  rw [l2TransportIso_apply]
  ext1
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving h (volume_preserving_toLp' l))).trans ?_
  exact Filter.Eventually.of_forall fun x => rfl
def l2Transport : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (l2TransportIsometry l) (l2TransportIso_surjective l)
variable {l}
end GlobalTheory.EuclidTransport


