-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:16:58.229165+00:00
-- url     : https://prove2.me/theorems/b84450d4-9d7e-478e-bda3-8774519ef8df
-- title:
--   Representative
-- statement:
--   Definitions and structural lemmas for Representative, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta1
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def qConstant (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    BDL26Field →ₗ[BDL26Field] (localCq P S q).middleCocycleCode.carrier where
  toFun b := ⟨fun _ => b, by
    change wordLinearMapTranspose (localCq P S q).boundary2 (fun _ => b) = 0
    rw [localCq, reindex_delta1]
    change wordEquiv (qSyndromeEquiv P S q)
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun _ => b)) = 0
    have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun _ => b) = 0 := by
      funext e
      rw [qDoubleCylinderBoundary1, wordLinearMapTranspose_graphBoundary_apply]
      exact ZModModule.add_self b
    rw [hz, map_zero]⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl
noncomputable def qRepresentative (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    (localCq P S q).middleCohomology →ₗ[BDL26Field]
      (localCq P S q).middleCocycleCode.carrier :=
  (qConstant P S q).comp (localCqCohomologyEquiv P A S q).toLinearMap
noncomputable def qCohomologyEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    (∀ q : P.Q, (localCq P S q).middleCohomology) ≃ₗ[BDL26Field] Word BDL26Field P.Q where
  toFun h q := localCqCohomologyEquiv P A S q (h q)
  invFun w q := (localCqCohomologyEquiv P A S q).symm (w q)
  left_inv h := by funext q; exact LinearEquiv.symm_apply_apply _ _
  right_inv w := by funext q; exact LinearEquiv.apply_symm_apply _ _
  map_add' a b := by funext q; exact map_add _ _ _
  map_smul' c a := by funext q; exact map_smul (localCqCohomologyEquiv P A S q) c (a q)
end QEC.Coding.BDL26RXDecoderAdapter


