-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:24.21778+00:00
-- url     : https://prove2.me/theorems/7fcb6a94-8250-4ce4-b24c-687ed7aaad54
-- title:
--   Source Split Evaluation
-- statement:
--   Definitions and structural lemmas for Source Split Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem sourceSplitAbovePlace_sourceStepEmbedding_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    GlobalPlace.RegularAt (sourceSplitAbovePlace Q P x hx c)
      (sourceStepEmbedding P x hx f) := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  have hle := H.valuation_le_one (K := L) (algebraMap O S fO)
  change H.valuation L (sourceStepEmbedding P x hx f) ≤ 1
  exact hle
theorem sourceSplitAbovePlace_sourceStepCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (sourceSplitAbovePlace Q P x hx c)
      (sourceStepCoordinate P x hx) := by
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  have hle := H.valuation_le_one (K := L)
    (sourceSplitIntegralCoordinate Q P x hx hregular hsplit)
  change H.valuation L (sourceStepCoordinate P x hx) ≤ 1
  exact hle
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


