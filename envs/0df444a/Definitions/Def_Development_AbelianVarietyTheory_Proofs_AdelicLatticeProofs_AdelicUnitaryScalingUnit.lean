-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:56.863364+00:00
-- url     : https://prove2.me/theorems/38724606-df8a-4902-81f9-89166fadc02d
-- title:
--   Adelic Unitary Scaling Unit
-- statement:
--   Definitions and structural lemmas for Adelic Unitary Scaling Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep
noncomputable def adEval (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
end GlobalTheory.UnRep


