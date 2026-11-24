-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulMemSpanOfFiniteQuot
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulMemSpanOfFiniteQuot
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:20.775071+00:00
-- url     : https://prove2.me/theorems/033dd69f-01b5-428e-80f0-f6ffa46827db
-- title:
--   Exists XPow Smul Mem Span Of Finite Quot
-- statement:
--   Definitions and structural lemmas for Exists XPow Smul Mem Span Of Finite Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsXPowSmulMemSpanOfFiniteQuot.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
namespace GlobalTheory
open GradedHilbert Pointwise
section
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (i : ι)
variable [Decomposition ℳ]
end
end GlobalTheory


