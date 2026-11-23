-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:34.661906+00:00
-- url     : https://prove2.me/theorems/a4dd08a7-661d-49f9-ac3f-e55fafaaceb3
-- title:
--   Exists Alg Hom Of Is Transcendence Basis
-- statement:
--   Definitions and structural lemmas for Exists Alg Hom Of Is Transcendence Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomOfIsTranscendenceBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
abbrev Gen (F I : Type) [Field F] : Type := AlgebraicClosure (FractionRing (MvPolynomial I F))
def genX (F I : Type) [Field F] : I → Gen F I := fun i => algebraMap (MvPolynomial I F) _ (X i)
end GlobalTheory.GenericValue


