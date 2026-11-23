-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:49.122718+00:00
-- url     : https://prove2.me/theorems/a8b3ef8c-f38a-4fdc-8a30-280ba843f656
-- title:
--   Exists Integral Ext Is Alg Closed Residue Field
-- statement:
--   Definitions and structural lemmas for Exists Integral Ext Is Alg Closed Residue Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
def Unram (π : W) (R : Subalgebra W Ω) : Prop :=
  (∀ x ∈ R, IsIntegral W x) ∧ (algebraMap W Ω π)⁻¹ ∉ R ∧
    ∀ x ∈ R, x ≠ 0 → ∃ (n : ℕ) (u : Ω), u ∈ R ∧ u⁻¹ ∈ R ∧ x = algebraMap W Ω π ^ n * u
end GlobalTheory.ClosedResidueExt


