-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:45.746132+00:00
-- url     : https://prove2.me/theorems/bfde88cd-79f8-422e-936c-149fcc6e2736
-- title:
--   Norm Eq Zpow Of Mem Max Unramified Subfield
-- statement:
--   Definitions and structural lemmas for Norm Eq Zpow Of Mem Max Unramified Subfield, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
namespace GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
def rootRing (l : ℕ) [Fact l.Prime] (m : ℕ) : Subalgebra ℤ_[l] (Om l) :=
  Algebra.adjoin ℤ_[l] {x : Om l | x ^ m = 1}
end GlobalTheory.UnramValue


