-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:44.418352+00:00
-- url     : https://prove2.me/theorems/e25707c1-3929-4b7f-8bae-a5a76fb63aee
-- title:
--   Chosen Eq Of All Rules
-- statement:
--   Definitions and structural lemmas for Chosen Eq Of All Rules, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ChosenEqOfAllRules.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SupNormExample
open Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }
end GlobalTheory.SupNormExample


