-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CharFnLocallyConstant
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CharFnLocallyConstant
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:13.890309+00:00
-- url     : https://prove2.me/theorems/20f30eb5-43a7-478f-a1b4-5745dc0bb13c
-- title:
--   Char Fn Locally Constant
-- statement:
--   Definitions and structural lemmas for Char Fn Locally Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CharFnLocallyConstant.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder
namespace GlobalTheory.CharIdem
section
variable {G : Type} [Group G]
open Classical in

noncomputable def charFn (K : Subgroup G) (χ : K →* Circle) (c : ℝ) : G → ℂ :=
  fun x => if h : x ∈ K then star ((χ ⟨x, h⟩ : Circle) : ℂ) / (c : ℂ) else 0
variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
end
end GlobalTheory.CharIdem


