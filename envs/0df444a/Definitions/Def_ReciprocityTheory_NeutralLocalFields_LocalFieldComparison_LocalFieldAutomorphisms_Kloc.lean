-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:02.740121+00:00
-- url     : https://prove2.me/theorems/d3ee28c6-a0c6-4bbd-899a-dc6687bf41cf
-- title:
--   Kloc
-- statement:
--   Definitions and structural lemmas for Kloc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Kloc.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
variable {Ω : Type} [Field Ω] (p : ℕ) [Fact p.Prime]
def Compat (A : ValuationSubring Ω) (ι : Ω →+* PadicAlgCl p) : Prop := ∀ x, x ∈ A ↔ ‖ι x‖ ≤ 1
variable {p}
def Kloc (F : Type) [Field F] [Algebra F Ω] (ι : Ω →+* PadicAlgCl p) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))
abbrev GK (F : Type) [Field F] [Algebra F Ω] (ι : Ω →+* PadicAlgCl p) := PadicAlgCl p ≃ₐ[Kloc F ι] PadicAlgCl p
end ReciprocityTheory.Neutral.Cmp


