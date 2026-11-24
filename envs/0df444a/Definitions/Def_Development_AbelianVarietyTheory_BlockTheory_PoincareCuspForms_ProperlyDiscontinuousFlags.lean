-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ProperlyDiscontinuousFlags
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ProperlyDiscontinuousFlags
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:10.332293+00:00
-- url     : https://prove2.me/theorems/e55086c2-8f5e-4a35-bdb4-59bc07bc55d5
-- title:
--   Properly Discontinuous Flags
-- statement:
--   Definitions and structural lemmas for Properly Discontinuous Flags, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/ProperlyDiscontinuousFlags.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def flagTransporter (X : Data E r) (K L : Set (Frame X.Ψ r)) : Set (GL (Fin r) E) :=
  {γ | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ L, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul y b}
def ProperlyDiscontinuousOnFlags (X : Data E r) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom → (flagTransporter X K K).Finite
end GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags


