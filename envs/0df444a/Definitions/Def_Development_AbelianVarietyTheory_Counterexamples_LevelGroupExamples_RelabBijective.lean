-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:59.528437+00:00
-- url     : https://prove2.me/theorems/47a126ee-4174-472b-8958-6d8c0ba06eba
-- title:
--   Relab Bijective
-- statement:
--   Definitions and structural lemmas for Relab Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnifDataTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
theorem conj_mem (X : Data E r) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) : conjEmb τ ∈ X.Ψ := by
  by_contra h'
  exact h ((X.cmType τ).2 h')
end GlobalTheory.UnifDataTest


