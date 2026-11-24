-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:33.608862+00:00
-- url     : https://prove2.me/theorems/922194fc-f005-44ce-b0cb-e0802ba88eb3
-- title:
--   Exists Index Ideal
-- statement:
--   Definitions and structural lemmas for Exists Index Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
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
namespace GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Lat
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)
def Bdd (M : Submodule (𝓞 E) (Fin n → E)) : Prop := ∃ k : 𝓞 E, k ≠ 0 ∧ ∀ v ∈ M, k • v ∈ stdLat E n
end Lat
section Push
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)
end Push
end GlobalTheory.BetaEx


