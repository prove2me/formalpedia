-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ChevalleyUnits_44a913e24a17d21a
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ChevalleyUnits_44a913e24a17d21a
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:41.06936+00:00
-- url     : https://prove2.me/theorems/71bd2bf0-3d6d-4915-9258-e19f5ab16d5d
-- title:
--   Chevalley Units
-- statement:
--   Definitions and structural lemmas for Chevalley Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChevalleyUnits.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace GlobalTheory.Published
def ChevalleyUnits : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m b : ℕ), 0 < m → 0 < b →
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m
end GlobalTheory.Published


