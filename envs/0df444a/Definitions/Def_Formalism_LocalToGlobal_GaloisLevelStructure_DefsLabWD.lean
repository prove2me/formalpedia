-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLabWD
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsLabWD
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:05.624989+00:00
-- url     : https://prove2.me/theorems/5e5a30b8-1ba7-4be1-800c-8f0f76d951e8
-- title:
--   Defs Lab WD
-- statement:
--   Definitions and structural lemmas for Defs Lab WD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLabWD.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsGal
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Gal
namespace Formalism.L2.NG
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {p n : ℕ} [Fact p.Prime]
  {v : HeightOneSpectrum (𝓞 F)}
def WildAt (A : ValuationSubring Ω) : Set (Ω ≃ₐ[F] Ω) :=
  {σ | σ ∈ Ine (F := F) A ∧ ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}
end Formalism.L2.NG


