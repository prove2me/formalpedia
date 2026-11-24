-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:15.071367+00:00
-- url     : https://prove2.me/theorems/173531e2-5306-491c-8793-b6fa806be4be
-- title:
--   Character Eq Of Rep Iso
-- statement:
--   Definitions and structural lemmas for Character Eq Of Rep Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/CharacterEqOfRepIso.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
namespace PI.SerBridgeGLW
section
variable {G : Type} [Group G] [Fintype G]
def repOfGL {n : ℕ} (ρ : G →* GL (Fin n) ℂ) : FDRep ℂ G :=
  FDRep.of (((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ)).toRingEquiv.toMonoidHom).comp
    ((Units.coeHom _).comp ρ))
end
end PI.SerBridgeGLW


