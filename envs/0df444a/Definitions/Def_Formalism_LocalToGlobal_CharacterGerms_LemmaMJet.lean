-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
-- name    : Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:00.757475+00:00
-- url     : https://prove2.me/theorems/b6eb168a-1f0a-5085-ac5c-f04eded79730
-- title:
--   Lemma MJet
-- statement:
--   Definitions and structural lemmas for Lemma MJet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
def linT [Fintype σ] (M : τ → σ → C) : MvPolynomial τ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun c => ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w
end Formalism.L2.FormalSeriesBounds


