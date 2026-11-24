-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:43:15.291646+00:00
-- url     : https://prove2.me/theorems/e3547ef5-90b9-419c-8100-191329cece05
-- title:
--   GGEq
-- statement:
--   Definitions and structural lemmas for GGEq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/GGEq.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
noncomputable def GG {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M) (β β' a a' : Fin (m + 2) → ℂ) : M :=
  ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
    (sgnL c id * sgnL d id * (β (c 0) * β' (c 1)) * (a (d 0) * a' (d 1))) •
      F (fun k => c k.succ.succ) (fun k => d k.succ.succ)
end PI.QnCovHat2W


