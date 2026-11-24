-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterEqOfRange
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterEqOfRange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:06.224161+00:00
-- url     : https://prove2.me/theorems/83b23270-cb68-48c3-89a7-01159298127a
-- title:
--   Iter Eq Of Range
-- statement:
--   Definitions and structural lemmas for Iter Eq Of Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/IterEqOfRange.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Eqv
open scoped ContDiff
open MeasureTheory
section Pt
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def ev {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1
noncomputable def dS {k : ℕ} (g : (Fin k → ℝ) → ℂ) (S : Finset (Fin k)) (t : Fin k → ℝ) : ℂ :=
  iteratedFDeriv ℝ S.card g t (fun a => ev (S.orderEmbOfFin rfl a))
end Pt
end Formalism.IndefR.Eqv


