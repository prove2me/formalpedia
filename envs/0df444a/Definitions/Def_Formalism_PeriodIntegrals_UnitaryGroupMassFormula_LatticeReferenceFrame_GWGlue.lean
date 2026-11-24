-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:57.919105+00:00
-- url     : https://prove2.me/theorems/6fea83eb-1cd8-4860-840b-9457a4fa9832
-- title:
--   GWGlue
-- statement:
--   Definitions and structural lemmas for GWGlue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.GWG
open PI.ScRefExists.Sk
section Lemmas
variable (I : Formalism.MainNotions.S.AutInst)
def SS (r k M : ℕ) (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (z : Fin I.n → I.E)
    (b bd : Fin k → Fin I.n → I.E) : Set (Fin I.n → I.E) :=
  Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
    Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)
end Lemmas
end PI.ScRefExists.GWG
end


