-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:55.745539+00:00
-- url     : https://prove2.me/theorems/3eff288d-a617-48ca-9ad5-d9edc60aa846
-- title:
--   Lat Count All Of
-- statement:
--   Definitions and structural lemmas for Lat Count All Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
theorem mem_gf (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (g : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := γ.2
def gm (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) : Matrix (Fin I.n) (Fin I.n) I.E :=
  (((mem_gf I γ).choose : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)
end PI.UnitaryGroupMassFormula.LCG


