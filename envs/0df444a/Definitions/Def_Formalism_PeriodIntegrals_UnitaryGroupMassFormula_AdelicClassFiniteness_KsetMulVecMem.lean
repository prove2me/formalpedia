-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:19.316409+00:00
-- url     : https://prove2.me/theorems/ea073f22-dd0c-4c44-83f0-fe6858912d63
-- title:
--   Kset Mul Vec Mem
-- statement:
--   Definitions and structural lemmas for Kset Mul Vec Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
def StLatFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ R : Finset (Fin I.n → I.E ⊗[I.F] Af I.F), (∀ r ∈ R, r ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ r ∈ R, ∃ z ∈ I.Lf, y - r = (g : I.E ⊗[I.F] Af I.F) • z
end PIW.AdelClassFin


