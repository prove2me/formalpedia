-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:13.951852+00:00
-- url     : https://prove2.me/theorems/fc973fda-8281-4706-8389-4e5aa51479ef
-- title:
--   Aniso Peel
-- statement:
--   Definitions and structural lemmas for Aniso Peel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/AnisoPeel.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
namespace DensInertW
open DensInertW.Sub
section
variable {L : Type} [Field L]
def anP {n m : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (B : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L) : Prop :=
  (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧ ∀ i j, hf q M (X i) (X j) = B i j
end
end DensInertW


