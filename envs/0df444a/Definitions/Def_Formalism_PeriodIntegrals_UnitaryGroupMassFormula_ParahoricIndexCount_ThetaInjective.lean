-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:04.365803+00:00
-- url     : https://prove2.me/theorems/542fc22d-f16f-40dc-a2cb-15f5d3288697
-- title:
--   Theta Injective
-- statement:
--   Definitions and structural lemmas for Theta Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.ParahoricIdxZ.W
section A
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
def theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin t) R)
    (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix (Fin (a + t)) (Fin (a + t)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)
variable {ϖ}
end A
end PI.ParahoricIdxZ.W


