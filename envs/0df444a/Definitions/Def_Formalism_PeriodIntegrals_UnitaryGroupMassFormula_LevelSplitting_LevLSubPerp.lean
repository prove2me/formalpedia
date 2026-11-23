-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:59.799817+00:00
-- url     : https://prove2.me/theorems/d04b34e4-b40b-4bd5-97d5-bba90e7d9654
-- title:
--   Lev LSub Perp
-- statement:
--   Definitions and structural lemmas for Lev LSub Perp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
def pV (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv
def levL (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) : (n → A) →ₗ[A] (n → A) :=
  pV D + ∑ a, ∑ b, U a b • (D.hL (D.f b)).smulRight (D.e a) +
    ∑ d, ∑ b, W d b • (D.hL (D.e b)).smulRight (D.f d)
variable {D : Dat A n r}
section Hyp
variable (H : D.Hyp)
include H
end Hyp
end PI.LevelKSplit.W.NCL


