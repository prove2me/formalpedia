-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:44.4152+00:00
-- url     : https://prove2.me/theorems/86da46ce-d1f3-47d0-befc-f7fd7ecc7003
-- title:
--   Block Main
-- statement:
--   Definitions and structural lemmas for Block Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
section Side
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ} {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V}
  {Γ : Matrix (Fin n) (Fin n) K}
end Side
end PI.Dv.TIW


