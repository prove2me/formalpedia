-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:33.815822+00:00
-- url     : https://prove2.me/theorems/399060ce-f5fe-5fb1-b983-3d195c8b7224
-- title:
--   Exists Isom Self Dual
-- statement:
--   Definitions and structural lemmas for Exists Isom Self Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsIsomSelfDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
section Abs
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
def PairUnit (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ w y : V, h y w = 1 → h w w ∈ S → h y y ∈ S →
    ∃ c ∈ S, ∃ d ∈ S, IsUnitIn S (h (c • w + d • y) (c • w + d • y))
end Abs
end PI.UnitaryGroupMassFormula.CntFormula.UG


