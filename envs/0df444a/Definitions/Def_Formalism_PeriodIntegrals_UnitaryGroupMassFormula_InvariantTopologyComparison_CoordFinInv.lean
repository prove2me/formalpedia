-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFinInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFinInv
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:53:38.770458+00:00
-- url     : https://prove2.me/theorems/49f72d7a-ed62-4f46-9e46-9171a7385feb
-- title:
--   Coord Fin Inv
-- statement:
--   Definitions and structural lemmas for Coord Fin Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFinInv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
def finCoordL (j : Fin 2) : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) →ₗ[I.F] Formalism.MainNotions.S.Af I.F :=
  (TensorProduct.lid I.F (Formalism.MainNotions.S.Af I.F)).toLinearMap ∘ₗ
    ((basisE I).coord j).rTensor (Formalism.MainNotions.S.Af I.F)
def sumsInt : AddSubgroup (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  AddSubgroup.closure {x | ∃ o ∈ Formalism.UG.intOE I.E, ∃ a ∈ Formalism.UG.intAd I.F, x = o ⊗ₜ[I.F] a}
end PI.InvTopW


