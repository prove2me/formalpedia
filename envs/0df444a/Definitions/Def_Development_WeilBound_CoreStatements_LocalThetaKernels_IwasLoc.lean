-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
-- name    : Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:18.642553+00:00
-- url     : https://prove2.me/theorems/7d51b63b-6e02-4924-b1ee-32f60be8229e
-- title:
--   Iwas Loc
-- statement:
--   Definitions and structural lemmas for Iwas Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
def ee (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (m + m) := (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv
section
variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]
end
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
end PositivityTheory.ThKH.Iwas


