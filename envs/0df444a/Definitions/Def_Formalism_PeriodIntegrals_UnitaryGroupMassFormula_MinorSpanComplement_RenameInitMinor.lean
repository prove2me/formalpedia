-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:47.136924+00:00
-- url     : https://prove2.me/theorems/c7aaef55-9b9c-4a2b-a646-2a2b44df7fef
-- title:
--   Rename Init Minor
-- statement:
--   Definitions and structural lemmas for Rename Init Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace PI.MSC
def phi (N n : ℕ) : Fin N × Fin n → ℕ × Fin N := fun v => ((v.2 : ℕ), v.1)
def gen (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram)
    (I : ∀ c : Fin (ν.rowLen 0), Fin (ν.colLen c) ↪o Fin N) :
    MvPolynomial (Fin N × Fin (ν.colLen 0)) R :=
  bideterminant R (sz0 ν) (hsz0 ν) fun c => I c
end PI.MSC


