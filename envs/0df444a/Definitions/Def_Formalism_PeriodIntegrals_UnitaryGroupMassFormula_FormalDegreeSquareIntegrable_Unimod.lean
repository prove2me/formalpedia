-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:00.058807+00:00
-- url     : https://prove2.me/theorems/b029c466-432e-48be-bc2d-5caa68859ba0
-- title:
--   Unimod
-- statement:
--   Definitions and structural lemmas for Unimod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
section Abstract
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
end Abstract
section Matrices
variable {n : ℕ} (ε : Fin n → Bool)
def mkU (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : UJ ε :=
  ⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg), coeMatrix_left_inv ε g hg⟩, hg⟩
end Matrices
end PIW.HCFdeg


