-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:01.636798+00:00
-- url     : https://prove2.me/theorems/aba0a2bd-807e-401c-88bf-589e5625a251
-- title:
--   Irreducible Of Minimal
-- statement:
--   Definitions and structural lemmas for Irreducible Of Minimal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
section Irr
variable {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
end Irr
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
end PI.GGMatBoundW


