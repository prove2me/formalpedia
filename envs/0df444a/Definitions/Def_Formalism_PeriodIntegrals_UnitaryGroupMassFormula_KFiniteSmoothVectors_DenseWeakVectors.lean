-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:10.018315+00:00
-- url     : https://prove2.me/theorems/bc935a67-6245-4b02-89df-5d5aacee0314
-- title:
--   Dense Weak Vectors
-- statement:
--   Definitions and structural lemmas for Dense Weak Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Dense
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def qd (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
end Dense
end PI.KFinSmoothW


