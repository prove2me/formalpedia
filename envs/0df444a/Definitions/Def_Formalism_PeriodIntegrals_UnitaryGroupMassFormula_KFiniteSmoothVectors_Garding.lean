-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:57.750315+00:00
-- url     : https://prove2.me/theorems/c88b79d9-a134-4086-a2ab-d439b5e2123c
-- title:
--   Garding
-- statement:
--   Definitions and structural lemmas for Garding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/Garding.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Gard
def mMeas (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
attribute [local instance] mMeas
lemma mBorel (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact ⟨rfl⟩
attribute [local instance] mBorel
lemma mBorelN (n : ℕ) : @BorelSpace (Matrix (Fin n) (Fin n) ℂ)
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _ Matrix.normedAddCommGroup)))) (mMeas n) := by
  exact ⟨rfl⟩
attribute [local instance] mBorelN
lemma mLocCpt (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
attribute [local instance] mLocCpt
section Calc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}
end Calc
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def Lsm (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H →L[ℝ] ℂ →L[ℝ] H :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] H →L[ℝ] H).flip
end Gard
end PI.KFinSmoothW


