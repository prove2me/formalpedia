-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:42.266823+00:00
-- url     : https://prove2.me/theorems/cf829415-92c1-4fbb-9eba-a1c51cb30490
-- title:
--   Pat Entry Zero
-- statement:
--   Definitions and structural lemmas for Pat Entry Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
def Pat (k r : ℕ) (l : Fin r) (Z : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), Z i j ≠ 0 →
    (i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
    (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val)
def dag (k r : ℕ) (Z : Mx k r) : Mx k r := (Hpk k r)⁻¹ * Zᴴ * Hpk k r
lemma ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    ell k r z (A + B) = ell k r z A + ell k r z B := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.add_mulVec]
lemma ell_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (A : Mx k r) :
    ell k r z (c • A) = c * ell k r z A := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.smul_mulVec]
lemma ell_rsmul (z : Fin (2 * r + k + 1) → ℂ) (c : ℝ) (A : Mx k r) :
    ell k r z (c • A) = (c : ℂ) * ell k r z A := by
  rw [← ell_smul, Complex.coe_smul]
def ellL (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℝ] ℂ where
  toFun := ell k r z
  map_add' := ell_add z
  map_smul' c A := by rw [ell_rsmul, RingHom.id_apply, Complex.real_smul]
end Formalism.FourierDecayAlt.Q.QRR


