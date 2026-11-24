-- Prove2me | solution 1 for AAInvW.conjugated_generator_gl_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:10:59.311998+00:00
-- url     : https://prove2.me/submissions/c383fbf1-05cf-4cbf-b4aa-dff7aeba9a09

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_Ec_sub
import Theorems.Thm_AAInvW_ana_Ec_zero
import Theorems.Thm_AAInvW_ana_EcComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AAInvW
theorem _root_.solution : EabHGl := by
  unfold EabHGl
  intro n H E _ _ f a b c d g hH hf hg
  have hE : ∀ (i j : Fin n) (φ : Matrix (Fin n) (Fin n) ℂ → E),
      EabH H i j φ = EcH H (Matrix.single i j (1 : ℂ)) φ := fun _ _ _ => rfl
  have hm : ∀ (i j k l : Fin n), Matrix.single i j (1 : ℂ) * Matrix.single k l 1 =
      if j = k then Matrix.single i l 1 else 0 := by
    intro i j k l
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      first
      | rw [Matrix.single_mul_single_same, mul_one]
      | (ext p q; simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'])
    · rw [if_neg hjk]
      first
      | exact Matrix.single_mul_single_of_ne hjk _ _
      | (ext p q; simp [Matrix.mul_apply, Matrix.single_apply, ite_and, hjk, Finset.sum_ite_eq,
          Finset.sum_ite_eq'])
  simp only [hE]
  rw [ana_EcComm hH f _ _ g hf hg, ana_Ec_sub hH hf hg, hm, hm]
  split_ifs <;> simp [ana_Ec_zero]
end AAInvW
