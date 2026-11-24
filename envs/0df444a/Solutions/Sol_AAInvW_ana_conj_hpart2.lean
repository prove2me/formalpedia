-- Prove2me | solution 1 for AAInvW.ana_conj_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:10.802499+00:00
-- url     : https://prove2.me/submissions/f89f736d-5e58-4252-84d6-7cd23207dc95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_unitInv
import Theorems.Thm_AAInvW_ana_HH_left
import Theorems.Thm_AAInvW_ana_hpart2_eq


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
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : s⁻¹ * hpart2 H Z * s = hpart2 H (s⁻¹ * Z * s) := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  rw [ana_unitInv hH hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.1, Matrix.mul_assoc, ana_HH_left hH,
    hH.2, Matrix.mul_one]
end AAInvW
