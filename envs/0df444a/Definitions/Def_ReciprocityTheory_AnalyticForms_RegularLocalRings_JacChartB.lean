-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:01.800815+00:00
-- url     : https://prove2.me/theorems/279537e1-f8ee-4b18-9982-f5b5ee99b8d5
-- title:
--   Jac Chart B
-- statement:
--   Definitions and structural lemmas for Jac Chart B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_le_ptIdeal_of_nontrivial
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
section
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]
theorem lin_mem_max (i : Fin n) : psi p K (X i - C (p i)) ∈ maximalIdeal (locR K p) :=
  (psi_mem_max_iff (K := K) (p := p) (le_ptIdeal_of_nontrivial (K := K) (p := p)) _).mpr
  (by rw [ptI, RingHom.mem_ker]; simp)
def Phi : (Fin n → ℂ) →ₗ[ℂ] CotangentSpace (locR K p) where
  toFun c := ∑ i, c i • (maximalIdeal (locR K p)).toCotangent ⟨_, lin_mem_max p K i⟩
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]
instance : IsScalarTower ℂ (ResidueField (locR K p)) (CotangentSpace (locR K p)) := by
  refine IsScalarTower.of_algebraMap_smul fun c y => ?_
  rw [IsScalarTower.algebraMap_apply ℂ (locR K p) (ResidueField (locR K p)),
    algebraMap_smul, algebraMap_smul]
end
variable {n : ℕ}
end
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt


