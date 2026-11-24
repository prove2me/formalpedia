-- Prove2me | Definitions.Def_HodgeComputerSSR_CoverE0
-- name    : HodgeComputerSSR_CoverE0
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T09:21:33.665804+00:00
-- url     : https://prove2.me/theorems/00146417-5ce3-43be-bced-2f525842f94e
-- title:
--   Quadratic cover polynomial $E_0(W) = W^2 + b_W(U) W + c_W(U)$ over $\operatorname{RatFunc}(K_5)$
-- statement:
--   Defines the quadratic polynomial $E_{0,\mathrm{poly}} = W^2 + b_W(U) W + c_W(U) \in \operatorname{RatFunc}(K_5)[W]$ and unpacks all 19 coprimalities from `cover_coprimalities_Q5` and `cover_coprimalities_P34`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L1-L260

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.CoverAlgebra QuadraticCovers Polynomial

abbrev toRat : K5[X] →+* RatFunc K5 := algebraMap K5[X] (RatFunc K5)

def E0_poly : (RatFunc K5)[X] :=
  X ^ 2 + C (toRat k5Params.bW) * X + C (toRat k5Params.cW)

lemma E0_poly_monic : E0_poly.Monic := by
  rw [E0_poly]
  have hdeg : (C (toRat k5Params.bW) * X + C (toRat k5Params.cW)).degree < (X ^ 2 : (RatFunc K5)[X]).degree := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
    · exact lt_of_le_of_lt degree_C_le (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
  rw [add_assoc]
  exact (monic_X_pow 2).add_of_left hdeg

lemma E0_poly_natDegree : E0_poly.natDegree = 2 := by
  rw [E0_poly, add_assoc]
  have hdeg : (C (toRat k5Params.bW) * X + C (toRat k5Params.cW)).natDegree < 2 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)
    · simp
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hdeg), natDegree_X_pow]


end SymmetricSexticResidual.CoverResidue


