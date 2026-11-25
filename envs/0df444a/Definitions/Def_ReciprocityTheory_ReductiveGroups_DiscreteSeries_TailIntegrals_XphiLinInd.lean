-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:54:49.137225+00:00
-- url     : https://prove2.me/theorems/7939e43c-fa97-4935-bf69-ef9724971def
-- title:
--   Xphi Lin Ind
-- statement:
--   Definitions and structural lemmas for Xphi Lin Ind, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_uh_inv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_uh_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
section fs
variable {k r : ℕ}
end fs
section meas
variable {k r : ℕ}
theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id
theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const
def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable
def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable
end meas
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities


