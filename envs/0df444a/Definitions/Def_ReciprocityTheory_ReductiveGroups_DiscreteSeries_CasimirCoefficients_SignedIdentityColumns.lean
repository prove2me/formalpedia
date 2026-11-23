-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:40.618562+00:00
-- url     : https://prove2.me/theorems/344fc17a-7021-4a9b-bc1d-872dd2c29375
-- title:
--   Signed Identity Columns
-- statement:
--   Definitions and structural lemmas for Signed Identity Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
abbrev SgIxV (ε : Fin n → Bool) (s : Bool) : Type := {a : Fin n // ε a = s}
section supnorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end supnorm
def hsRV {Q : Type} [Fintype Q] (x : Matrix (Fin n) Q ℂ) : ℝ := ∑ i, ∑ j, ‖x i j‖ ^ 2
def signedIdentityColumns (ε : Fin n → Bool) (s : Bool) : Matrix (Fin n) (SgIxV ε s) ℂ := fun a b => if a = b.1 then 1 else 0
def LcV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) Q ℂ →ₗ[ℂ] Matrix (Fin n) Q ℂ where
  toFun x := g * x
  map_add' := Matrix.mul_add g
  map_smul' c x := by simp
abbrev REV (n : ℕ) (Q : Type) := Fin n → Q → ℂ
def ReV (n : ℕ) (Q : Type) : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ := Matrix.ofLinearEquiv ℝ
def RLV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : REV n Q →ₗ[ℝ] REV n Q :=
  ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
    ((ReV n Q : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ) : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ)
section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
end frob
end ReciprocityTheory.ChartRestriction.DS.S7


