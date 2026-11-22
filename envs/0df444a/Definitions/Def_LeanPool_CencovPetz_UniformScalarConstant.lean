-- Prove2me | Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
-- name    : LeanPool_CencovPetz_UniformScalarConstant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:28:18.026259+00:00
-- url     : https://prove2.me/theorems/071ed775-84a1-4995-b843-ead1113558b7
-- title:
--   Uniform Scalar Constant
-- statement:
--   Definitions and structural lemmas for Uniform Scalar Constant, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarConstant.lean

module
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_self
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_coe
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_self
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
namespace MonotoneMetricFamily
open MarkovMorphism TangentFin
noncomputable def uniformScalar (G : MonotoneMetricFamily) (n : ℕ) (hn : 2 ≤ n) : ℝ := by
  classical
  let i0 : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le Nat.one_lt_two hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  exact
    (TangentFin.Bilin.B (G := G) (n := n) (TangentFin.Basis.dij (n := n) i0 i1)
          (TangentFin.Basis.dij (n := n) i0 i1) /
        (2 * (Fintype.card (Fin n) : ℝ)))
lemma two_le_card_prod {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    2 ≤ Fintype.card (Fin n × Fin m) := by
  classical
  -- `card (Fin n × Fin m) = n * m`.
  simpa [Fintype.card_prod, Fintype.card_fin] using
    (le_trans hn (Nat.le_mul_of_pos_right n hm))
end MonotoneMetricFamily
end LeanPool.CencovPetz


