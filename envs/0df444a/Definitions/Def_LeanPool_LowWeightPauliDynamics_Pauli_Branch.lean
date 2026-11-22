-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Branch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:17:35.607634+00:00
-- url     : https://prove2.me/theorems/f06d076f-bbe9-4fb9-838a-f2066e26f779
-- title:
--   Branch
-- statement:
--   Definitions and structural lemmas for Branch, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_anticommute
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_self_of_isSelfAdjoint

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
example (G s : PauliString n) (hG : IsSelfAdjoint G) (h : sympForm G s = 1) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • (toMatrix G * toMatrix s) :=
  rot_conj_of_anticommute (toMatrix_mul_self_of_isSelfAdjoint hG) (toMatrix_anticommute h)
end PauliString
end Lean4LPD


