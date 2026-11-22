-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Tensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:38.541646+00:00
-- url     : https://prove2.me/theorems/cea39d0d-74e5-4aca-9f9b-79942fdaa29e
-- title:
--   Tensor
-- statement:
--   Definitions and structural lemmas for Tensor, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_card_bits

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.PauliString
open Matrix Finset
def qubitX : Matrix (ZMod 2) (ZMod 2) ℂ := ![![0, 1], ![1, 0]]
def qubitY : Matrix (ZMod 2) (ZMod 2) ℂ := ![![0, -Complex.I], ![Complex.I, 0]]
def qubitZ : Matrix (ZMod 2) (ZMod 2) ℂ := ![![1, 0], ![0, -1]]
def qubitPauli (x z : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  if x = 0 then (if z = 0 then 1 else qubitZ) else (if z = 0 then qubitX else qubitY)
noncomputable def qubitXZ (x z : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun a b => if a = b + x then negOnePow (z * b) else 0
def yPhase {n : ℕ} (x z : Bits n) : ZMod 4 := ∑ i, ((x i * z i).val : ZMod 4)
noncomputable def tensorPauli : (n : ℕ) → Bits n → Bits n → Matrix (Bits n) (Bits n) ℂ
  | 0, _, _ => 1
  | n + 1, x, z =>
      Matrix.reindex (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2))
        (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2))
        ((qubitPauli (x 0) (z 0)).kronecker (tensorPauli n (Fin.tail x) (Fin.tail z)))
def dropFirst {n : ℕ} (s : PauliString (n + 1)) : PauliString n :=
  ⟨Fin.tail s.x, Fin.tail s.z, s.phase⟩
def tensorRepresentative {n : ℕ} (p : PauliIndex n) : PauliString n :=
  ⟨p.1, p.2, yPhase p.1 p.2⟩
noncomputable def bitsEquivFin (n : ℕ) : Bits n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (card_bits n)
noncomputable def bitsMatrixEquiv (n : ℕ) :
    Matrix (Bits n) (Bits n) ℂ ≃ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n)
end Lean4LPD.PauliString


