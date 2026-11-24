-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:04.893731+00:00
-- url     : https://prove2.me/theorems/32d5dd2c-264a-4c68-8db0-b99faf967855
-- title:
--   Modulus Rigidity
-- statement:
--   Definitions and structural lemmas for Modulus Rigidity, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ModulusRigidity.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
namespace HermitekLEAN
def finiteCoeffSeq {d : ℕ} (a : Fin (d + 1) → ℂ) : ℕ → ℂ :=
  fun n => if h : n < d + 1 then a ⟨n, h⟩ else 0
def finitePositiveModeMainSum
    (k d : ℕ) (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) (r : ℝ) : ℂ :=
  ∑ i : Fin (d + 1),
    star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
      (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
        ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ)))
def finitePositiveModeErrorSum
    (k d : ℕ) (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) (r : ℝ) : ℂ :=
  ∑ i : Fin (d + 1),
    if h : d - n.1 ≤ i.1 then
      star (b ⟨i.1 - (d - n.1), by
        have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
        omega⟩) * a i *
        (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
          ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
    else 0
end HermitekLEAN


