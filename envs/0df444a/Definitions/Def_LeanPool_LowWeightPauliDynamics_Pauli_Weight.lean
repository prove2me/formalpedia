-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Weight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:55.334795+00:00
-- url     : https://prove2.me/theorems/3f9d33ae-8c21-4429-9502-a54dde978258
-- title:
--   Weight
-- statement:
--   Definitions and structural lemmas for Weight, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
def site (s : PauliString n) (i : Fin n) : ZMod 2 × ZMod 2 := (s.x i, s.z i)
def support (s : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => site s i ≠ 0)
def weight (s : PauliString n) : ℕ := (support s).card
def cancelSites (G s : PauliString n) : Finset (Fin n) := support s \ support (G * s)
def createSites (G s : PauliString n) : Finset (Fin n) := support (G * s) \ support s
def antiSites (G s : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i)
variable {kh : ℕ}
end PauliString
end Lean4LPD


