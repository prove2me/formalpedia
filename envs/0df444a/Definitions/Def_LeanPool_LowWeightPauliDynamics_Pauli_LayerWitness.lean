-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:15.571288+00:00
-- url     : https://prove2.me/theorems/f01009a2-cc80-466f-8e53-f466cb9b6b8b
-- title:
--   Layer Witness
-- statement:
--   Definitions and structural lemmas for Layer Witness, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
def branch (G p : PauliString n) : Finset (PauliString n) :=
  if sympForm G p = 1 then {p, phaseMul 1 (G * p)} else {p}
def oneLayer : (L : List (PauliString n)) → (p : PauliString n) → Finset (PauliString n)
  | [], p => {p}
  | G :: Gs, p => (branch G p).biUnion (oneLayer Gs)
def reachable : (layers : List (List (PauliString n))) → (p : PauliString n) →
    Finset (PauliString n)
  | [], p => {p}
  | L :: Ls, p => (oneLayer L p).biUnion (reachable Ls)
structure IsLayer (kh : ℕ) (L : List (PauliString n)) : Prop where
  /-- Distinct generators of the layer act on disjoint sets of qubits. -/
  disjoint : L.Pairwise fun G H => Disjoint (support G) (support H)
  /-- Every generator is `k_h`-local. -/
  weight_le : ∀ G ∈ L, weight G ≤ kh
def hitting (L : List (PauliString n)) (S : Finset (Fin n)) : Finset (PauliString n) :=
  L.toFinset.filter fun G => (support G ∩ S).Nonempty
def cover (L : List (PauliString n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ (hitting L S).biUnion support
def X (i : Fin n) : PauliString n := ⟨fun j => if j = i then 1 else 0, 0, 0⟩
def Z (i : Fin n) : PauliString n := ⟨0, fun j => if j = i then 1 else 0, 0⟩
end PauliString
namespace LayerWitness
open PauliString
def L₁ : List (PauliString 8) := [X 0 * Z 1, X 2 * X 3, Z 4 * X 5, X 6 * X 7]
def L₂ : List (PauliString 8) := [X 1 * Z 2, X 3 * X 4, X 5 * X 6]
def P₄ : PauliString 8 := ⟨![0, 1, 1, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], 1⟩
def P₆ : PauliString 8 := ⟨![1, 1, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], 3⟩
end LayerWitness
end Lean4LPD


