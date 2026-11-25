-- Prove2me | Definitions.Def_LovaszTheta_Solution
-- name    : LovaszTheta_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:37:17.973412+00:00
-- url     : https://prove2.me/theorems/0104b516-9e24-41ea-be66-eacb7b01bff6
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/lovasz-theta; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lovasz theta bound and Shannon capacity of the 5-cycle development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ShannonCapacity
variable {V : Type*}
def strongPow (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm SimpleGraph.Adj.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
def IsOrthonormalRep (G : SimpleGraph V) {d : ℕ} (u : V → Fin d → ℝ) : Prop :=
  (∀ i, dotProduct (u i) (u i) = 1) ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → dotProduct (u i) (u j) = 0
noncomputable def shannonCapacity [Fintype V] (G : SimpleGraph V) : ℝ :=
  ⨆ k : ℕ, ((strongPow G (k + 1)).indepNum : ℝ) ^ (1 / ((k : ℝ) + 1))
end ShannonCapacity


