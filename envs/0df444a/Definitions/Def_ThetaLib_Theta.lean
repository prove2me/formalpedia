-- Prove2me | Definitions.Def_ThetaLib_Theta
-- name    : ThetaLib_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:29:04.601951+00:00
-- url     : https://prove2.me/theorems/ad80dc69-9938-4432-8ee8-316f2623faaf
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from Juan Pablo Traverso Gianini (jtraverso/lovasz-theta; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lovasz theta bound and Shannon capacity of the 5-cycle development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace LovaszTheta
variable {V : Type*}
def strongPow (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm SimpleGraph.Adj.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
def IsOrthonormalRep (G : SimpleGraph V) {d : ℕ} (u : V → Fin d → ℝ) : Prop :=
  (∀ i, dotProduct (u i) (u i) = 1) ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → dotProduct (u i) (u j) = 0
noncomputable def pentAngle (i : Fin 5) : ℝ := 2 * Real.pi * ((i : ℕ) : ℝ) / 5
noncomputable def umbH : ℝ := Real.sqrt (1 / Real.sqrt 5)
noncomputable def umbS : ℝ := Real.sqrt (1 - 1 / Real.sqrt 5)
noncomputable def umbrella (i : Fin 5) : Fin 3 → ℝ :=
  ![umbS * Real.cos (pentAngle i), umbS * Real.sin (pentAngle i), umbH]
noncomputable def shannonCapacity [Fintype V] (G : SimpleGraph V) : ℝ :=
  ⨆ k : ℕ, ((strongPow G (k + 1)).indepNum : ℝ) ^ (1 / ((k : ℝ) + 1))
end LovaszTheta


