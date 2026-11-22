-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:34:26.716701+00:00
-- url     : https://prove2.me/theorems/33860687-46de-48cd-bd36-d316634d39fd
-- title:
--   Layer Counterexample
-- statement:
--   Definitions and structural lemmas for Layer Counterexample, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
noncomputable def pf2Rotations (θ : ℝ) : List (PauliString 8 × ℝ) :=
  (L₁ ++ L₂ ++ L₂ ++ L₁).map fun G => (G, θ)
noncomputable def pf2Output (θ : ℝ) : Matrix (Bits 8) (Bits 8) ℂ :=
  layerConj (pf2Rotations θ) (toMatrix (Z 3))
def backwardReaches {n : ℕ} :
    List (PauliString n) → PauliIndex n → PauliIndex n → Bool
  | [], p, q => decide (p = q)
  | G :: L, p, q =>
      if sympForm G (herm p) = 0 then backwardReaches L p q
      else backwardReaches L p q || backwardReaches L (partner G p) q
def bitIndex (x z : ℕ) : PauliIndex 8 :=
  (fun i => if x.testBit i.val then 1 else 0, fun i => if z.testBit i.val then 1 else 0)
def generator : Fin 7 → PauliString 8 :=
  ![X 0 * Z 1, X 2 * X 3, Z 4 * X 5, X 6 * X 7,
    X 1 * Z 2, X 3 * X 4, X 5 * X 6]
attribute [local irreducible] layerAct
noncomputable abbrev coefficientSeed : EuclideanSpace ℂ (PauliIndex 8) :=
  WithLp.toLp 2 (Pi.single (bitIndex 0 8) (1 : ℂ))
noncomputable def pf2Discard (θ : ℝ) : Matrix (Bits 8) (Bits 8) ℂ :=
  pf2Output θ - truncOp (highSet 8 1)ᶜ (pf2Output θ)
end Lean4LPD.LayerCounterexample


