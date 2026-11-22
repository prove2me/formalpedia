-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:28:24.099687+00:00
-- url     : https://prove2.me/theorems/30e1716f-29a3-4034-8cbf-a60be39d2a0d
-- title:
--   Layer Flow
-- statement:
--   Definitions and structural lemmas for Layer Flow, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
noncomputable def stayAct (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then y.ofLp p else (Real.cos θ : ℂ) * y.ofLp p
noncomputable def jumpAct (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then 0
    else -(Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p))
noncomputable def layerAct : List (PauliString n × ℝ) →
    EuclideanSpace ℂ (PauliIndex n) → EuclideanSpace ℂ (PauliIndex n)
  | [], y => y
  | (G, θ) :: L, y => rotAct G θ (layerAct L y)
noncomputable def layerConj : List (PauliString n × ℝ) →
    Matrix (Bits n) (Bits n) ℂ → Matrix (Bits n) (Bits n) ℂ
  | [], O => O
  | (G, θ) :: L, O => rot (toMatrix G) θ * layerConj L O * rot (toMatrix G) (-θ)
noncomputable def layerJump : List (PauliString n × ℝ) → ℕ →
    EuclideanSpace ℂ (PauliIndex n) → EuclideanSpace ℂ (PauliIndex n)
  | [], 0, y => y
  | [], _ + 1, _ => 0
  | (G, θ) :: L, 0, y => stayAct G θ (layerJump L 0 y)
  | (G, θ) :: L, j + 1, y =>
      stayAct G θ (layerJump L (j + 1) y) + jumpAct G θ (layerJump L j y)
def antiLayer (L : List (PauliString n)) (p : PauliIndex n) : Finset (PauliString n) :=
  L.toFinset.filter fun G => sympForm G (herm p) = 1
noncomputable def layerSigma : List (PauliString n × ℝ) → ℝ
  | [] => 0
  | g :: L => max |Real.sin g.2| (layerSigma L)
noncomputable def layerJumpMatrix (L : List (PauliString n × ℝ)) (j : ℕ) :
    Matrix (PauliIndex n) (PauliIndex n) ℂ := fun p q =>
  (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p
def layerAntiCount (L : List (PauliString n)) (p : PauliIndex n) : ℕ :=
  L.countP fun G => sympForm G (herm p) = 1
noncomputable def layerInflowMatrix (L : List (PauliString n × ℝ)) (w j : ℕ) :
    Matrix (PauliIndex n) (PauliIndex n) ℂ := fun p q =>
  if w < wt p ∧ wt q ≤ w then layerJumpMatrix L j p q else 0
end Lean4LPD.PauliString


