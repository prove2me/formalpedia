-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Coeff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:52.999297+00:00
-- url     : https://prove2.me/theorems/ddabe601-58bc-41d7-8618-e1889c447ca1
-- title:
--   Coeff
-- statement:
--   Definitions and structural lemmas for Coeff, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
abbrev PauliIndex (n : ℕ) := Bits n × Bits n
namespace PauliString
variable {n : ℕ}
def cls (s : PauliString n) : PauliIndex n := (s.x, s.z)
def herm (p : PauliIndex n) : PauliString n := ⟨p.1, p.2, ((p.2 ⬝ᵥ p.1).val : ZMod 4)⟩
def wt (p : PauliIndex n) : ℕ := weight (herm p)
noncomputable def coeff (O : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm p) * O).trace
noncomputable def pauliNormSq (O : Matrix (Bits n) (Bits n) ℂ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ a : Bits n, ∑ b : Bits n, ‖O a b‖ ^ 2
noncomputable def pauliNorm (O : Matrix (Bits n) (Bits n) ℂ) : ℝ := Real.sqrt (pauliNormSq O)
noncomputable def coeffVec (O : Matrix (Bits n) (Bits n) ℂ) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 (coeff O)
noncomputable def restr (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p => if p ∈ S then y.ofLp p else 0
def highSet (n w : ℕ) : Finset (PauliIndex n) := univ.filter fun p => w < wt p
noncomputable def highNorm (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℝ :=
  ‖restr (highSet n w) (coeffVec O)‖
end PauliString
end Lean4LPD


