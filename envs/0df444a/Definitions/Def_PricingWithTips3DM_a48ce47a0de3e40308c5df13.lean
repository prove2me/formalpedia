-- Prove2me | Definitions.Def_PricingWithTips3DM_a48ce47a0de3e40308c5df13
-- name    : PricingWithTips3DM_a48ce47a0de3e40308c5df13
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:03:01.233818+00:00
-- url     : https://prove2.me/theorems/ee4374f8-0a8b-44f6-a826-51e955fa968e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.EncodingBounds
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9174b91e232fd04a6eaa5646
import Definitions.Def_PricingWithTips3DM_3e5e8df74ad0aba26b3400f6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial bounds for verifier-circuit serialization

The tableau input arity and the complete unary circuit encoding are bounded by
explicit polynomials depending only on the fixed verifier witness.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Fixed-verifier polynomial controlling the number of tableau input bits. -/
def verifierCircuitInputBound {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  (verifierHorizon W + 1) *
    (Polynomial.C (cfgBitCoefficient W.machine.tm) *
      (verifierHeight W + 1))

@[simp] theorem verifierCircuitInputBound_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierCircuitInputBound W).eval n =
      ((verifierHorizon W).eval n + 1) *
        (cfgBitCoefficient W.machine.tm *
          ((verifierHeight W).eval n + 1)) := by
  simp [verifierCircuitInputBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_natCast]

/-- The generated verifier circuit has polynomially many declared inputs. -/
theorem verifierCircuit_input_count_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierCircuit W x).inputCount ≤
      (verifierCircuitInputBound W).eval x.length := by
  rw [verifierCircuit_inputCount, verifierCircuitInputBound_eval]
  unfold tableauInputCount tableauRowCount
  exact Nat.mul_le_mul_left _
    (cfgBitCount_le W.machine.tm ((verifierHeight W).eval x.length))

/-- Fixed-verifier polynomial controlling the complete unary circuit encoding. -/
def verifierCircuitEncodingBound {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  12 * (verifierCircuitGateBound W + 1) *
    (verifierCircuitGateBound W + verifierCircuitInputBound W + 1)

@[simp] theorem verifierCircuitEncodingBound_eval {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierCircuitEncodingBound W).eval n =
      12 * ((verifierCircuitGateBound W).eval n + 1) *
        ((verifierCircuitGateBound W).eval n +
          (verifierCircuitInputBound W).eval n + 1) := by
  simp [verifierCircuitEncodingBound, Polynomial.eval_add,
    Polynomial.eval_mul]

/-- The canonical encoding of the verifier circuit has polynomial length. -/
theorem verifierCircuit_encoding_length_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (encodeCircuit (verifierCircuit W x)).length ≤
      (verifierCircuitEncodingBound W).eval x.length := by
  rw [verifierCircuitEncodingBound_eval]
  calc
    (encodeCircuit (verifierCircuit W x)).length ≤
        12 * ((verifierCircuit W x).gates.length + 1) *
          ((verifierCircuit W x).gates.length +
            (verifierCircuit W x).inputCount + 1) :=
      encodeCircuit_length_le (verifierCircuit W x)
        (verifierCircuit_wellFormed W x)
    _ ≤ 12 * ((verifierCircuitGateBound W).eval x.length + 1) *
        ((verifierCircuitGateBound W).eval x.length +
          (verifierCircuitInputBound W).eval x.length + 1) := by
      gcongr
      · exact verifierCircuit_gate_count_le W x
      · exact verifierCircuit_gate_count_le W x
      · exact verifierCircuit_input_count_le W x

end

end CLRS.Chapter34.Turing.CookLevin


