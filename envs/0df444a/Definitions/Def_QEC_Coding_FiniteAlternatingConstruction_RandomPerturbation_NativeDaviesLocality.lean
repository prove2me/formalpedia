-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T11:43:05.332708+00:00
-- url     : https://prove2.me/theorems/ea9fc708-1768-4d58-ae82-fbfb5d691654
-- title:
--   Native Davies Locality
-- statement:
--   Definitions and structural lemmas for Native Davies Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def localFrequency (S : OddScale) (n : ℕ) (q : Physical S n)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    Operator (subsystem S n q).selectedSystem :=
  (subsystem S n q).restrictLocalFromRegister
    (actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω)
def localJump (S : OddScale) (n : ℕ)
    (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    Operator (subsystem S n q).selectedSystem :=
  (subsystem S n q).restrictLocalFromRegister
    (hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
      (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω))
def DaviesGeometry (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (t : ℝ) : Prop :=
  BDL26NativeHamiltonianLocality.HamiltonianGeometry S n J t ∧
  ∀ q : Physical S n,
    (region S n q).card ≤ 50 ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (∀ (a : CSSDaviesLocality.Axis) (ω : ℝ),
      (subsystem S n q).OperatorSupportedOnRegister
        (actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω) ∧
      actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω =
        actualFrequency (incidentHamiltonian S n q) (incidentHamiltonian_symmetric S n q)
          (coupling S n q a) ω ∧
      (subsystem S n q).extendLocalToRegister (localFrequency S n q a ω) =
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω) ∧
    (∀ (rate : CouplingIndex S n → Frequency S n → ℝ)
      (a : CSSDaviesLocality.Axis) (ω : Frequency S n),
      (subsystem S n q).OperatorSupportedOnRegister
        (hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
      hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) =
        (Real.sqrt (rate (q,a) ω) : ℂ) •
          actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
            (coupling S n q a) ω.val ∧
      (subsystem S n q).extendLocalToRegister (localJump S n rate q a ω) =
        hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ a : CSSDaviesLocality.Axis,
      (∑ ω : Frequency S n,
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω.val) = coupling S n q a ∧
      ∃ ω : Frequency S n,
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω.val ≠ 0)
def finiteDaviesSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Set (BDL26NativeFiniteComposition.Experiment p N) :=
  {z | z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
    ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t}
end QEC.Coding.BDL26NativeDaviesLocality


