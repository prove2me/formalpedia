-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T11:38:04.623845+00:00
-- url     : https://prove2.me/theorems/aaf84abc-cbde-4110-b2d2-a0485c046893
-- title:
--   Native Hamiltonian Locality
-- statement:
--   Definitions and structural lemmas for Native Hamiltonian Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def ballSubsystem (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ) :
    FiniteSubsystem (Physical S n) :=
  ⟨qubitHits (state S n).presentation J (Metric.closedBall c r)⟩
def signedCheck (S : OddScale) (n : ℕ) (j : Sum (ZLabel S n) (XLabel S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) :=
  -toQubitOperator (check S n j)
def localCheck (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (j : Sum (ZLabel S n) (XLabel S n)) :
    Operator (ballSubsystem S n J (checkCenter S n J j) 1).selectedSystem :=
  (ballSubsystem S n J (checkCenter S n J j) 1).restrictLocalFromRegister (signedCheck S n j)
def HamiltonianGeometry (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (t : ℝ) : Prop :=
  PhysicalGeometry S n J t ∧
  hamiltonian S n = (∑ j : Sum (ZLabel S n) (XLabel S n), signedCheck S n j) ∧
  ∀ j : Sum (ZLabel S n) (XLabel S n),
    (ballSubsystem S n J (checkCenter S n J j) 1).extendLocalToRegister (localCheck S n J j) =
      signedCheck S n j ∧
    ((((ballSubsystem S n J (checkCenter S n J j) 1).selected.card : ℕ) : ℝ) ≤ 2*t) ∧
    (∀ q ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      dist (J (.q q)) (checkCenter S n J j) ≤ 1) ∧
    (∀ q ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      ∀ u ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      dist (J (.q q)) (J (.q u)) ≤ 2) ∧
    (checkSupport S n j).card ≤ 7
def finiteHamiltonianSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Set (BDL26NativeFiniteComposition.Experiment p N) :=
  {z | z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
    ∀ i : Fin (N+1), HamiltonianGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t}
end QEC.Coding.BDL26NativeHamiltonianLocality


