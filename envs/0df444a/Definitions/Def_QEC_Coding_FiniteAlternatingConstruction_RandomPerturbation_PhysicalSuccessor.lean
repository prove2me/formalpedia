-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:13:52.821892+00:00
-- url     : https://prove2.me/theorems/ffa36891-f000-431d-b6ca-2993d6aaed35
-- title:
--   Physical Successor
-- statement:
--   Definitions and structural lemmas for Physical Successor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}
def replacementOutput (S : OddScale) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) : Vertex (nextState S n C).presentation → Space :=
  @_root_.dite (Vertex (nextState S n C).presentation → Space) (n % 2 = 0)
    (Nat.decEq (n % 2) 0)
    (fun h v => rxVertexPoint C.presentation S J (nextRXVertex S n C h v))
    (fun h v => rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible S J
      (nextRZVertex S n C h v))
def physicalTableLaw (p : GeometricParameters L) (n : Nat) :
    Measure (Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) := by
  let P := (state (perturbationOddScale p) n).presentation
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  exact tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
def physicalSuccessorOutput (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) :
    Vertex (state (perturbationOddScale p) (n+1)).presentation → Space :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (perturbationEmbeddingOutput _ J p T)
def PhysicalSuccessorFacts (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) : Prop :=
  let S := perturbationOddScale p
  Halts (eventSupport (state S n).presentation J (anchorRadius p.m))
    (eventBad (state S n).presentation J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
  IsBoundedDensityLocalMap (state S (n+1)).presentation (physicalSuccessorOutput p n J T) p.t ∧
  PhysicalGeometry S (n+1) (physicalSuccessorOutput p n J T) p.t ∧
  (∀ (q : Physical S (n+1)) (a : CSSDaviesLocality.Axis) (ω : ℝ),
    (BDL26CSSDaviesLocality.subsystem S (n+1) q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S (n+1)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+1))
        (BDL26CSSDaviesLocality.coupling S (n+1) q a) ω)) ∧
  (∀ (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+1) →
      BDL26CSSDaviesLocality.Frequency S (n+1) → ℝ)
      (q : Physical S (n+1)) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S (n+1)),
    (BDL26CSSDaviesLocality.subsystem S (n+1) q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S (n+1)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+1))
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S (n+1) =>
          BDL26CSSDaviesLocality.coupling S (n+1) qa.1 qa.2) rate ((q,a),ω)))
end QEC.Coding.BDL26RandomPerturbation


