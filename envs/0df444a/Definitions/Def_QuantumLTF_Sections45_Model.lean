-- Prove2me | Definitions.Def_QuantumLTF_Sections45_Model
-- name    : QuantumLTF_Sections45_Model
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T20:34:45.340072+00:00
-- url     : https://prove2.me/theorems/aa772c8b-4aa8-4bc5-97fb-975aca714f07
-- title:
--   Shared learner contracts for Sections 4 and 5
-- statement:
--   Reusable predicates recording exact learning of hidden Majority supports, parallel circuit depth, finite-grid homogeneous-LTF learner contracts, and generic oracle-query lower bounds. These interfaces give the numbered results of Sections 4 and 5 a shared operational circuit semantics.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Sections 4–5, pp. 39–78.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Example_qex

namespace QuantumLTF

open QAlgorithms Membership

namespace Majority

/-- Gates in one parallel layer act on pairwise-disjoint wire sets. -/
def LayerDisjoint {S : Set Gate} {m : ℕ} (L : List (GateApp S m)) : Prop :=
  L.Pairwise fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)

/-- A sequential circuit admits a partition into at most `d` disjoint-wire parallel layers. -/
def HasDepth {S : Set Gate} {m : ℕ} (c : Circuit S m) (d : ℕ) : Prop :=
  ∃ layers : List (List (GateApp S m)), layers.flatten = c ∧ layers.length ≤ d ∧
    ∀ L ∈ layers, LayerDisjoint L

/-- A circuit exactly learns every hidden nonempty support of size at most `k`. -/
def LearnsUpTo {n k m : ℕ}
    (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
    (out : Fin n ↪ Fin m) (success : ℝ) : Prop :=
  ∀ A : Finset (Fin n), A.Nonempty → A.card ≤ k →
    probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
      (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ success

/-- A circuit exactly learns every hidden support of cardinality `k`. -/
def LearnsExact {n k m : ℕ}
    (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
    (out : Fin n ↪ Fin m) (success : ℝ) : Prop :=
  ∀ A : Finset (Fin n), A.card = k →
    probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
      (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ success

/-- Quantitative gate/query/depth accounting used by the time-efficient Majority results.
`depth` is supplied together with a certified parallel schedule in a later circuit library; here the
contract records the claimed numerical resource bounds. -/
structure ResourceCertificate {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) where
  depth : ℕ
  depth_le_gateCount : depth ≤ c.gateCount

end Majority

namespace Example

/-- A finite-dimensional quantum learner contract for homogeneous LTFs. -/
structure LearnerContract (n q m : ℕ) where
  circuit : OracleCircuit Membership.gates12 (fun _ : Fin 1 => n * q + 1) m
  output : Qubits m → EuclideanSpace ℝ (Fin n)

/-- Worst-case correctness of a finite-grid quantum-example learner. -/
def LearnsHomogeneous {n q m : ℕ} (L : LearnerContract n q m)
    (ε success : ℝ) : Prop :=
  ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
    ∀ U, IsQEX w U →
      probEvent (act (L.circuit.unitary fun _ => U) (zeroKet m))
        (fun z => ‖L.output z - w‖ ≤ ε) ≥ success

/-- Abstract query lower-bound interface: every learner satisfying `Good` uses at least the
specified number of calls. -/
def RequiresQueries {S : Set Gate} {a : Fin 1 → ℕ}
    (Good : ∀ m, OracleCircuit S a m → Prop) (Q : ℝ) : Prop :=
  ∀ m (c : OracleCircuit S a m), Good m c → Q ≤ c.queryCount 0

end Example

end QuantumLTF


