-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering
-- name    : ConstrainedCorrelationRepulsion_Main_Preclustering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:45.327075+00:00
-- url     : https://prove2.me/theorems/1a37cd0a-d154-49d6-a717-191c6736b0d5
-- title:
--   Figure 4 construction trace and its separate guarantees
-- statement:
--   A 2-expansion certificate specifies $Q,Z$ and witness edges, including $N(Q)=Z$, $|L\setminus Q|\le2|R\setminus Z|$, exactly two witnesses at every right vertex, at most one use of a left witness, and inclusion of isolated left vertices.
--
--   The preclustering trace starts with an optimal metric and its deterministic radius-$2/3$ Repulsion partition. A singleton or a cluster with $q_S\ge |S|^2/10000$ becomes free. Other clusters are trimmed at $|S|/100$, use outside threshold $|S|/4$, and retain the 2-expansion set. Units are those retained sets and the remaining singletons. Cannot-links are added between atoms and propagated between units, then positive hard pairs are relabelled while retaining every vertex. The trace contains no optimality-preservation or degree-budget guarantee; these are separate conclusions of Theorem 2.4. The separate guarantees retain the free-degree bound both before and after the final relabelling.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Figure 4, Lemma 2.3, §§4.1–4.2; printed pp.8, 17–21 (PDF pp.9, 18–22)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Repulsion
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

/-- The complete, empty-set-permitting 2-expansion certificate. The two vertex carriers can
be the same type; left and right are distinguished by their positions in an ordered pair. -/
def ExpansionCertificate {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : A → B → Prop) (left : Finset A) (right : Finset B)
    (Q : Finset A) (Z : Finset B) (matching : Finset (A × B)) : Prop :=
  Q ⊆ left ∧ Z ⊆ right ∧
  (∀ z ∈ right, z ∈ Z ↔ ∃ q ∈ Q, E q z) ∧
  (left \ Q).card ≤ 2 * (right \ Z).card ∧
  (∀ e ∈ matching, e.1 ∈ Q ∧ e.2 ∈ Z ∧ E e.1 e.2) ∧
  (∀ z ∈ Z, (matching.filter (fun e => e.2 = z)).card = 2) ∧
  (∀ q ∈ Q, (matching.filter (fun e => e.1 = q)).card ≤ 1) ∧
  (∀ q ∈ left, (∀ z ∈ right, ¬ E q z) → q ∈ Q)

noncomputable def classSet {n : ℕ} (P : Partition n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => P u = P v)

noncomputable def classes {n : ℕ} (P : Partition n) : Finset (Finset (Fin n)) :=
  Finset.univ.image (classSet P)

noncomputable def totalIncident {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : ℕ :=
  ∑ v ∈ S, incidentErrors I S v

noncomputable def trimmed {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun v => (incidentErrors I S v : ℝ) ≤ (S.card : ℝ) / 100)

noncomputable def outsideCandidates {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ S).filter (fun w => (S.card : ℝ) / 4 ≤ positiveDegree I w S)

def TrimmingChoice {n : ℕ} (I : Instance n) (S Q : Finset (Fin n)) : Prop :=
  if S.card = 1 ∨ (S.card : ℝ)^2 / 10000 ≤ totalIncident I S then Q = ∅ else
    ∃ Z matching, ExpansionCertificate I.cannotLink.Adj (trimmed I S) (outsideCandidates I S) Q Z matching

noncomputable def retainedAtoms {n : ℕ} (P : Partition n)
    (chosen : Finset (Fin n) → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((classes P).image chosen).filter (fun B => B.Nonempty)

noncomputable def chosenUnits {n : ℕ} (P : Partition n)
    (chosen : Finset (Fin n) → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  let A := retainedAtoms P chosen
  A ∪ ((Finset.univ \ A.biUnion id).image (fun v => {v}))

noncomputable def augmentedHard {n : ℕ} (I : Instance n) (U : Units n)
    (u v : Fin n) : Prop :=
  unitOf U u ≠ unitOf U v ∧
    ((2 ≤ (unitOf U u).card ∧ 2 ≤ (unitOf U v).card) ∨
     ∃ a ∈ unitOf U u, ∃ b ∈ unitOf U v, I.cannotLink.Adj a b)

/-- Figure 4 as a construction relation. It names the initial optimal metric, the actual
deterministic radius-2/3 Repulsion partition, and the 2-expansion choices. It contains no atom,
optimal-partition-preservation, degree-budget or cost-identity conclusion. -/
def PreclusterTrace {n : ℕ} (I J : Instance n) (U : Units n) : Prop :=
  ∃ x : Fin n → Fin n → ℝ, MetricOptimal I (signedCosts I) x ∧
    let P := partitionOfBlocks (repulsionBlocks I x (2/3) (potentialTwoThirds I x) n Finset.univ)
    ∃ chosen : Finset (Fin n) → Finset (Fin n),
      (∀ S ∈ classes P, TrimmingChoice I S (chosen S)) ∧
      U.blocks = chosenUnits P chosen ∧ J.mustLink = ⊥ ∧
      (∀ u v, J.cannotLink.Adj u v ↔ augmentedHard I U u v) ∧
      (∀ u v, J.positive.Adj u v ↔ I.positive.Adj u v ∧ ¬ J.cannotLink.Adj u v)

/-- Conclusions of Theorem 2.4, separated from its construction trace. -/
def PreclusterGuarantees {n : ℕ} (I J : Instance n) (U : Units n) : Prop :=
  ResidualUnits J U ∧
  (∀ B ∈ atoms U, IsAtom J B) ∧
  (∀ P, Optimal J P → ∀ B ∈ atoms U, ∀ D ∈ atoms U, B ≠ D →
    ∀ u ∈ B, ∀ v ∈ D, P u ≠ P v) ∧
  OPT J ≤ OPT I ∧ freeDegree I U ≤ Cpre * OPT I ∧
  freeDegree J U ≤ Cpre * OPT I ∧
  (∀ P, Optimal I P → Feasible J P ∧ Preserves U P) ∧
  (∀ P, Feasible J P → Preserves U P → Feasible I P ∧
    (cost I P : ℤ) - (cost J P : ℤ) = (OPT I : ℤ) - (OPT J : ℤ))

noncomputable def EncodesPrecluster {n : ℕ} (s : MachineState) (J : Instance n)
    (U : Units n) : Prop :=
  (∀ u v, s.natMem u.val = s.natMem v.val ↔ unitOf U u = unitOf U v) ∧
  (∀ u v, (s.natMem (n + u.val * n + v.val) = 1 ↔ J.positive.Adj u v)) ∧
  (∀ u v, (s.natMem (n + n*n + u.val * n + v.val) = 1 ↔ J.cannotLink.Adj u v)) ∧
  J.mustLink = ⊥

end ConstrainedCorrelationRepulsion.Main


