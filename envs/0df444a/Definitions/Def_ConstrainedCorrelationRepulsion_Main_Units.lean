-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Units
-- name    : ConstrainedCorrelationRepulsion_Main_Units
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:07.941535+00:00
-- url     : https://prove2.me/theorems/f55b0635-8868-4dbc-8dd5-b3a6507f428e
-- title:
--   Atoms, units, dangerous outsiders and two-witness certificates
-- statement:
--   A unit system is a partition of the vertices into nonempty sets, with its non-singleton sets called selected atoms and its singleton vertices free. This data structure carries no assertion about optimal partitions. A set is an atom only when every optimal feasible partition keeps it whole. Distinct units are compatible when no cannot-link joins them.
--
--   For $Q\subseteq V$, define $e_Q(v)=e^-(v,Q)+e^+(v,V\setminus Q)$ and $\delta_Q=\max_{v\in Q}e_Q(v)$, with empty maximum zero. Dangerous outsiders have at least $|Q|/3$ positive neighbors in $Q$ and a cannot-link neighbor there. A two-witness certificate assigns each such outsider two distinct cannot-link neighbors, with no witness reused. Residual unit conditions require negative hard pairs, no internal hard pair, complete hard cross-products, and incompatible distinct atoms. The common constant is $C_{\rm pre}=60006$, the value proved on printed p.20.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §§2.3, 4.1–4.2, printed pp.6–8, 17–20 (PDF pp.7–9, 18–21)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Instance

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

/-- Selected disjoint atoms and singleton free vertices; only the partition data is bundled.
No optimality, LP, or sampling guarantee is part of this structure. -/
structure Units (n : ℕ) where
  blocks : Finset (Finset (Fin n))
  nonempty : ∀ B ∈ blocks, B.Nonempty
  cover : ∀ v : Fin n, ∃! B, B ∈ blocks ∧ v ∈ B

noncomputable def unitOf {n : ℕ} (U : Units n) (v : Fin n) : Finset (Fin n) :=
  Classical.choose (ExistsUnique.exists (U.cover v))

noncomputable def freeVertices {n : ℕ} (U : Units n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (unitOf U v).card = 1)

noncomputable def atoms {n : ℕ} (U : Units n) : Finset (Finset (Fin n)) :=
  U.blocks.filter (fun B => 2 ≤ B.card)

def Preserves {n : ℕ} (U : Units n) (P : Partition n) : Prop :=
  ∀ B ∈ U.blocks, ∀ u ∈ B, ∀ v ∈ B, P u = P v

def UnitUnion {n : ℕ} (U : Units n) (D : Finset (Fin n)) : Prop :=
  ∀ B ∈ U.blocks, B ⊆ D ∨ Disjoint B D

def Compatible {n : ℕ} (I : Instance n) (B D : Finset (Fin n)) : Prop :=
  ∀ u ∈ B, ∀ v ∈ D, ¬ I.cannotLink.Adj u v

def HardProduct {n : ℕ} (I : Instance n) (B D : Finset (Fin n)) : Prop :=
  ∀ u ∈ B, ∀ v ∈ D, I.cannotLink.Adj u v

noncomputable def positiveDegree {n : ℕ} (I : Instance n) (v : Fin n)
    (S : Finset (Fin n)) : ℕ := (S.filter (I.positive.Adj v)).card

noncomputable def incidentErrors {n : ℕ} (I : Instance n) (Q : Finset (Fin n))
    (v : Fin n) : ℕ :=
  ((Q.erase v).filter (fun u => ¬ I.positive.Adj v u)).card +
    positiveDegree I v (Finset.univ \ Q)

/-- Finite maximum; its empty-set value is 0. Atom hypotheses always require |Q| ≥ 2. -/
noncomputable def deltaQ {n : ℕ} (I : Instance n) (Q : Finset (Fin n)) : ℕ :=
  Q.sup (incidentErrors I Q)

noncomputable def dangerous {n : ℕ} (I : Instance n) (Q : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ Q).filter (fun w =>
    (Q.card : ℝ) / 3 ≤ positiveDegree I w Q ∧ ∃ v ∈ Q, I.cannotLink.Adj w v)

def TwoWitnesses {n : ℕ} (I : Instance n) (W Q : Finset (Fin n)) : Prop :=
  ∃ f : W → Fin 2 → Q, Function.Injective (fun p : W × Fin 2 => f p.1 p.2) ∧
    ∀ (w : W) (k : Fin 2), I.cannotLink.Adj (w : Fin n) (f w k : Fin n)

def AtomHypotheses {n : ℕ} (I : Instance n) (Q : Finset (Fin n)) : Prop :=
  2 ≤ Q.card ∧ Compatible I Q Q ∧ (deltaQ I Q : ℝ) < (Q.card : ℝ) / 20 ∧
    TwoWitnesses I (dangerous I Q) Q

def IsAtom {n : ℕ} (I : Instance n) (Q : Finset (Fin n)) : Prop :=
  2 ≤ Q.card ∧ ∀ P, Optimal I P → ∀ u ∈ Q, ∀ v ∈ Q, P u = P v

/-- Standing residual unit conditions in §§5–6, independent of any LP solution or sampler.
These are outputs of preclustering, not extra hypotheses of the main theorem. -/
def ResidualUnits {n : ℕ} (I : Instance n) (U : Units n) : Prop :=
  I.mustLink = ⊥ ∧
  (∀ u v, I.cannotLink.Adj u v → ¬ I.positive.Adj u v) ∧
  (∀ B ∈ U.blocks, Compatible I B B) ∧
  (∀ B ∈ U.blocks, ∀ D ∈ U.blocks, B ≠ D → Compatible I B D ∨ HardProduct I B D) ∧
  (∀ B ∈ atoms U, ∀ D ∈ atoms U, B ≠ D → HardProduct I B D)

def Cpre : ℕ := 60006

noncomputable def freeDegree {n : ℕ} (I : Instance n) (U : Units n) : ℕ :=
  ∑ v ∈ freeVertices U, positiveDegree I v Finset.univ

end ConstrainedCorrelationRepulsion.Main


