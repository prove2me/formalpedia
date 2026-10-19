-- Prove2me | Definitions.Def_HyperKCut_Structure_Model
-- name    : HyperKCut_Structure_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:22.847524+00:00
-- url     : https://prove2.me/theorems/183e221d-9885-474d-8d59-eb1f3049404b
-- title:
--   §1.1 and §3 — cut values, partitions, terminal cuts, and σ
-- statement:
--   For a finite unit-cost hypergraph $G=(V,E)$, the **cut value** $d(A)$ counts edge copies meeting both $A$ and $V\setminus A$. An ordered partition $P=(P_1,\ldots,P_n)$ has nonempty, pairwise disjoint parts covering $V$; its cost counts each edge copy meeting at least two parts. A minimum $k$-partition has smallest cost, and it is maximal minimum when no minimum partition has a strictly larger first part.
--
--   For disjoint terminal sets $S,T$, an $(S,T)$-terminal cut is a set $U$ with $S\subseteq U\subseteq V\setminus T$. The source-maximal minimum terminal cut minimizes $d(U)$ and contains every other minimum terminal source set.
--
--   For a partition $(Y_1,\ldots,Y_p,W,Z)$, the paper uses four counts: its crossing cost; $\operatorname{cost}(W,Z)$, the copies contained in $W\cup Z$ meeting both; $\alpha$, the copies meeting $Z$ and at least two of $Y_1,\ldots,Y_p,W$; and $\beta$, the copies disjoint from $Z$ meeting at least two of $Y_1,\ldots,Y_p$. Their sum is
--
--   $$\sigma(Y_1,\ldots,Y_p,W,Z)=\operatorname{cost}(Y_1,\ldots,Y_p,W,Z)+\operatorname{cost}(W,Z)+\alpha+\beta.$$
--
--   These definitions are the common vocabulary of the structural theorem and its uncrossing milestones.
--
--   **Formalization Note** Each edge copy contributes once to each applicable count. The paper's phrase “more than two parts” conflicts with its explicit “there exist distinct $i,j$” clause; crossing means at least two parts. Complements are taken in $V$.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, pp. 1, 3–4, 7–8 (PDF 2, 4–5, 8–9), §1, §1.1, §3

import Mathlib
import Definitions.Def_HyperKCut_Structure_Hypergraph

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A hyperedge meets a vertex set. -/
def Meets (e A : Finset V) : Prop := (e ∩ A).Nonempty

instance (e A : Finset V) : Decidable (Meets e A) :=
  inferInstanceAs (Decidable (e ∩ A).Nonempty)

/-- The number of edge copies meeting both a set and its complement. -/
def d (H : Hypergraph V) (A : Finset V) : ℕ :=
  (H.edges.filter fun e => Meets e A ∧ Meets e Aᶜ).card

/-- An ordered partition into nonempty, disjoint parts covering all vertices. -/
def IsPartition {n : ℕ} (P : Fin n → Finset V) : Prop :=
  (∀ i, (P i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ v, ∃ i, v ∈ P i)

/-- Number of edge copies meeting at least two parts. -/
def cost {n : ℕ} (H : Hypergraph V) (P : Fin n → Finset V) : ℕ :=
  (H.edges.filter fun e =>
    ∃ i j, i ≠ j ∧ Meets e (P i) ∧ Meets e (P j)).card

/-- A partition whose crossing cost is least among all k-partitions. -/
def IsMinKPartition (H : Hypergraph V) (k : ℕ) (P : Fin k → Finset V) : Prop :=
  IsPartition P ∧ ∀ Q : Fin k → Finset V, IsPartition Q → cost H P ≤ cost H Q

/-- No other minimum partition has a strictly larger first part. -/
def IsMaximalMinKPartition (H : Hypergraph V) (k : ℕ) [NeZero k]
    (P : Fin k → Finset V) : Prop :=
  IsMinKPartition H k P ∧
  ¬ ∃ Q : Fin k → Finset V, IsMinKPartition H k Q ∧ P 0 ⊂ Q 0

/-- A terminal cut has S on its source side and T on its sink side. -/
def IsTerminalCut (S T U : Finset V) : Prop := S ⊆ U ∧ Disjoint U T

/-- A least-value terminal cut. -/
def IsMinTerminalCut (H : Hypergraph V) (S T U : Finset V) : Prop :=
  IsTerminalCut S T U ∧
  ∀ U' : Finset V, IsTerminalCut S T U' → d H U ≤ d H U'

/-- The unique minimum terminal cut that contains every minimum terminal cut. -/
def IsSourceMaxMinTerminalCut (H : Hypergraph V) (S T U : Finset V) : Prop :=
  IsMinTerminalCut H S T U ∧
  ∀ U' : Finset V, IsMinTerminalCut H S T U' → U' ⊆ U

/-- Number of Y-parts met by an edge. -/
def numYMet {p : ℕ} (e : Finset V) (Y : Fin p → Finset V) : ℕ :=
  (Finset.univ.filter fun i => Meets e (Y i)).card

/-- Cost of the partition (Y₁,...,Yₚ,W,Z). -/
def costYWZ {p : ℕ} (H : Hypergraph V) (Y : Fin p → Finset V)
    (W Z : Finset V) : ℕ :=
  cost H (Fin.snoc (Fin.snoc Y W) Z)

/-- Edge copies contained in W ∪ Z and meeting both W and Z. -/
def costWZ (H : Hypergraph V) (W Z : Finset V) : ℕ :=
  (H.edges.filter fun e => e ⊆ W ∪ Z ∧ Meets e W ∧ Meets e Z).card

/-- Edge copies meeting Z and at least two of the Y-parts and W. -/
def alpha {p : ℕ} (H : Hypergraph V) (Y : Fin p → Finset V)
    (W Z : Finset V) : ℕ :=
  (H.edges.filter fun e =>
    Meets e Z ∧
    (2 ≤ numYMet e Y ∨ (1 ≤ numYMet e Y ∧ Meets e W))).card

/-- Edge copies disjoint from Z and meeting at least two Y-parts. -/
def beta {p : ℕ} (H : Hypergraph V) (Y : Fin p → Finset V)
    (Z : Finset V) : ℕ :=
  (H.edges.filter fun e =>
    ¬ Meets e Z ∧ 2 ≤ numYMet e Y).card

/-- The paper's sigma count for a (p+2)-partition. -/
def sigma {p : ℕ} (H : Hypergraph V) (Y : Fin p → Finset V)
    (W Z : Finset V) : ℕ :=
  costYWZ H Y W Z + costWZ H W Z + alpha H Y W Z + beta H Y Z

/-- The tuple (Y₁,...,Yₚ,W,Z) is a partition. -/
def IsPartitionYWZ {p : ℕ} (Y : Fin p → Finset V)
    (W Z : Finset V) : Prop :=
  IsPartition (Fin.snoc (Fin.snoc Y W) Z)

end HyperKCut.Structure


