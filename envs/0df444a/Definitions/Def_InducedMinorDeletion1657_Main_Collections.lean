-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Collections
-- name    : InducedMinorDeletion1657_Main_Collections
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:43.973248+00:00
-- url     : https://prove2.me/theorems/63dba26f-486b-408c-9d9d-3aa1affc04a1
-- title:
--   Full packing and branching output specifications
-- statement:
--   The packing output consists of disjoint connected vertex sets $V_i$ outside a prescribed modulator, with $Z_i\subseteq V_i$, more than $d$ neighbors in the modulator, bounded $|Z_i|$, and the required core after deleting all $Z_i$. Anticompleteness is not required.
--
--   The degeneracy output retains each witness $B_i$, its $t$-degeneracy, the degree bound outside $A_i\cup B_i$, and $\Delta$-degeneracy of $G-A_i$. Every $t$-degenerate deletion set must contain an output $A_i$.
--
--   Core branching requires the modulator, size, core and degeneracy guarantees on the same pair $(X_i,M_i)$. Sublinear branching requires both the width bound and containment coverage:
--   $$\forall S,\ \operatorname{tw}(G-S)\le t\land |S|\le k\ \Longrightarrow\ \exists i,\ X_i\subseteq S.$$
--   These are output predicates only; the theorem items assert that finite executable programs produce them within the stated resources.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), Corollary 3.6 and Lemmas 4.2–4.3; Theorem 4.1, pp. 13, 16–17 (PDF pp. 14, 17–18)

import Definitions.Def_InducedMinorDeletion1657_Main_Execution

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

noncomputable def removedWitnesses {n : ℕ}
    (P : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  P.foldl (fun S p => S ∪ p.2) ∅

/-- The four clauses of Corollary 3.6; the collection is not required anticomplete. -/
def packingResult (G : InputGraph) (M : Finset (Fin G.n)) (d t C : ℕ)
    (P : List (Finset (Fin G.n) × Finset (Fin G.n))) : Prop :=
  P.Pairwise (fun p q => Disjoint p.1 q.1) ∧
  (∀ p ∈ P, p.1 ⊆ Finset.univ \ M ∧ p.2 ⊆ p.1 ∧
    (G.graph.induce (↑p.1 : Set (Fin G.n))).Connected ∧
    ((neighbors G.graph (↑p.1)) ∩ M).card > d ∧ p.2.card ≤ C * t) ∧
  coreAfter G.graph (removedWitnesses P) M d

noncomputable def degreeAfter {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (v : Fin n) : ℕ :=
  ((Finset.univ \ A).filter (G.Adj v)).card

/-- Full Lemma 4.3, including its B witness and containment for every deletion set. -/
def degeneracyResult (G : InputGraph) (Δ t : ℕ) (L : List (Finset (Fin G.n))) : Prop :=
  (∀ A ∈ L, (∃ B : Finset (Fin G.n), Disjoint A B ∧
      ForestBackdoorFPT.IsDegenerate (G.graph.induce (↑B : Set (Fin G.n))) t ∧
      ∀ v : Fin G.n, v ∉ A ∪ B → degreeAfter G.graph A v ≤ Δ) ∧
    ForestBackdoorFPT.IsDegenerate (residual G.graph A) Δ) ∧
  ∀ S : Finset (Fin G.n), ForestBackdoorFPT.IsDegenerate (residual G.graph S) t →
    ∃ A ∈ L, A ⊆ S

/-- All four clauses of Lemma 4.2, on the same pairs and with a saturated logarithm. -/
def coreBranchResult (G : InputGraph) (k d t C : ℕ)
    (Q : List (Finset (Fin G.n) × Finset (Fin G.n))) : Prop :=
  (∀ p ∈ Q, modulator G.graph t (p.1 ∪ p.2) ∧
    (p.2.card : ℝ) ≤ C * (t : ℝ)^2 * satLog t * k ∧
    coreAfter G.graph p.1 p.2 (C * (d + t)) ∧
    ForestBackdoorFPT.IsDegenerate (G.graph.induce (↑p.2 : Set (Fin G.n))) d) ∧
  ∀ S : Finset (Fin G.n), modulator G.graph t S → S.card ≤ k →
    ∃ p ∈ Q, p.1 ⊆ S

/-- Theorem 4.1's width and all-modulator containment clauses. -/
def sublinearResult (G : InputGraph) (k d t C a : ℕ)
    (L : List (Finset (Fin G.n))) : Prop :=
  (∀ X ∈ L, (width (residual G.graph X) : ℝ) ≤
    C * (t : ℝ)^a * Real.sqrt ((k : ℝ) * d)) ∧
  ∀ S : Finset (Fin G.n), modulator G.graph t S → S.card ≤ k →
    ∃ X ∈ L, X ⊆ S

end InducedMinorDeletion1657.Main


