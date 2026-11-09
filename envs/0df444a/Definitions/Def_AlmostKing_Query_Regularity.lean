-- Prove2me | Definitions.Def_AlmostKing_Query_Regularity
-- name    : AlmostKing_Query_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:08.400038+00:00
-- url     : https://prove2.me/theorems/bec7797e-ab0d-4a2d-960f-ab91de8190ae
-- title:
--   Sparse regularity, template graphs, group graphs, and active courts
-- statement:
--   For a relation $E$ and finite vertex sets $X,Y$, the crossing edge set is the subset of $X\times Y$ satisfying $E$. Its cardinality is $d_E^+(X,Y)$, and its density is $\rho_E(X,Y)=d_E^+(X,Y)/(|X||Y|)$. For a simple graph and disjoint classes, this counts each undirected crossing edge once. Density on an empty class is assigned zero and is only used on nonempty classes in regularity assertions.
--
--   An ordered disjoint nonempty pair is $(\alpha,p)$-regular when every $X'\subseteq X$, $Y'\subseteq Y$ of sizes strictly greater than $\alpha|X|$, $\alpha|Y|$ has density within $\alpha p$ of the original density. It is $(\xi,q)$-lower-regular when all such subsets with sizes at least $\xi|X|$, $\xi|Y|$ satisfy
--   $$d_E^+(X',Y')\ge(1-\xi)q|X'||Y'|.$$
--   A graph is $(\mu,p)$-upper-uniform when disjoint classes of sizes at least $\mu n$ have at most $(1+\mu)p|X||Y|$ edges. These predicates leave their real parameters unrestricted; theorem hypotheses specify their ranges, and Theorem 12 also uses regularity when $\alpha\ge1$.
--
--   A $\kappa$-template graph has at most $n^{4/3}$ edges and, for every disjoint $X,Y$ with $|X|,|Y|\ge\kappa n$,
--   $$(1-\kappa)n^{-2/3}|X||Y|\le |E_G(X,Y)|\le(1+\kappa)n^{-2/3}|X||Y|.$$
--   An orientation contains exactly one direction of every underlying edge and no other arcs. A partition consists of a possibly empty exceptional class and pairwise disjoint classes covering the vertex type. The group graph contains $i\to j$ exactly when both directions of the class pair are regular and the forward arc count is greater, with ties resolved by $i<j$. Missing unordered pairs are counted once using $i<j$; irregular ordered pairs are counted using $i\ne j$.
--
--   The court union is $Q=\bigcup_i A_i$. A tournament on $Q$ imposes the tournament conditions only on vertices in $Q$. The active groups of $w$ are
--   $$I_S(w)=\{i:|N_S^+(w)\cap A_i|\ge\lceil\eta L\rceil\}.$$
--   These are predicates and computed objects, with no assumed existence theorem embedded in them.
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, §2, pp. 5–6; Definitions 4, 6, 8, pp. 6–7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Goal

namespace AlmostKing.Query

/-- Section 2, pp. 5–6: relation edges directed from X to Y, each counted once.
For a simple graph and disjoint sets this also counts its undirected crossing edges once. -/
noncomputable def crossing {V : Type*} (E : V → V → Prop) (X Y : Finset V) : Finset (V × V) :=
  by classical exact (X ×ˢ Y).filter (fun e => E e.1 e.2)

/-- Section 2: d⁺ for a digraph, and |E_G(X,Y)| for a simple graph. -/
noncomputable def edgeCount {V : Type*} (E : V → V → Prop) (X Y : Finset V) : ℕ :=
  (crossing E X Y).card

/-- Density. Only used on nonempty classes in regularity assertions; empty denominator gives 0. -/
noncomputable def density {V : Type*} (E : V → V → Prop) (X Y : Finset V) : ℝ :=
  (edgeCount E X Y : ℝ) / ((X.card : ℝ) * Y.card)

/-- Section 2, pp. 5–6: strict subset-size thresholds. Parameters are left unrestricted
so Theorem 12 can also use τ ≥ 1; its subset condition is then vacuous. -/
def IsRegular {V : Type*} (D : Digraph V) (α p : ℝ) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ X.Nonempty ∧ Y.Nonempty ∧
  ∀ X' ⊆ X, ∀ Y' ⊆ Y,
    α * X.card < (X'.card : ℝ) → α * Y.card < (Y'.card : ℝ) →
    |density D.Adj X' Y' - density D.Adj X Y| ≤ α * p

/-- Section 2, p. 6: non-strict subset-size thresholds. -/
def IsLowerRegular {V : Type*} (E : V → V → Prop) (ξ q : ℝ) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ X.Nonempty ∧ Y.Nonempty ∧
  ∀ X' ⊆ X, ∀ Y' ⊆ Y,
    ξ * X.card ≤ (X'.card : ℝ) → ξ * Y.card ≤ (Y'.card : ℝ) →
    (1 - ξ) * q * X'.card * Y'.card ≤ (edgeCount E X' Y' : ℝ)

/-- Section 2, p. 6: upper-uniformity of a finite simple graph. -/
def IsUpperUniform {V : Type*} [Fintype V] (G : SimpleGraph V) (μ p : ℝ) : Prop :=
  ∀ X Y : Finset V, Disjoint X Y →
    μ * Fintype.card V ≤ (X.card : ℝ) → μ * Fintype.card V ≤ (Y.card : ℝ) →
    (edgeCount G.Adj X Y : ℝ) ≤ (1 + μ) * p * X.card * Y.card

/-- All and only the edges of G receive one direction. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  IsOriented D ∧ (∀ u v, D.Adj u v → G.Adj u v) ∧
    ∀ u v, G.Adj u v → D.Adj u v ∨ D.Adj v u

/-- Undirected total edge count, using the order on Fin n to count each pair once. -/
noncomputable def totalEdges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card

/-- Definition 4, p. 6: both discrepancy inequalities and the n^(4/3) edge budget. -/
def IsTemplate {n : ℕ} (κ : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  (totalEdges G : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) ∧
  ∀ X Y : Finset (Fin n), Disjoint X Y →
    κ * n ≤ (X.card : ℝ) → κ * n ≤ (Y.card : ℝ) →
    (1 - κ) * (n : ℝ) ^ (-(2 : ℝ) / 3) * X.card * Y.card ≤ (edgeCount G.Adj X Y : ℝ) ∧
    (edgeCount G.Adj X Y : ℝ) ≤ (1 + κ) * (n : ℝ) ^ (-(2 : ℝ) / 3) * X.card * Y.card

/-- A partition with an exceptional class V₀, possibly empty. -/
def IsPartition {V : Type*} [Fintype V] {r : ℕ}
    (V₀ : Finset V) (groups : Fin r → Finset V) : Prop :=
  (∀ i, Disjoint V₀ (groups i)) ∧
  (∀ i j, i ≠ j → Disjoint (groups i) (groups j)) ∧
  ∀ v, v ∈ V₀ ∨ ∃ i, v ∈ groups i

/-- Definition 6, pp. 6–7: bidirectional regularity, majority, then index tie-break.
Disjoint nonempty groups are required by IsRegular; the diagonal cannot be an arc. -/
def groupGraph {V : Type*} {r : ℕ} (D : Digraph V)
    (groups : Fin r → Finset V) (α p : ℝ) : Digraph (Fin r) where
  Adj i j := i ≠ j ∧ IsRegular D α p (groups i) (groups j) ∧
    IsRegular D α p (groups j) (groups i) ∧
    (edgeCount D.Adj (groups j) (groups i) < edgeCount D.Adj (groups i) (groups j) ∨
      (edgeCount D.Adj (groups i) (groups j) = edgeCount D.Adj (groups j) (groups i) ∧ i < j))

/-- Unordered missing pairs are represented by their unique ordering i < j. -/
noncomputable def missingPairs {r : ℕ} (R : Digraph (Fin r)) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin r × Fin r)).filter
    (fun e => e.1 < e.2 ∧ ¬ R.Adj e.1 e.2 ∧ ¬ R.Adj e.2 e.1)).card

/-- Ordered irregular pairs, as counted in Theorem 12 (not the unordered count above). -/
noncomputable def irregularPairs {V : Type*} {r : ℕ} (D : Digraph V)
    (groups : Fin r → Finset V) (α p : ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin r × Fin r)).filter
    (fun e => e.1 ≠ e.2 ∧ ¬ IsRegular D α p (groups e.1) (groups e.2))).card

noncomputable def courtUnion {V : Type*} {r : ℕ} (A : Fin r → Finset V) : Finset V :=
  by classical exact Finset.univ.biUnion A

/-- Tournament on Q: arcs outside Q are ignored. -/
def IsTournamentOn {V : Type*} (S : Digraph V) (Q : Finset V) : Prop :=
  (∀ v ∈ Q, ¬ S.Adj v v) ∧
  ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v →
    (S.Adj u v ∨ S.Adj v u) ∧ ¬ (S.Adj u v ∧ S.Adj v u)

/-- Definition 8, p. 7: active groups use the natural ceiling of ηL. -/
noncomputable def activeGroups {V : Type*} [Fintype V] {r : ℕ}
    (S : Digraph V) (A : Fin r → Finset V) (η : ℝ) (L : ℕ) (w : V) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i => ⌈η * L⌉₊ ≤ ((outNbhd S w) ∩ A i).card)

end AlmostKing.Query


