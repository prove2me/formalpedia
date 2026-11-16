-- Prove2me | Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph
-- name    : SubadditiveProphet1456_Quarter_Supplement_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:42:40.423755+00:00
-- url     : https://prove2.me/theorems/11a99000-d94b-4662-800d-3027b6481c63
-- title:
--   Complete k-uniform hypergraph on k² vertices, the covering valuation (33), and the undersampling coupling
-- statement:
--   Fix an integer $k$. The **vertex set** is $U=\{0,\ldots,k^2-1\}$, so $|U|=k^2$, and the **complete $k$-uniform hypergraph** $H=(U,M)$ has as its edges all $k$-element subsets of $U$:
--   $$
--   M=\binom{U}{k},\qquad m=|M|=\binom{k^2}{k}.
--   $$
--   For a vertex $r$, $\delta_H(r)=\{e\in M:r\in e\}$ is the set of edges incident to $r$. For a vertex set $J\subseteq U$, $E(H-J)=\{e\in M:e\cap J=\varnothing\}$ is the set of edges avoiding $J$. For a finite family $\mathcal J$ of $k$-vertex sets, $\bigcup_{J\in\mathcal J}E(H-J)$ is the set of edges covered by the corresponding **bulk pieces**.
--
--   Put $\beta=(e-1)^2/e^3$. A bulk piece $E(H-J)$, $J\in\binom Uk$, costs $\beta m$, and a singleton piece $\{e\}$, $e\in M$, costs $1$. A cover of an edge set $T$ is a pair $(\mathcal J,S)$ of bulk indices and singleton edges with $T\subseteq\bigcup_{J\in\mathcal J}E(H-J)\cup S$; its cost is $|\mathcal J|\beta m+|S|$. The **covering valuation** of display (33) is
--   $$
--   g(S)=\min_{\mathcal J\subseteq\binom Uk}\Big(|\mathcal J|\,\beta m+\Big|S\setminus\bigcup_{J\in\mathcal J}E(H-J)\Big|\Big),\qquad S\subseteq M,
--   $$
--   the minimum cost of a cover of $S$; the empty family gives the value $|S|$.
--
--   For the undersampling device of Proposition 5.4, put $p=(1-k^{-1/4})/k$. The random set $X\subseteq U$ that contains each vertex independently with probability $p$ has law $\Pr[X=A]=p^{|A|}(1-p)^{k^2-|A|}$. A **coupling** of $X$ with a uniformly random edge $e\in\binom Uk$ is a nonnegative joint mass function $\mu(A,e)$ whose first marginal is this law and whose second marginal is the uniform mass $1/m$. For a family $\mathcal F$ of subsets of $U$, $\Pr[X\in\mathcal F]$ and $\Pr[e\in\mathcal F]$ are the corresponding sums of masses, and $\Pr_\mu[X\not\subseteq e]$ is the $\mu$-mass of the pairs with $A\not\subseteq e$.
--
--   These objects are the hard instance of Section 5 of the paper: the items of the impossibility instance are the edges of $H$, and $g$ is the valuation of its final buyer.
--
--   **Formalization Note** Edges and $k$-vertex sets are the subtype of $k$-element finite subsets of $\mathrm{Fin}(k^2)$; $m$ is the cardinality of that type. The minimum in (33) is taken over finite sets of $k$-vertex sets rather than tuples $J_1,\ldots,J_q$; repeating a bulk piece only adds cost, so the two minima coincide. Masses and probabilities are real numbers. The definitions are stated for every natural $k$; the results using them assume $k\ge2$.
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, §5 hypergraph notation printed p.18, PDF p.19; β printed p.21, PDF p.22; covering pieces and (33) printed pp.21–22, PDF pp.22–23; undersampling law printed p.24, PDF p.25.

import Mathlib

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- Kroll–MacRury–Reiffenhäuser–Sundaram, STOC 2027 #1456, §5, printed p. 18 (PDF 19):
the vertex set `U` of the complete `k`-uniform hypergraph, with `|U| = k²`. -/
abbrev Vertex (k : ℕ) := Fin (k ^ 2)

/-- A `k`-element vertex set, i.e. an element of `(U choose k)`. The edges of the complete
`k`-uniform hypergraph `H = (U, M)` are exactly these sets, and the bulk covering pieces are
indexed by them as well. -/
abbrev KSubset (k : ℕ) := {e : Finset (Vertex k) // e.card = k}

/-- `m = |M|`, the number of edges, which equals `choose (k²) k`. -/
noncomputable def edgeCount (k : ℕ) : ℕ := Fintype.card (KSubset k)

/-- `δ_H(r) = {e ∈ M : r ∈ e}`, the edges incident to the vertex `r`. -/
noncomputable def incident (k : ℕ) (r : Vertex k) : Finset (KSubset k) := by
  classical
  exact Finset.univ.filter fun e => r ∈ e.1

/-- `E(H − J) = {e ∈ M : e ∩ J = ∅}`, the edges avoiding the vertex set `J`. -/
noncomputable def avoidEdges (k : ℕ) (J : Finset (Vertex k)) : Finset (KSubset k) := by
  classical
  exact Finset.univ.filter fun e => Disjoint e.1 J

/-- The edges covered by the bulk pieces `E(H − J)`, `J ∈ 𝒥`. -/
noncomputable def bulkUnion (k : ℕ) (𝒥 : Finset (KSubset k)) : Finset (KSubset k) := by
  classical
  exact 𝒥.biUnion fun J => avoidEdges k J.1

/-- `β = (e − 1)² / e³`, printed p. 21 (PDF 22). -/
noncomputable def coverBeta : ℝ := (Real.exp 1 - 1) ^ 2 / Real.exp 1 ^ 3

/-- The cost of a cover consisting of the bulk pieces indexed by `𝒥` (cost `βm` each) and the
singleton pieces `{e}`, `e ∈ S` (cost `1` each). -/
noncomputable def coverCost (k : ℕ) (𝒥 S : Finset (KSubset k)) : ℝ :=
  (𝒥.card : ℝ) * coverBeta * (edgeCount k : ℝ) + (S.card : ℝ)

/-- `(𝒥, S)` covers the edge set `T`: every edge of `T` lies in a selected bulk piece or is a
selected singleton. -/
def IsCover (k : ℕ) (T 𝒥 S : Finset (KSubset k)) : Prop :=
  T ⊆ bulkUnion k 𝒥 ∪ S

/-- The covering valuation `g` of (33), printed p. 22 (PDF 23):
`g(S) = min_{𝒥} ( |𝒥| β m + |S \ ⋃_{J ∈ 𝒥} E(H − J)| )`, the minimum over all finite sets
`𝒥` of `k`-vertex sets (the empty choice gives cost `|S|`). -/
noncomputable def coverValue (k : ℕ) (S : Finset (KSubset k)) : ℝ := by
  classical
  exact (Finset.univ : Finset (Finset (KSubset k))).inf' Finset.univ_nonempty fun 𝒥 =>
    (𝒥.card : ℝ) * coverBeta * (edgeCount k : ℝ) + ((S \ bulkUnion k 𝒥).card : ℝ)

/-- The undersampling probability `p = (1 − k^{−1/4}) / k`, printed p. 24 (PDF 25). -/
noncomputable def sampleProb (k : ℕ) : ℝ := (1 - (k : ℝ) ^ (-(1 / 4 : ℝ))) / k

/-- The law of the random set `X ⊆ U` containing each vertex independently with probability
`p`: `Pr[X = A] = p^{|A|} (1 − p)^{k² − |A|}`. -/
noncomputable def sampleMass (k : ℕ) (A : Finset (Vertex k)) : ℝ :=
  sampleProb k ^ A.card * (1 - sampleProb k) ^ (k ^ 2 - A.card)

/-- A coupling of the independent `p`-sample `X ⊆ U` with a uniformly random edge
`e ∈ (U choose k)`: a nonnegative joint mass function whose first marginal is `sampleMass k`
and whose second marginal is the uniform mass `1 / m`. -/
def IsSampleCoupling (k : ℕ) (μ : Finset (Vertex k) × KSubset k → ℝ) : Prop :=
  (∀ z, 0 ≤ μ z) ∧
  (∀ A, ∑ e, μ (A, e) = sampleMass k A) ∧
  (∀ e, ∑ A, μ (A, e) = 1 / (edgeCount k : ℝ))

/-- `Pr[X ∈ F]` under the independent `p`-sample. -/
noncomputable def sampleEventProb (k : ℕ) (F : Set (Finset (Vertex k))) : ℝ := by
  classical
  exact ∑ A ∈ Finset.univ.filter (fun A => A ∈ F), sampleMass k A

/-- `Pr[e ∈ F]` for a uniformly random edge `e ∈ (U choose k)`. -/
noncomputable def uniformEventProb (k : ℕ) (F : Set (Finset (Vertex k))) : ℝ := by
  classical
  exact ((Finset.univ.filter fun e : KSubset k => e.1 ∈ F).card : ℝ) / (edgeCount k : ℝ)

/-- The mass a joint mass function puts on the event `{X ⊈ e}`. -/
noncomputable def notSubsetMass (k : ℕ) (μ : Finset (Vertex k) × KSubset k → ℝ) : ℝ := by
  classical
  exact ∑ z ∈ Finset.univ.filter (fun z : Finset (Vertex k) × KSubset k => ¬ z.1 ⊆ z.2.1), μ z

end SubadditiveProphet1456.Quarter.Supplement


