-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Supplement_Widths
-- name    : SparseIncidenceHom_WidthComparison_Supplement_Widths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:46.781948+00:00
-- url     : https://prove2.me/theorems/342df24f-9384-4366-8349-db057164f3ca
-- title:
--   Submodular width, clique embedding power, fractional $(X,Y)$-separators, $(\mu,\lambda)$-connectivity and the hub inequality
-- statement:
--   Let $H$ be a finite hypergraph (no empty edges, every vertex in an edge) with primal graph $P(H)$.
--
--   1. A function $b:2^{V(H)}\to\mathbb R_{\ge0}$ is an **edge-dominated polymatroid** if $b(\varnothing)=0$, $b(X)\le b(Y)$ for $X\subseteq Y$, $b(X\cup Y)+b(X\cap Y)\le b(X)+b(Y)$, and $b(e)\le1$ for every hyperedge $e$. The **submodular width** is
--   $$\operatorname{subw}(H)=\sup_{b}\ \min_{(T,B)}\ \max_{t\in V(T)} b(B(t)),$$
--   the supremum over edge-dominated polymatroids taken outside the minimum over tree decompositions.
--
--   2. Two nonempty sets $U,W\subseteq V(H)$ **touch** if they intersect or some hyperedge meets both. A **clique embedding** $\psi:K_m\to H$ assigns to each $i\in[m]$ a nonempty set $\psi(i)$ that is connected in $P(H)$, with $\psi(i)$ and $\psi(j)$ touching whenever $i\ne j$ (images may coincide). Its **weak edge depth** and the **clique embedding power** are
--   $$d(\psi)=\max_{e\in E(H)}|\{i\in[m]:\psi(i)\cap e\ne\varnothing\}|,\qquad \operatorname{emb}(H)=\sup_{m\ge3,\ \psi:K_m\to H}\frac{m}{d(\psi)}.$$
--   On the empty hypergraph no embedding exists and $\operatorname{emb}=0$.
--
--   3. For a nonnegative vertex weighting $\mu$ write $\mu(X)=\sum_{v\in X}\mu(v)$. A **fractional $(X,Y)$-separator** is a nonnegative hyperedge weighting $s$ such that every path $P$ of $P(H)$ from a vertex of $X$ to a vertex of $Y$ satisfies $\sum_{e:\,e\cap V(P)\ne\varnothing}s(e)\ge1$. A set $W$ is **$(\mu,\lambda)$-connected** if for all disjoint $X,Y\subseteq W$ every fractional $(X,Y)$-separator has $\sum_e s(e)\ge\lambda\min\{\mu(X),\mu(Y)\}$.
--
--   4. A **pseudometric** on $[k]$ is $d:[k]\times[k]\to\mathbb R_{\ge0}$ with $d(i,i)=0$, $d(i,j)=d(j,i)$ and $d(i,j)\le d(i,l)+d(l,j)$; distinct points may be at distance $0$. For nonempty $A,B$, $d(A,B)=\min_{i\in A,j\in B}d(i,j)$. A constant $C$ satisfies the **hub inequality** (10) if for every $k\ge2$ and every pseudometric $d$ on $[k]$ some $z\in[k]$ has
--   $$\sum_{u\in[k]}d(z,u)\le C\log k\max_{\substack{\varnothing\ne A,B\subseteq[k]\\ A\cap B=\varnothing}}\min\{|A|,|B|\}\,d(A,B).$$
--
--   These are the objects of Section 6, which connect unbounded submodular width to W[1]-hardness through clique embeddings.
--
--   **Formalization Note** Logarithms are to base two (the published `logTwo`). Tree decompositions and the minimum over them are the published `optimalWidth`. Paths are Mathlib walks with `IsPath`; a hyperedge counts once if it meets the path's vertex set. $[k]$ is `Fin k`.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 8 (Section 2.2: polymatroids, subw), p. 20 (touching sets, clique embeddings, equation (8)), p. 24 (vertex weightings, fractional (X,Y)-separators, (µ,λ)-connectivity, pseudometrics, d(A,B), inequality (10))

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Decompositions

namespace SparseIncidenceHom.WidthComparison.Supplement

open SparseIncidenceHom.WidthComparison

/-- p. 8. An edge-dominated polymatroid: `b : 2^V → ℝ≥0`, `b(∅) = 0`, monotone, submodular, and
`b(e) ≤ 1` for every hyperedge `e`. -/
def IsEdgeDominatedPolymatroid {V : Type} (H : FiniteHypergraph V) (b : Set V → ℝ) : Prop :=
  (∀ X, 0 ≤ b X) ∧ b ∅ = 0 ∧ (∀ X Y, X ⊆ Y → b X ≤ b Y) ∧
  (∀ X Y, b (X ∪ Y) + b (X ∩ Y) ≤ b X + b Y) ∧ ∀ e : Edge H, b e.val ≤ 1

/-- p. 8. Submodular width: supremum over edge-dominated polymatroids OUTSIDE the minimum over
tree decompositions, exactly as the published `adaptiveWidth` with modular weights. -/
noncomputable def submodularWidth {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℝ :=
  sSup {c | ∃ b : Set V → ℝ, IsEdgeDominatedPolymatroid H b ∧ c = optimalWidth H b}

/-- p. 20. A nonempty vertex set that is connected in the primal graph `P(H)`. -/
def IsConnectedSet {V : Type} (H : FiniteHypergraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, ∃ p : (primal H).Walk u v, ∀ w ∈ p.support, w ∈ S

/-- p. 20. Two sets touch if they intersect or some hyperedge meets both. -/
def Touch {V : Type} (H : FiniteHypergraph V) (U W : Set V) : Prop :=
  (U ∩ W).Nonempty ∨ ∃ e ∈ H.graph.edgeSet, (e ∩ U).Nonempty ∧ (e ∩ W).Nonempty

/-- p. 20. A clique embedding `ψ : K_m → H`: nonempty connected images, pairwise touching for
distinct clique vertices; images may coincide. -/
structure CliqueEmbedding {V : Type} (H : FiniteHypergraph V) (m : ℕ) where
  img : Fin m → Set V
  connected : ∀ i, IsConnectedSet H (img i)
  touch : ∀ i j, i ≠ j → Touch H (img i) (img j)

/-- Equation (8): the weak edge depth `d(ψ) = max_e |{i : ψ(i) ∩ e ≠ ∅}|`. -/
noncomputable def weakEdgeDepth {V : Type} [Fintype V] {H : FiniteHypergraph V} {m : ℕ}
    (ψ : CliqueEmbedding H m) : ℕ := by
  classical
  exact Finset.univ.sup (fun e : Edge H =>
    (Finset.univ.filter (fun i : Fin m => (ψ.img i ∩ e.val).Nonempty)).card)

/-- Equation (8): the clique embedding power `emb(H) = sup_{m ≥ 3, ψ : K_m → H} m / d(ψ)`.
On the empty hypergraph no embedding exists and the value is `sSup ∅ = 0`. -/
noncomputable def cliqueEmbeddingPower {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℝ :=
  sSup {c | ∃ (m : ℕ) (ψ : CliqueEmbedding H m), 3 ≤ m ∧ c = (m : ℝ) / (weakEdgeDepth ψ : ℝ)}

/-- p. 24. `μ(X) = ∑_{v ∈ X} μ(v)`. -/
noncomputable def weightOf {V : Type} (μ : V → ℝ) (X : Finset V) : ℝ := ∑ v ∈ X, μ v

/-- p. 24. A fractional `(X, Y)`-separator: a nonnegative hyperedge weighting `s` such that every
path of `P(H)` from a vertex of `X` to a vertex of `Y` meets hyperedges of total weight at least 1
(a hyperedge counts once if it meets the path's vertex set). -/
noncomputable def IsFractionalXYSeparator {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (X Y : Set V) (s : Edge H → ℝ) : Prop := by
  classical
  exact (∀ e, 0 ≤ s e) ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ p : (primal H).Walk x y, p.IsPath →
    1 ≤ ∑ e : Edge H, if (∃ w ∈ p.support, w ∈ e.val) then s e else 0

/-- p. 24. `W` is `(μ, λ)`-connected: for all disjoint `X, Y ⊆ W`, every fractional
`(X, Y)`-separator has total weight at least `λ · min{μ(X), μ(Y)}`. -/
def IsMuLambdaConnected {V : Type} [Fintype V] (H : FiniteHypergraph V) (μ : V → ℝ)
    (lam : ℝ) (W : Set V) : Prop :=
  ∀ X Y : Finset V, (X : Set V) ⊆ W → (Y : Set V) ⊆ W → Disjoint X Y →
    ∀ s : Edge H → ℝ, IsFractionalXYSeparator H X Y s →
      lam * min (weightOf μ X) (weightOf μ Y) ≤ ∑ e, s e

/-- p. 24. A pseudometric on `[k]` (identified with `Fin k`); distinct points may be at distance 0. -/
def IsPseudometric {k : ℕ} (d : Fin k → Fin k → ℝ) : Prop :=
  (∀ i j, 0 ≤ d i j) ∧ (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧
  ∀ i j l, d i j ≤ d i l + d l j

/-- p. 24. `d(A, B) = min_{i ∈ A, j ∈ B} d(i, j)` (used only for nonempty `A`, `B`). -/
noncomputable def setDist {k : ℕ} (d : Fin k → Fin k → ℝ) (A B : Finset (Fin k)) : ℝ :=
  sInf {c | ∃ i ∈ A, ∃ j ∈ B, c = d i j}

/-- The right-hand maximum of (10): `max_{∅ ≠ A, B ⊆ [k], A ∩ B = ∅} min{|A|, |B|} d(A, B)`
(a maximum over a finite set). -/
noncomputable def hubSeparation {k : ℕ} (d : Fin k → Fin k → ℝ) : ℝ :=
  sSup {c | ∃ A B : Finset (Fin k), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    c = ((min A.card B.card : ℕ) : ℝ) * setDist d A B}

/-- Inequality (10) of Lemma 6.4 with constant `C`: for every pseudometric `d` on `[k]` with
`k ≥ 2`, some `z` has `∑_u d(z, u) ≤ C · log₂ k · max … min{|A|,|B|} d(A, B)`. -/
def HubBound (C : ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ d : Fin k → Fin k → ℝ, IsPseudometric d →
    ∃ z : Fin k, ∑ u, d z u ≤ C * logTwo (k : ℝ) * hubSeparation d

end SparseIncidenceHom.WidthComparison.Supplement


