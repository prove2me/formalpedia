-- Prove2me | Definitions.Def_BicliqueSDP_Chain_Model
-- name    : BicliqueSDP_Chain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:51.346055+00:00
-- url     : https://prove2.me/theorems/b373d9ea-7805-4d7c-96d5-65740b364d15
-- title:
--   pp. 1–2, 5–6, 12–13 — biindependent pairs, α, g (1), h (2), α_bal, g_bal, h_bal, C (26), g₁ (8), h₁ (9), the dual (32), las₁ (23), ϑ (24)
-- statement:
--   This module fixes the objects of Laurent, Polak and Vargas, *Semidefinite approximations for bicliques and biindependent pairs*.
--
--   A **bipartite graph** $G=(V_1\cup V_2,E)$ is given by two finite vertex sets $V_1$, $V_2$ and a relation $E\subseteq V_1\times V_2$; its vertex set is $V=V_1\sqcup V_2$, and $i\in V_1$, $j\in V_2$ are adjacent exactly when $(i,j)\in E$. No two vertices on the same side are adjacent.
--
--   1. **Biindependent pairs (p. 1).** A pair $(A,B)$ with $A\subseteq V_1$, $B\subseteq V_2$ is a *bipartite biindependent pair* if no $\{i,j\}\in A\times B$ is an edge. It is *balanced* if $|A|=|B|$ (p. 2). The pair $(\emptyset,\emptyset)$ is always biindependent and balanced.
--   2. **Combinatorial parameters (pp. 1–2).** Over all biindependent pairs,
--   $$\alpha(G)=\max(|A|+|B|),\qquad g(G)=\max |A|\cdot|B|\ \ (1),\qquad h(G)=\max\frac{|A|\cdot|B|}{|A|+|B|}\ \ (2),$$
--   and $\alpha_{\mathrm{bal}}(G)$, $g_{\mathrm{bal}}(G)$, $h_{\mathrm{bal}}(G)$ are the same maxima over balanced pairs. The trivial pair $(\emptyset,\emptyset)$ contributes the value $0$ to $h$ and $h_{\mathrm{bal}}$.
--   3. **The matrix $C$, Eq. (26).** $C=\tfrac12\begin{pmatrix}0&J\\ J&0\end{pmatrix}$ indexed by $V$, where $J$ is the all-ones matrix: $C_{ij}=\tfrac12$ when one of $i,j$ lies in $V_1$ and the other in $V_2$, and $C_{ij}=0$ otherwise. For a matrix $X$ indexed by $V$, $\langle C,X\rangle=\sum_{i,j}C_{ij}X_{ij}$.
--   4. **The SDP bounds (8) and (9), p. 5.**
--   $$g_1(G)=\max\Bigl\{\langle C,X\rangle:\begin{pmatrix}1&\mathrm{diag}(X)^{\mathsf T}\\ \mathrm{diag}(X)&X\end{pmatrix}\succeq0,\ X_{ij}=0 \text{ if } \{i,j\}\in E\Bigr\},$$
--   $$h_1(G)=\max\{\langle C,X\rangle: X\succeq0,\ \mathrm{Tr}(X)=1,\ X_{ij}=0 \text{ if } \{i,j\}\in E\}.$$
--   5. **The dual program (32), p. 13.** With $S_G$ the set of symmetric matrices $Z$ indexed by $V$ with $Z_{ij}=0$ whenever $\{i,j\}\notin E$ (in particular $Z_{ii}=0$, p. 6),
--   $$\min\{\lambda\in\mathbb R:\ \lambda I+Z-C\succeq0,\ Z\in S_G\}.$$
--   6. **$\mathrm{las}_1$ and the theta number, (23)–(24), p. 12.** For an arbitrary finite graph $G=(V,E)$,
--   $$\mathrm{las}_1(G)=\max\Bigl\{\mathrm{Tr}(X):\begin{pmatrix}1&\mathrm{diag}(X)^{\mathsf T}\\ \mathrm{diag}(X)&X\end{pmatrix}\succeq0,\ X_{ij}=0 \text{ for } \{i,j\}\in E\Bigr\},$$
--   $$\vartheta(G)=\max\{\langle J,X\rangle: X\succeq0,\ \mathrm{Tr}(X)=1,\ X_{ij}=0 \text{ for } \{i,j\}\in E\}.$$
--
--   These objects carry Proposition 1.2 and its proof in §3.3: Lemma 1.1, Eq. (25), the identity $\vartheta(G)=\alpha(G)$ for bipartite $G$, Lemma 3.3 and relations (40)–(41).
--
--   **Formalization Note** The vertex type is `V1 ⊕ V2` and the graph is `bipGraph E`, a `SimpleGraph` with edges only between the two sides. The combinatorial maxima are `Finset.sup'` over the finite, nonempty set of biindependent pairs, as real numbers; $0/0=0$ at $(\emptyset,\emptyset)$ matches the paper's convention that trivial pairs have value $0$ (p. 2). The SDP maxima are `sSup` and the minimum (32) is `sInf` of sets of reals. Their feasible sets are bounded (trace one, resp. the bordered constraint, bound every entry), so no junk value arises except for the empty vertex set, where every parameter is $0$. $X\succeq0$ is `Matrix.PosSemidef`, which includes symmetry, so the paper's $X\in\mathcal S^{|V|}$ is implied. The bordered matrix is indexed by `Unit ⊕ V`, the `Unit` index playing the role of $0$. $g_1$ and $h_1$ are defined by their SDP forms (8) and (9) as stated on p. 5, not by the Lasserre hierarchy (29)–(30); Lemma 3.5 (which identifies the two for $g_1$) is then the definition and is not stated.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, pp. 1–2, Eqs. (1), (2) and the definitions of α, α_bal, g_bal, h_bal; p. 5, Eqs. (8), (9); p. 6, S_G; p. 12, Eqs. (23), (24), (26); p. 13, Eq. (32)

import Mathlib

namespace BicliqueSDP.Chain

open Matrix

noncomputable section

/-! ## Bipartite graphs and biindependent pairs (pp. 1–2) -/

section Bipartite

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

/-- The bipartite graph `G = (V₁ ∪ V₂, E)` on the vertex type `V₁ ⊕ V₂`: the vertices `inl i` and
`inr j` are adjacent iff `E i j`, and no two vertices on the same side are adjacent. -/
def bipGraph (E : V1 → V2 → Prop) : SimpleGraph (V1 ⊕ V2) where
  Adj u v :=
    match u, v with
    | Sum.inl i, Sum.inr j => E i j
    | Sum.inr j, Sum.inl i => E i j
    | _, _ => False
  symm := ⟨fun u v huv => by cases u <;> cases v <;> simp_all⟩
  loopless := ⟨fun u huu => by cases u <;> simp at huu⟩

/-- `(A, B)` with `A ⊆ V₁`, `B ⊆ V₂` is a bipartite biindependent pair: no `i ∈ A`, `j ∈ B` is an edge. -/
def IsBiindep (E : V1 → V2 → Prop) (A : Finset V1) (B : Finset V2) : Prop :=
  ∀ i ∈ A, ∀ j ∈ B, ¬ E i j

variable (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)]

instance (A : Finset V1) (B : Finset V2) : Decidable (IsBiindep E A B) := by
  unfold IsBiindep; infer_instance

/-- All bipartite biindependent pairs of `G`. -/
def pairs : Finset (Finset V1 × Finset V2) :=
  Finset.univ.filter (fun p => IsBiindep E p.1 p.2)

/-- The balanced bipartite biindependent pairs, `|A| = |B|`. -/
def balPairs : Finset (Finset V1 × Finset V2) :=
  (pairs E).filter (fun p => p.1.card = p.2.card)

theorem empty_mem_pairs : ((∅ : Finset V1), (∅ : Finset V2)) ∈ pairs E :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩

theorem empty_mem_balPairs : ((∅ : Finset V1), (∅ : Finset V2)) ∈ balPairs E :=
  Finset.mem_filter.mpr ⟨empty_mem_pairs E, rfl⟩

/-- `α(G) = max{|A| + |B| : (A, B) biindependent}` (p. 1). -/
def alpha : ℝ :=
  (pairs E).sup' ⟨_, empty_mem_pairs E⟩ (fun p => (p.1.card : ℝ) + p.2.card)

/-- `g(G) = max{|A|·|B| : (A, B) biindependent}`, Eq. (1). -/
def g : ℝ :=
  (pairs E).sup' ⟨_, empty_mem_pairs E⟩ (fun p => (p.1.card : ℝ) * p.2.card)

/-- `h(G) = max{|A|·|B|/(|A|+|B|) : (A, B) biindependent}`, Eq. (2); the trivial pair `(∅, ∅)`
contributes `0/0 = 0`. -/
def h : ℝ :=
  (pairs E).sup' ⟨_, empty_mem_pairs E⟩
    (fun p => ((p.1.card : ℝ) * p.2.card) / ((p.1.card : ℝ) + p.2.card))

/-- `α_bal(G)`: the maximum of `|A| + |B|` over balanced biindependent pairs (p. 2). -/
def alphaBal : ℝ :=
  (balPairs E).sup' ⟨_, empty_mem_balPairs E⟩ (fun p => (p.1.card : ℝ) + p.2.card)

/-- `g_bal(G)`: Eq. (1) restricted to balanced pairs (p. 2). -/
def gBal : ℝ :=
  (balPairs E).sup' ⟨_, empty_mem_balPairs E⟩ (fun p => (p.1.card : ℝ) * p.2.card)

/-- `h_bal(G)`: Eq. (2) restricted to balanced pairs (p. 2). -/
def hBal : ℝ :=
  (balPairs E).sup' ⟨_, empty_mem_balPairs E⟩
    (fun p => ((p.1.card : ℝ) * p.2.card) / ((p.1.card : ℝ) + p.2.card))

end Bipartite

/-! ## Matrix notation (pp. 5–6, 12) -/

section MatrixNotation

variable {ι : Type} [Fintype ι]

/-- The trace inner product `⟨M, X⟩ = ∑_{i,j} M_ij X_ij`. -/
def frob (M X : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, M i j * X i j

/-- The bordered matrix `(1, diag(X)ᵀ; diag(X), X)`, indexed by `{0} ∪ ι` encoded as `Unit ⊕ ι`:
the `(0,0)` entry is `1`, the `(0,i)` and `(i,0)` entries are `X_ii`, and the `ι`-block is `X`. -/
def bordered (X : Matrix ι ι ℝ) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ j => X j j) (fun i _ => X i i) X

end MatrixNotation

/-! ## The SDP bounds `g₁`, `h₁` and the dual of `h₁` (pp. 5, 12–13) -/

section SDP

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

/-- `C = ½ (0, J; J, 0)`, Eq. (26): `C_ij = 1/2` if one of `i, j` is in `V₁` and the other in `V₂`,
and `0` otherwise. -/
def Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ :=
  Matrix.fromBlocks 0 (fun _ _ => 1 / 2) (fun _ _ => 1 / 2) 0

variable (E : V1 → V2 → Prop)

/-- `X_ij = 0` if `{i, j} ∈ E`. -/
def VanishesOnEdges (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : Prop :=
  ∀ u v, (bipGraph E).Adj u v → X u v = 0

/-- Feasibility for program (9) = (33): `X ⪰ 0`, `Tr(X) = 1`, `X_ij = 0` if `{i, j} ∈ E`. -/
def H1Feasible (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : Prop :=
  X.PosSemidef ∧ X.trace = 1 ∧ VanishesOnEdges E X

/-- Feasibility for program (8) = (36): `(1, diag(X)ᵀ; diag(X), X) ⪰ 0`, `X_ij = 0` if `{i, j} ∈ E`. -/
def G1Feasible (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : Prop :=
  (bordered X).PosSemidef ∧ VanishesOnEdges E X

/-- `g₁(G) = max{⟨C, X⟩ : (1, diag(X)ᵀ; diag(X), X) ⪰ 0, X_ij = 0 if {i, j} ∈ E}`, Eq. (8). -/
def g1 : ℝ := sSup ((fun X => frob Cmat X) '' {X | G1Feasible E X})

/-- `h₁(G) = max{⟨C, X⟩ : X ⪰ 0, Tr(X) = 1, X_ij = 0 if {i, j} ∈ E}`, Eq. (9) = (33). -/
def h1 : ℝ := sSup ((fun X => frob Cmat X) '' {X | H1Feasible E X})

/-- `Z ∈ S_G` (p. 6): `Z` is symmetric and `Z_ij = 0` whenever `{i, j} ∉ E` (including `i = j`). -/
def InSG (Z : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : Prop :=
  Z.IsSymm ∧ ∀ u v, ¬ (bipGraph E).Adj u v → Z u v = 0

/-- Feasibility for program (32): `λI + Z − C ⪰ 0` with `Z ∈ S_G`. -/
def H1DualFeasible (lam : ℝ) (Z : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : Prop :=
  InSG E Z ∧ (lam • (1 : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) + Z - Cmat).PosSemidef

/-- The value of program (32): `min{λ : λI + Z − C ⪰ 0, Z ∈ S_G}`. -/
def h1Dual : ℝ := sInf {lam : ℝ | ∃ Z, H1DualFeasible E lam Z}

end SDP

/-! ## `las₁` and the theta number for an arbitrary graph (p. 12) -/

section GeneralGraph

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- `las₁(G) = max{⟨I, X⟩ : (1, diag(X)ᵀ; diag(X), X) ⪰ 0, X_ij = 0 for {i, j} ∈ E}`, Eq. (23). -/
def las1 : ℝ :=
  sSup ((fun X : Matrix V V ℝ => X.trace) ''
    {X | (bordered X).PosSemidef ∧ ∀ i j, G.Adj i j → X i j = 0})

/-- Lovász's theta number `ϑ(G) = max{⟨J, X⟩ : X ⪰ 0, ⟨I, X⟩ = 1, X_ij = 0 for {i, j} ∈ E}`,
Eq. (24); `⟨J, X⟩ = ∑_{i,j} X_ij` and `⟨I, X⟩ = Tr(X)`. -/
def theta : ℝ :=
  sSup ((fun X : Matrix V V ℝ => ∑ i, ∑ j, X i j) ''
    {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0})

end GeneralGraph

end

end BicliqueSDP.Chain


