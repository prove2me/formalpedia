-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Supplement_Gadgets
-- name    : DistributedMWC440_UpperBound_Supplement_Gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:04.784104+00:00
-- url     : https://prove2.me/theorems/712e19eb-3dea-42f2-9212-b5f20148923b
-- title:
--   The lower-bound graphs $G(H,x,y)$ and $G_{d,p}(H,x,y)$
-- statement:
--   Let $H=(L\cup R,E_H)$ be a bipartite graph with parts $L=\{\ell_1,\dots,\ell_\gamma\}$ and $R=\{\rho_1,\dots,\rho_\gamma\}$, and let $x,y\in\{0,1\}^{E_H}$, with $\langle x,y\rangle=\sum_{e\in E_H}x_ey_e$.
--
--   1. **The basic two-copy graph $G(H,x,y)$** has vertices $a_i,b_j$ (a copy of $L\cup R$) and $u_i,v_j$ (a second copy). For each $e=\{\ell_i,\rho_j\}\in E_H$ it contains $\{a_i,b_j\}$ if $x_e=1$ and $\{u_i,v_j\}$ if $y_e=1$, and it contains the perfect matching $\{a_i,u_i\}$, $\{b_j,v_j\}$. In the directed unweighted variant the arcs are $a_i\to u_i$, $u_i\to v_j$ (iff $y_e=1$), $v_j\to b_j$, $b_j\to a_i$ (iff $x_e=1$). In the undirected weighted variant matching edges weigh $0$ and edges inside the copies weigh $1$.
--   2. **The CONGEST graph $G_{d,p}(H,x,y)$** ($d\ge2$, $p\ge1$) replaces each matching edge $\{a_i,u_i\}$ by a path $Q_i=(q^i_0=a_i,\dots,q^i_{d^p-1}=u_i)$ of $d^p$ nodes and each $\{b_j,v_j\}$ by $R_j=(r^j_0=b_j,\dots,r^j_{d^p-1}=v_j)$, and adds a complete $d$-ary tree $T$ of depth $p$ with nodes $t^h_0,\dots,t^h_{d^h-1}$ at depth $h$ (the parent of $t^{h+1}_{a}$ is $t^h_{\lfloor a/d\rfloor}$), joining each leaf $t^p_s$ to $q^i_s$ and $r^j_s$ for all $i,j$. Directed variant: $Q_i$ oriented from $a_i$ to $u_i$, $R_j$ from $v_j$ to $b_j$, $b_j\to a_i$ iff $x_e=1$, $u_i\to v_j$ iff $y_e=1$, tree edges away from the root and leaf–path edges away from the leaf. Weighted variant: edges inherited from $H$ weigh $1$, path edges $0$, and every overlay edge (tree and leaf–path) $2(k+1)$.
--
--   These are the hard instances of the reductions from set-disjointness behind Theorems 5 and 2; Lemmas 8.1 and 8.4 state their approximation gaps.
--
--   **Formalization Note** $H$ is given by $E\subseteq \mathrm{Fin}\,\gamma\times\mathrm{Fin}\,\gamma$ and lives on $\mathrm{Fin}\,\gamma\oplus\mathrm{Fin}\,\gamma$; $x,y$ are Boolean functions on $E$. Each undirected graph is the corresponding digraph with orientation forgotten, which gives exactly the edge sets above. The weighted variants are instances of the published nonnegative weighted graph, so the $0$-weight edges are allowed.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), §8.1, printed pp. 43–44 / PDF pp. 45–46; §8.3, printed pp. 46–47 / PDF pp. 48–49.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_Directed

open scoped ENNReal

noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-!
The lower-bound graphs of §8 of Chang et al., STOC 2027 submission #440: the basic two-copy
construction `G(H, x, y)` (§8.1, printed pp. 43–44 / PDF pp. 45–46) and the CONGEST construction
`G_{d,p}(H, x, y)` (§8.3, printed pp. 46–47 / PDF pp. 48–49), each in its directed unweighted and
its undirected weighted variant.

The bipartite graph `H = (L ∪ R, E_H)` has parts `L = {ℓ_i}`, `R = {ρ_j}` indexed by `Fin γ`; an
edge `{ℓ_i, ρ_j}` is the pair `(i, j) ∈ E`. The input strings are `x, y : E → Bool`
(`true` = bit `1`).
-/

/-- The bipartite graph `H` on `L ⊕ R = Fin γ ⊕ Fin γ` with edge set `E ⊆ Fin γ × Fin γ`. -/
def HGraph (γ : ℕ) (E : Finset (Fin γ × Fin γ)) : SimpleGraph (Fin γ ⊕ Fin γ) :=
  SimpleGraph.fromRel fun p q => ∃ i j, p = Sum.inl i ∧ q = Sum.inr j ∧ (i, j) ∈ E

/-- `x_e = 1` for the edge `e = {ℓ_i, ρ_j}` of `H` (false when `{ℓ_i, ρ_j}` is not an edge). -/
def bit {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x : E → Bool) (i j : Fin γ) : Prop :=
  ∃ h : (i, j) ∈ E, x ⟨(i, j), h⟩ = true

/-- `⟨x, y⟩ = ∑_{e ∈ E_H} x_e y_e`. -/
def inner {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) : ℕ :=
  ∑ e : E, (x e).toNat * (y e).toNat

/-! ### The basic two-copy construction `G(H, x, y)` -/

/-- Vertices `a_i, b_j` (first copy of `L ∪ R`) and `u_i, v_j` (second copy). -/
inductive BasicV (γ : ℕ) where
  | a (i : Fin γ)
  | b (j : Fin γ)
  | u (i : Fin γ)
  | v (j : Fin γ)

/-- Directed unweighted variant: `a_i → u_i`, `v_j → b_j` always; `u_i → v_j` iff
`y_{ℓ_i ρ_j} = 1`; `b_j → a_i` iff `x_{ℓ_i ρ_j} = 1`. -/
def basicArc {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) :
    BasicV γ → BasicV γ → Prop
  | .a i, .u i' => i = i'
  | .u i, .v j => bit E y i j
  | .v j, .b j' => j = j'
  | .b j, .a i => bit E x i j
  | _, _ => False

def basicDigraph {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) : Digraph (BasicV γ) :=
  ⟨basicArc E x y⟩

/-- The undirected graph `G(H, x, y)`: `{a_i, b_j}` iff `x_e = 1`, `{u_i, v_j}` iff `y_e = 1`, and
the perfect matching `{a_i, u_i}`, `{b_j, v_j}`. These are exactly the arcs of the directed
variant with orientation forgotten. -/
def basicGraph {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) : SimpleGraph (BasicV γ) :=
  SimpleGraph.fromRel (basicArc E x y)

/-- Weights of the undirected weighted variant: matching edges `0`, edges inside the copies `1`
(the value on a non-adjacent pair is never used). -/
def basicLength {γ : ℕ} : BasicV γ → BasicV γ → ℝ
  | .a _, .u _ => 0
  | .u _, .a _ => 0
  | .b _, .v _ => 0
  | .v _, .b _ => 0
  | _, _ => 1

/-- The undirected weighted variant of `G(H, x, y)` as a published weighted graph. -/
def basicWGraph {γ : ℕ} (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) : WGraph (BasicV γ) where
  graph := basicGraph E x y
  length := basicLength
  symmetric := by
    intro s t
    cases s <;> cases t <;> rfl
  nonnegative := by
    intro s t _
    cases s <;> cases t <;> simp [basicLength]

/-! ### The CONGEST construction `G_{d,p}(H, x, y)` -/

/-- Vertices of `G_{d,p}(H, x, y)`: path nodes `q^i_s` of `Q_i` and `r^j_s` of `R_j`
(`s < d^p`, with `q^i_0 = a_i`, `q^i_{d^p-1} = u_i`, `r^j_0 = b_j`, `r^j_{d^p-1} = v_j`), and the
nodes `t^h_a` (`h ≤ p`, `a < d^h`) of the complete `d`-ary overlay tree `T` of depth `p`. -/
inductive CongV (γ d p : ℕ) where
  | q (i : Fin γ) (s : Fin (d ^ p))
  | r (j : Fin γ) (s : Fin (d ^ p))
  | t (h : Fin (p + 1)) (a : Fin (d ^ h.val))

/-- Directed unweighted variant: `Q_i` oriented from `a_i` to `u_i`; `R_j` oriented from `v_j` to
`b_j`; `b_j → a_i` iff `x_{ℓ_i ρ_j} = 1`; `u_i → v_j` iff `y_{ℓ_i ρ_j} = 1`; tree edges away from
the root (the parent of `t^{h+1}_{a'}` is `t^h_{⌊a'/d⌋}`); leaf `t^p_s` to `q^i_s` and `r^j_s`,
away from the leaf. -/
def congArc {γ : ℕ} (d p : ℕ) (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) :
    CongV γ d p → CongV γ d p → Prop
  | .q i s, .q i' s' => i = i' ∧ s'.val = s.val + 1
  | .r j s, .r j' s' => j = j' ∧ s.val = s'.val + 1
  | .r j s, .q i s' => s.val = 0 ∧ s'.val = 0 ∧ bit E x i j
  | .q i s, .r j s' => s.val = d ^ p - 1 ∧ s'.val = d ^ p - 1 ∧ bit E y i j
  | .t h a, .t h' a' => h'.val = h.val + 1 ∧ a'.val / d = a.val
  | .t h a, .q _ s => h.val = p ∧ a.val = s.val
  | .t h a, .r _ s => h.val = p ∧ a.val = s.val
  | _, _ => False

def congDigraph {γ : ℕ} (d p : ℕ) (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) :
    Digraph (CongV γ d p) :=
  ⟨congArc d p E x y⟩

/-- The undirected graph `G_{d,p}(H, x, y)`: the edges of the directed variant, orientation
forgotten. -/
def congGraph {γ : ℕ} (d p : ℕ) (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) :
    SimpleGraph (CongV γ d p) :=
  SimpleGraph.fromRel (congArc d p E x y)

/-- Weights of the undirected weighted variant: edges inherited from `H` weigh `1`, path edges of
`Q ∪ R` weigh `0`, and every overlay edge (tree edges and leaf–path edges) weighs `2(k+1)`. -/
def congLength {γ d p : ℕ} (k : ℕ) : CongV γ d p → CongV γ d p → ℝ
  | .q _ _, .q _ _ => 0
  | .r _ _, .r _ _ => 0
  | .q _ _, .r _ _ => 1
  | .r _ _, .q _ _ => 1
  | _, _ => 2 * ((k : ℝ) + 1)

def congWGraph {γ : ℕ} (k d p : ℕ) (E : Finset (Fin γ × Fin γ)) (x y : E → Bool) :
    WGraph (CongV γ d p) where
  graph := congGraph d p E x y
  length := congLength k
  symmetric := by
    intro s t
    cases s <;> cases t <;> rfl
  nonnegative := by
    intro s t _
    cases s <;> cases t <;> simp [congLength] <;> positivity

end DistributedMWC440.UpperBound.Supplement


