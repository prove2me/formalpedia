-- Prove2me | Definitions.Def_PinningSync_Tree_Setting
-- name    : PinningSync_Tree_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:57.074436+00:00
-- url     : https://prove2.me/theorems/ba898775-0596-4d9a-81a4-204c2de5b1bd
-- title:
--   (2.2)–(2.8), (3.5), Defs. 2.2–2.3, 2.6, 4.6, §4 pp. 1404–1407 — pinned network model, Frobenius normal form by components, blocks G̃ⱼ, Aⱼ, Π̃ⱼ, condition (4.8)
-- statement:
--   This file fixes the model of Yu, Chen, Lü and Kurths for pinning control on a network with a directed spanning tree.
--
--   **The network.** There are $N$ vertices $1,\dots,N$ with states $x_i(t)\in\mathbb R^n$. The **coupling configuration matrix** $G\in\mathbb R^{N\times N}$ satisfies (2.2): $G_{ij}\ge 0$ for $i\ne j$, where $G_{ij}>0$ means a connection from vertex $j$ to vertex $i$, and $G_{ii}=-\sum_{j\ne i}G_{ij}$, i.e. every row sums to zero. The **in-degree** of vertex $i$ is $k_i^{\mathrm{in}}=\sum_{j\ne i}G_{ij}$ (Definition 2.2), and $G$ is **strongly connected** when any vertex can be reached from any other along directed edges (Definition 2.3).
--
--   **Dynamics.** Let $f:\mathbb R^n\times\mathbb R_+\to\mathbb R^n$, let $c\in\mathbb R$ be the coupling strength and $\Gamma\in\mathbb R^{n\times n}$ the inner coupling matrix. A reference trajectory $s$ solves the isolated system (2.4) $\dot s(t)=f(s(t),t)$ for $t\ge 0$. Given pinning gains $d_i\ge 0$ (vertex $i$ is pinned iff $d_i>0$), $x$ solves the **controlled network** (2.5)–(2.6) when
--   $$
--   \dot x_i(t)=f(x_i(t),t)+c\sum_{j=1}^N G_{ij}\,\Gamma x_j(t)-c\,d_i\,\Gamma\bigl(x_i(t)-s(t)\bigr),\qquad t\ge 0 .
--   $$
--   The network is **globally synchronized** (2.7) along $(s,x)$ when $x_i(t)-s(t)\to 0$ as $t\to\infty$ for every $i$. **Assumption 1** (2.8) asks for a matrix $K$ with $(x-y)^{\mathsf T}(f(x,t)-f(y,t))\le (x-y)^{\mathsf T}K\Gamma(x-y)$ for all $x,y\in\mathbb R^n$, $t\ge 0$. For a symmetric matrix $A$, $\lambda_{\max}(A)$ is characterized as the least $\mu$ with $v^{\mathsf T}Av\le\mu\,v^{\mathsf T}v$ for all $v$; this gives $\theta=\lambda_{\max}((K+K^{\mathsf T})/2)$ of (3.5).
--
--   **Strongly connected components.** The reference state acts as a virtual leader, joined by an edge to each pinned vertex. The network **has a directed spanning tree** rooted at the leader (Definition 2.6) when every vertex is reachable from some pinned vertex along edges of $G$. A map $\mathrm{blk}$ assigns each vertex one of $M$ components, numbered in the order of the Frobenius normal form (4.2)/(4.3): every component is strongly connected inside itself, and no edge between distinct vertices goes from a later component to an earlier one (the zero upper blocks of (4.3)). For component $j$ with vertex set $V_j$:
--
--   1. $\widetilde G_j$ is the diagonal block of $G-\widetilde D$ on $V_j$, where $\widetilde D=\mathrm{diag}(d_1,\dots,d_N)$;
--   2. $A_j$ is the within-component part of $G$: off-diagonal entries $G_{ab}$ ($a,b\in V_j$) and diagonal entries $-\sum_{b\in V_j,\,b\ne a}G_{ab}$, so $A_j$ has zero row sums;
--   3. $\widetilde\Pi_j=\mathrm{diag}(\Pi_j)$ for a weight vector $\pi\in\mathbb R^N$ restricted to $V_j$;
--   4. condition (4.8) on component $j$ is $2\theta\widetilde\Pi_j+c(\widetilde\Pi_j\widetilde G_j+\widetilde G_j^{\mathsf T}\widetilde\Pi_j)<0$ (negative definite);
--   5. (Definition 4.6 and p. 1407) $C_j=\mathrm{diag}$ of the outer in-degrees $\sum_{k:\ \mathrm{blk}(k)<j}G_{ak}$, $\overline D_j=\mathrm{diag}(d_a)_{a\in V_j}$, and $\overline A_j=\tfrac12(\widetilde\Pi_jA_j+A_j^{\mathsf T}\widetilde\Pi_j)$.
--
--   These objects are the vocabulary of Theorem 4.5 and its corollaries.
--
--   **Formalization Note** States are `Fin n → ℝ`, matrices are indexed by `Fin`, and derivatives are taken within $[0,\infty)$ (right derivative at $t=0$). Convergence (2.7) is stated componentwise through the product topology, which agrees with any norm on $\mathbb R^n$. The vertices are not reordered: `blk : Fin N → Fin M` records the components and their Frobenius order, and component `j : Fin M` is the paper's component $j+2$ (the paper's component 1 is the leader). `IsLamMax A r` is unsatisfiable for a matrix with an empty index type, where $\lambda_{\max}$ is undefined. The spanning-tree condition is stated as reachability from the leader, which for a digraph is equivalent to the existence of a directed spanning tree rooted at the leader.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), pp. 1397–1400 ((2.2), (2.4)–(2.8), Definitions 2.2, 2.3, 2.6), p. 1402 ((3.5)), pp. 1404–1407 (§4: G̃, d̃, D̃, (4.2), (4.3), G̃ⱼ = Aⱼ + Bⱼ, Πⱼ, Definition 4.6, Āⱼ, D̄ⱼ, Cⱼ, (4.8))

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Tree

open Matrix Kronecker Filter Topology

/-! ### Section 4: networks with a directed spanning tree in Frobenius normal form

`blk : Fin N → Fin M` assigns each (follower) vertex its strongly connected component;
component `j : Fin M` is the paper's component `j + 2`, and the order of `Fin M` is the order
of the Frobenius normal form (4.2)/(4.3). The leader (the reference state `s`) is the paper's
component 1. -/

/-- The zero upper blocks of (4.2)/(4.3): a connection `j → i` between distinct vertices only
comes from an earlier or the same component. -/
def IsBlockLowerTriangular {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) :
    Prop :=
  ∀ i j, i ≠ j → 0 < G i j → blk j ≤ blk i

/-- An edge `a → b` inside one component. -/
def blockEdge {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) (a b : Fin N) :
    Prop :=
  a ≠ b ∧ blk a = blk b ∧ 0 < G b a

/-- Every component is strongly connected inside itself (each diagonal block `G̃ⱼ`
irreducible, Lemma 4.1). -/
def BlocksStronglyConnected {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) :
    Prop :=
  ∀ i j, blk i = blk j → i ≠ j → Relation.TransGen (blockEdge G blk) i j

/-- The augmented network `G̃` (leader plus followers) has a directed spanning tree rooted at
the leader: every vertex is reached from some pinned vertex `k` (`d k > 0`, an edge from the
leader to `k`) along edges of `G`. -/
def HasLeaderSpanningTree {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) : Prop :=
  ∀ i, ∃ k, 0 < d k ∧ Relation.ReflTransGen (PinningSync.Strong.edge G) k i

/-- The vertices of component `j`. -/
abbrev Blk {N M : ℕ} (blk : Fin N → Fin M) (j : Fin M) : Type :=
  {i : Fin N // blk i = j}

/-- `G̃ⱼ`: the diagonal block of `G - D̃` on component `j`. -/
def Gtil {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (blk : Fin N → Fin M)
    (j : Fin M) : Matrix (Blk blk j) (Blk blk j) ℝ :=
  (G - diagonal d).submatrix Subtype.val Subtype.val

/-- `Aⱼ`: the within-component part of `G` on component `j`, with zero row sums (off-diagonal
entries of `G`, diagonal equal to minus the within-component off-diagonal row sum). -/
def Ablk {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) (j : Fin M) :
    Matrix (Blk blk j) (Blk blk j) ℝ :=
  fun a b => if a = b then -∑ k : Blk blk j, (if k = a then 0 else G a.val k.val)
    else G a.val b.val

/-- `Π̃ⱼ = diag(Πⱼ)`: the restriction of the weight vector `π` to component `j`, as a diagonal
matrix. -/
def Pitil {N M : ℕ} (π : Fin N → ℝ) (blk : Fin N → Fin M) (j : Fin M) :
    Matrix (Blk blk j) (Blk blk j) ℝ :=
  diagonal (fun a => π a.val)

/-- Condition (4.8) on component `j`: `2θ Π̃ⱼ + c (Π̃ⱼ G̃ⱼ + G̃ⱼᵀ Π̃ⱼ) < 0`. -/
def cond48 {N M : ℕ} (θ c : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (π : Fin N → ℝ)
    (blk : Fin N → Fin M) (j : Fin M) : Prop :=
  (-((2 * θ) • Pitil π blk j
      + c • (Pitil π blk j * Gtil G d blk j + (Gtil G d blk j)ᵀ * Pitil π blk j))).PosDef

/-- Definition 4.6: the outer in-degree `C_{jk}` of a vertex, the total weight from the earlier
(follower) components to it. -/
def outerIn {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) (i : Fin N) : ℝ :=
  ∑ k, if blk k < blk i then G i k else 0

/-- `Cⱼ = diag(C_{j1}, …, C_{jpⱼ})`. -/
def Cdiag {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (blk : Fin N → Fin M) (j : Fin M) :
    Matrix (Blk blk j) (Blk blk j) ℝ :=
  diagonal (fun a => outerIn G blk a.val)

/-- `D̄ⱼ`: the pinning gains of component `j`, as a diagonal matrix. -/
def Dbar {N M : ℕ} (d : Fin N → ℝ) (blk : Fin N → Fin M) (j : Fin M) :
    Matrix (Blk blk j) (Blk blk j) ℝ :=
  diagonal (fun a => d a.val)

/-- `Āⱼ = ½ (Π̃ⱼ Aⱼ + Aⱼᵀ Π̃ⱼ)`. -/
noncomputable def Abar {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (π : Fin N → ℝ) (blk : Fin N → Fin M)
    (j : Fin M) : Matrix (Blk blk j) (Blk blk j) ℝ :=
  (1 / 2 : ℝ) • (Pitil π blk j * Ablk G blk j + (Ablk G blk j)ᵀ * Pitil π blk j)

end PinningSync.Tree


