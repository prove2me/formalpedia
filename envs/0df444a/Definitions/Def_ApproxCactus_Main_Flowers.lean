-- Prove2me | Definitions.Def_ApproxCactus_Main_Flowers
-- name    : ApproxCactus_Main_Flowers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:00.125316+00:00
-- url     : https://prove2.me/theorems/e625a14a-9082-4a77-a872-066b03b5a46b
-- title:
--   Cycle-decompositions, k-flowers, k-daisies, strong k-anemones, graphic-k-flowers, q-leanness, the clover-property and γ-compatibility
-- statement:
--   A **cycle-decomposition** is a graph-decomposition whose multigraph is the cycle $Z_\ell$ for some $\ell\ge2$ (for $\ell=2$: two nodes joined by two parallel edges) and which has no P-nodes. A **$k$-flower** is a cycle-decomposition all of whose displayed separations have order $\le k$. A **(strong) $k$-anemone** is a $k$-flower whose adhesion-sets have a union of size $\le k$. A **$k$-daisy** is a $k$-flower $O$ such that every narrow proper separation of order exactly $k$ induced by some set of nodes is also induced by the node set of a path in $O$ (a node set inducing a connected subgraph of $O$).
--
--   A **graphic-$k$-anemone** is a star-decomposition (the multigraph is a star $K_{1,n}$ with centre $c$: every edge is incident with $c$, there are no parallel edges, and every other node is joined to $c$) whose central bag has size $\le k$ and is contained in every leaf-bag, with $c$ as its only P-node. A **graphic-$k$-daisy** is a $k$-daisy; a **graphic-$k$-flower** is either.
--
--   With $Z$ the centre (intersection of all bags): a graphic-$k$-daisy is **$q$-lean** if for every separation of breadth $>q$ induced by a cut with edge set exactly $\{e,f\}$ ($e\ne f$), the sets $V_e\setminus Z$ and $V_f\setminus Z$ are disjoint; a graphic-$k$-anemone is $q$-lean if $|Z|=k$. A graphic-$k$-daisy has the **clover-property** if $|Z|<k$ and there are four distinct edges $e_0,\dots,e_3$ with $V_{e_i}\cap V_{e_j}=Z$ for $i\ne j$.
--
--   A separation $s=(A,B)$ is **$\gamma$-compatible** with a graphic-$k$-anemone with centre node $c$ if whenever $s$ $\gamma$-crosses a petal-separation $t$, then $s$ and $t$ cross, their centre is $V_c$ and all four links are empty; with a graphic-$k$-daisy if whenever $s$ $\gamma$-crosses the petal-separation $t$ at a node $p$, with $e\ne f$ the two edges at $p$: (i) $Z=V_e\cap V_f$ and $Z$ is the $st$-centre; (ii) $\{V_e\setminus Z,V_f\setminus Z\}$ is $\{At\text{-link},Bt\text{-link}\}$; (iii) all four links of $s,t$ have the same size.
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), pp. 22–23, 28, 45–46 (PDF 25–26, 31, 48–49), §3.4, Definitions 3.9, 6.1–6.3

import Definitions.Def_ApproxCactus_Main_Crossing
import Definitions.Def_ApproxCactus_Main_Decompositions

namespace ApproxCactus.Main

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `D` is a **cycle-decomposition** (p. 22): its decomposition graph is the cycle `Z_ℓ` for some
`ℓ ≥ 2` (nodes `0, …, ℓ − 1` in cyclic order, edge `i` joining `i` and `i + 1 mod ℓ`; for `ℓ = 2`
two parallel edges), up to relabelling of nodes and edges, and it has no P-nodes. -/
def IsCycleDecomp (D : Decomp G) : Prop :=
  D.pnode = ∅ ∧ ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ∃ (φ : Fin ℓ ≃ D.N) (χ : Fin ℓ ≃ D.E),
    ∀ i, D.ends (χ i) = s(φ i, φ (finRotate ℓ i))

/-- A **`k`-flower** (§3.4, p. 23): a cycle-decomposition of `G` all of whose displayed
separations have order `≤ k`. -/
def IsFlower (k : ℕ) (D : Decomp G) : Prop :=
  IsCycleDecomp D ∧ ∀ s, D.IsDisplayed s → order s ≤ k

/-- A **(strong) `k`-anemone** (p. 23): a `k`-flower such that the union of its adhesion-sets has
size `≤ k`. -/
def IsStrongAnemone (k : ℕ) (D : Decomp G) : Prop :=
  IsFlower k D ∧ (Finset.univ.biUnion D.adhesion).card ≤ k

/-- A **`k`-daisy** (p. 23): a `k`-flower `O` such that every narrow proper `k`-separation induced
by some subset of `V(O)` is induced by the vertex set of a path contained in `O` (a node set `J`
inducing a connected subgraph of the cycle `O`). -/
def IsDaisy (G : SimpleGraph V) (k : ℕ) (D : Decomp G) : Prop :=
  IsFlower k D ∧ ∀ I : Finset D.N,
    IsNarrow G (D.inducedSep I) → IsProper (D.inducedSep I) → order (D.inducedSep I) = k →
      ∃ J : Finset D.N, (D.skeleton.induce (J : Set D.N)).Connected ∧
        D.inducedSep J = D.inducedSep I

/-- A **graphic-`k`-anemone** (Definition 3.9, p. 28): a star-decomposition — the decomposition
graph is a star `K_{1,n}` with centre `c` (every edge is incident with `c`, no parallel edges,
every other node is joined to `c`) — whose central bag `V_c` has size `≤ k` and is contained in
every leaf-bag; the centre `c` is the only P-node. -/
def IsGraphicAnemone (k : ℕ) (D : Decomp G) : Prop :=
  ∃ c : D.N, D.pnode = {c} ∧ (∀ e, c ∈ D.ends e) ∧ Function.Injective D.ends ∧
    (∀ n, n ≠ c → ∃ e, D.ends e = s(c, n)) ∧
    (D.bag c).card ≤ k ∧ ∀ n, n ≠ c → D.bag c ⊆ D.bag n

/-- A **graphic-`k`-daisy** (Definition 3.9, p. 28) is a `k`-daisy. -/
def IsGraphicDaisy (G : SimpleGraph V) (k : ℕ) (D : Decomp G) : Prop :=
  IsDaisy G k D

/-- A **graphic-`k`-flower** (Definition 3.9): a graphic-`k`-anemone or a graphic-`k`-daisy. -/
def IsGraphicFlower (G : SimpleGraph V) (k : ℕ) (D : Decomp G) : Prop :=
  IsGraphicAnemone k D ∨ IsGraphicDaisy G k D

/-- **`q`-lean** (Definition 6.2, p. 46), with `Z` the centre (intersection of all bags):
a graphic-`k`-daisy is `q`-lean if for every `(> q)`-broad separation displayed by a set of two
edges `{e, f}` (induced by a cut with edge set exactly `{e, f}`), `V_e ∖ Z` and `V_f ∖ Z` are
disjoint; a graphic-`k`-anemone is `q`-lean if `|Z| = k`. -/
def IsQLean (G : SimpleGraph V) (q k : ℕ) (D : Decomp G) : Prop :=
  (IsGraphicDaisy G k D → ∀ (U : Finset D.N) (e f : D.E), e ≠ f → D.cutEdges U = {e, f} →
      q < breadth (D.inducedSep U) → Disjoint (D.adhesion e \ D.centre) (D.adhesion f \ D.centre)) ∧
    (IsGraphicAnemone k D → D.centre.card = k)

/-- The **clover-property** of a graphic-`k`-daisy (Definition 6.3, p. 46): its centre `X` has size
`< k` and there are four (distinct) edges `e₀, …, e₃` whose adhesion-sets satisfy
`V_{e_i} ∩ V_{e_j} = X` for all `i ≠ j`. -/
def HasClover (k : ℕ) (D : Decomp G) : Prop :=
  D.centre.card < k ∧ ∃ e : Fin 4 → D.E, Function.Injective e ∧
    ∀ i j, i ≠ j → D.adhesion (e i) ∩ D.adhesion (e j) = D.centre

/-- **`γ`-compatible** (Definition 6.1, pp. 45–46). For a graphic-`k`-anemone with centre node `c`
and `Z := V_c`: whenever `s` `γ`-crosses a petal-separation `t`, then `s` and `t` cross, their
centre is `Z`, and all four links are empty. For a graphic-`k`-daisy with `Z` the intersection of
all bags: whenever `s = (A, B)` `γ`-crosses the petal-separation `t` at a node `p`, with `e ≠ f` the
two edges at `p`: (i) `Z = V_e ∩ V_f` and `Z` is the `st`-centre; (ii) `{V_e ∖ Z, V_f ∖ Z}` is
`{At-link, Bt-link}`; (iii) all four links of `s, t` have the same size. -/
def IsCompatible (G : SimpleGraph V) (k γ : ℕ) (D : Decomp G) (s : Finset V × Finset V) : Prop :=
  (IsGraphicAnemone k D → ∀ c ∈ D.pnode, ∀ p : D.N, CrossEps γ s (D.petalSep p) →
      Crosses s (D.petalSep p) ∧ centre2 s (D.petalSep p) = D.bag c ∧
      linkFst s (D.petalSep p) = ∅ ∧ linkSnd s (D.petalSep p) = ∅ ∧
      linkFst (D.petalSep p) s = ∅ ∧ linkSnd (D.petalSep p) s = ∅) ∧
    (IsGraphicDaisy G k D → ∀ p : D.N, CrossEps γ s (D.petalSep p) →
      ∀ e f : D.E, e ≠ f → p ∈ D.ends e → p ∈ D.ends f →
        (D.centre = D.adhesion e ∩ D.adhesion f ∧ D.centre = centre2 s (D.petalSep p)) ∧
        ((D.adhesion e \ D.centre = linkFst (D.petalSep p) s ∧
            D.adhesion f \ D.centre = linkSnd (D.petalSep p) s) ∨
          (D.adhesion e \ D.centre = linkSnd (D.petalSep p) s ∧
            D.adhesion f \ D.centre = linkFst (D.petalSep p) s)) ∧
        ((linkFst s (D.petalSep p)).card = (linkSnd s (D.petalSep p)).card ∧
          (linkSnd s (D.petalSep p)).card = (linkFst (D.petalSep p) s).card ∧
          (linkFst (D.petalSep p) s).card = (linkSnd (D.petalSep p) s).card))

end ApproxCactus.Main


