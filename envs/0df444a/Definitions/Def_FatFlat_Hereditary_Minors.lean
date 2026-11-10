-- Prove2me | Definitions.Def_FatFlat_Hereditary_Minors
-- name    : FatFlat_Hereditary_Minors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:42:45.958224+00:00
-- url     : https://prove2.me/theorems/1834eebd-54d8-41c0-ac50-c78e4a50ffaf
-- title:
--   Shallow minors, shallow induced minors, $(a,b)$-shallow induced 1-subdivisions, and shallow $\delta$-fat minors in unweighted graphs
-- statement:
--   Let $H$ and $G$ be graphs.
--
--   - A **model** of $H$ in $G$ assigns to each vertex $w$ of $H$ a nonempty set $B_w\subseteq V(G)$ inducing a connected subgraph, the sets pairwise disjoint, such that for every edge $uw$ of $H$ some edge of $G$ joins $B_u$ and $B_w$. It is **$r$-shallow** if every $G[B_w]$ has radius at most $r$. $G$ contains $H$ as an **$r$-shallow minor** if such a model exists.
--   - An **induced model** (the published `MISInducedMinor.InducedMinorModel`) additionally requires, for distinct $u,w$: some edge of $G$ joins $B_u$ and $B_w$ **iff** $uw\in E(H)$. $G$ contains $H$ as an **$r$-shallow induced minor** if it has an induced model with every $G[B_w]$ of radius at most $r$.
--   - The **1-subdivision** of $H$ replaces every edge by a path of length 2 through a new vertex (the published `SparseDisc.subdivide` with $k\equiv 0$). The 1-subdivision of $H$ is an **$(a,b)$-shallow induced minor** of $G$ if it has an induced model in $G$ in which the branch sets of the vertices of $H$ have radius at most $a$ and those of the subdivision vertices radius at most $b$.
--   - A **$\delta$-fat model** of $H$ in $G$ (unweighted version, $\delta\in\mathbb N$) maps every vertex and every edge of $H$ to a nonempty vertex set of $G$ inducing a connected subgraph, such that $\varphi(u)\cap\varphi(e)\neq\emptyset$ whenever $u$ is an endpoint of $e$, and for every other pair of distinct objects $o_1,o_2\in V(H)\cup E(H)$, $\mathrm{dist}_G(\varphi(o_1),\varphi(o_2))\ge\delta$, i.e. every $x\in\varphi(o_1)$ and $y\in\varphi(o_2)$ satisfy $\mathrm{dist}_G(x,y)\ge\delta$. $G$ contains $H$ as a **$d$-shallow $\delta$-fat minor** if some $\delta$-fat model has every branch set (of a vertex or an edge) of radius at most $d$.
--
--   **Formalization Note.** Branch sets are vertex sets, connected through the subgraph they induce; for fat minors the paper speaks of "connected subgraphs", and replacing a connected subgraph by the subgraph its vertex set induces keeps it connected, keeps all intersections and distances, and does not increase its radius, so the existence of a $d$-shallow $\delta$-fat model is the same. The shallow minor model is restated (not the published `RobertsonSeymour1986.GM5.IsMinor`) because the radius bound must refer to the same branch sets.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, §2.1 p. 7 (PDF 9), §2.3 'Fat minors in unweighted graphs' p. 9 (PDF 11), §4.1 p. 12 (PDF 14). PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_MISInducedMinor_InducedMinorModel
import Definitions.Def_SparseDisc_subdivide
import Definitions.Def_FatFlat_Hereditary_Basic

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- A **(minor) model** of `H` in `G` (arXiv:2607.21474, §2.1, p. 7): pairwise disjoint
nonempty branch sets `B w ⊆ V(G)`, each inducing a connected subgraph, such that for every edge
`uw` of `H` some edge of `G` joins `B u` and `B w`. -/
structure MinorModel {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set of the vertex `w` of `H`. -/
  B : W → Set V
  nonempty : ∀ w, (B w).Nonempty
  disjoint : Pairwise (Function.onFun Disjoint B)
  connected : ∀ w, (G.induce (B w)).Connected
  adj : ∀ u w, H.Adj u w → ∃ x ∈ B u, ∃ y ∈ B w, G.Adj x y

/-- `G` contains `H` as an **`r`-shallow minor**: there is a minor model of `H` in `G` whose
branch sets all induce subgraphs of radius at most `r` (§2.1, p. 7). -/
def IsShallowMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ M : MinorModel H G, ∀ w, RadiusLE G (M.B w) r

/-- `G` contains `H` as an **`r`-shallow induced minor**: there is an induced minor model of `H`
in `G` (the published `MISInducedMinor.InducedMinorModel`: nonempty, pairwise disjoint,
connected branch sets, and for distinct `u, w`, an edge of `G` between `B u` and `B w` iff
`uw ∈ E(H)`) whose branch sets all induce subgraphs of radius at most `r` (§2.1, p. 7). -/
def IsShallowInducedMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ M : MISInducedMinor.InducedMinorModel H G, ∀ w, RadiusLE G (M.B w) r

/-- The **1-subdivision** of `H`: every edge of `H` is replaced by a path of length 2 through
one new vertex (published `SparseDisc.subdivide` with `k ≡ 0`). Vertices of `H` are
`Sum.inl w`; the subdivision vertices are `Sum.inr _`. For `H = K_h`
(`⊤ : SimpleGraph (Fin h)`) this is the 1-subdivision of `K_h` (p. 4). -/
noncomputable def oneSubdivision {W : Type} (H : SimpleGraph W) :
    SimpleGraph (W ⊕ (Σ _ : H.edgeSet, Fin (0 + 1))) :=
  SparseDisc.subdivide H (fun _ => 0)

/-- The 1-subdivision of `H` is an **`(a, b)`-shallow induced minor** of `G` (§4.1, p. 12):
there is an induced minor model of the 1-subdivision of `H` in `G` in which every branch set of
a vertex of `H` induces a subgraph of radius at most `a`, and every branch set of a subdivision
vertex induces a subgraph of radius at most `b`. -/
def IsShallowInducedMinorOneSubdiv {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V)
    (a b : ℕ) : Prop :=
  ∃ M : MISInducedMinor.InducedMinorModel (oneSubdivision H) G,
    (∀ w : W, RadiusLE G (M.B (Sum.inl w)) a) ∧ (∀ x, RadiusLE G (M.B (Sum.inr x)) b)

/-- Two objects of `V(H) ∪ E(H)` are **incident** if one is a vertex `u` and the other an edge
`e` with endpoint `u`. -/
def Incident {W : Type} (H : SimpleGraph W) : W ⊕ H.edgeSet → W ⊕ H.edgeSet → Prop
  | Sum.inl u, Sum.inr e => u ∈ (e : Sym2 W)
  | Sum.inr e, Sum.inl u => u ∈ (e : Sym2 W)
  | _, _ => False

/-- A **`δ`-fat model** of `H` in an unweighted graph `G` (§2.3, "Fat minors in unweighted
graphs", p. 9): a map `φ` from the vertices and the edges of `H` to vertex sets of `G`, each
nonempty and inducing a connected subgraph, such that `φ(u)` and `φ(e)` intersect whenever `u`
is an endpoint of `e`, and for every other pair of distinct objects `o₁, o₂`,
`dist_G(φ(o₁), φ(o₂)) ≥ δ`, i.e. every `x ∈ φ(o₁)` and `y ∈ φ(o₂)` are at distance at least
`δ` (distance `⊤` between components). -/
structure FatModel {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (δ : ℕ) where
  /-- The branch set of a vertex (`Sum.inl`) or an edge (`Sum.inr`) of `H`. -/
  φ : W ⊕ H.edgeSet → Set V
  nonempty : ∀ o, (φ o).Nonempty
  connected : ∀ o, (G.induce (φ o)).Connected
  meet : ∀ (e : H.edgeSet) (u : W), u ∈ (e : Sym2 W) → (φ (Sum.inr e) ∩ φ (Sum.inl u)).Nonempty
  far : ∀ o₁ o₂, o₁ ≠ o₂ → ¬ Incident H o₁ o₂ →
    ∀ x ∈ φ o₁, ∀ y ∈ φ o₂, (δ : ℕ∞) ≤ G.edist x y

/-- `G` contains `H` as a **`d`-shallow `δ`-fat minor** (§2.3, p. 9): there is a `δ`-fat model
of `H` in `G` in which every branch set (of a vertex and of an edge) induces a subgraph of
radius at most `d`. -/
def IsShallowFatMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (d δ : ℕ) : Prop :=
  ∃ M : FatModel H G δ, ∀ o, RadiusLE G (M.φ o) d

end FatFlat.Hereditary


