-- Prove2me | Definitions.Def_LocalSepDecomp_Cutouts
-- name    : LocalSepDecomp_Cutouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:30.845333+00:00
-- url     : https://prove2.me/theorems/be031571-1e6f-4942-aad7-4308b417eb6c
-- title:
--   Cutouts and parts of a nested set of $r$-local separations, the decomposition $H(N)$, $H^{\le k}_r(G)$ and the folding of $H(\hat N)$
-- statement:
--   Let $N$ be a set of $r$-local separations of $G$, $\operatorname{ori}(N)$ the set of their orientations, and for $s=(E_1,X,E_2)$ write $X(s)=X$, $R(s)=E_2$.
--
--   1. $s_1\,\Sigma^{vx}_N\,s_2$ if $X(s_1),X(s_2)$ share a vertex $v$, $s_1\succ s_2^*$, and no $s\in\operatorname{ori}(N)$ with $v\in X(s)$ satisfies $s_1\succ s\succ s_2^*$.
--   2. $R_N(s)=R(s)\setminus\bigcup\{R(s'):s'\in\operatorname{ori}(N),\ X(s')\cap X(s)\neq\emptyset,\ s\succ s'\}$.
--   3. $\mathcal K(N)$ is the set of components of $G-\bigcup_{u\in N}X(u)$; $s_1\,\Sigma^K_N\,s_2$ if some $K\in\mathcal K(N)$ has $\partial K$ meeting both $R_N(s_1)$ and $R_N(s_2)$; $s_1\,\Sigma^{\mathcal X}_N\,s_2$ if some edge bridging the separators (both ends in $\bigcup X(u)$, no separator containing both) lies in $R_N(s_1)\cap R_N(s_2)$.
--   4. The **cutouts** of $N$ are the classes of the reflexive transitive closure $\Sigma_N$ of the union of the three relations. The **$\sigma$-part** is the union of $G[X(s)]$ for $s\in\sigma$, the components $K\in\mathcal K(N)$ whose boundary meets some $R_N(s)$, $s\in\sigma$, and the edges in $R_N(s)$, $s\in\sigma$.
--   5. **$H(N)$** (Construction 8.17): if $N=\emptyset$, one node with part $G$; otherwise the nodes are the cutouts, the edges are the elements of $N$, $\{E_1,X,E_2\}$ joins the cutouts containing $(E_2,X,E_1)$ and $(E_1,X,E_2)$, and the part of a cutout is its part. Then
--   $$H^{\le k}_r(G):=H\bigl(N^{\le k}_r(G)\bigr),$$
--   and its edges **represent** all $r$-local bottlenecks of order $\le k$ if each of them contains an element of $N^{\le k}_r(G)$.
--   6. For a covering $p:C\to G$ and a set $\hat N$ of $r$-local separations of $C$, $\bar H(N)$ is $H(\hat N)$ folded via $p$ along the natural action of the deck transformations. The isomorphism $\tau$ of Theorem 8.21 sends a cutout $\sigma$ to the set of cutouts $\hat\sigma$ with $p(\hat\sigma)=\sigma$ and $s\in N$ to the set of its lifts.
--
--   This is the paper's finite, local construction of a graph-decomposition from a nested set of $r$-local separations.
--
--   **Formalization Note** The single node of $H(\emptyset)$ is represented by the empty set of orientations. In part (iii), each edge of $R_N(s)$ is added together with its ends.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §8.1 (pp.50–51), §8.2 (pp.51–52), Construction 8.17 (p.54), Theorem 8.21 (p.55), §9 (p.56)

import Mathlib
import Definitions.Def_LocalSepDecomp_Bottlenecks
import Definitions.Def_LocalSepDecomp_Decompositions

set_option autoImplicit false

open Classical

namespace LocalSepDecomp

/-! # Cutouts and parts of a nested set of r-local separations, the candidate `H(N)`,
`H^{≤k}_r(G)`, and the folding of `H(N̂)` along a covering

R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §8.1 (pp.50–51), §8.2
(pp.51–52), Construction 8.17 (p.54), Theorem 8.21 (p.55), §9 (p.56).

**Formalization Note.**
1. For an oriented `r`-local separation `s = (E₁, X, E₂)`: `X(s) = X`, `L(s) = E₁`, `R(s) = E₂`;
   `ori(N)` is the set of orientations of the elements of `N`.
2. `H(N)` has as nodes the cutouts of `N` when `N ≠ ∅`, and the single node `∅` with part `G`
   when `N = ∅` (Construction 8.17). Its edges are the elements of `N`; the edge `{E₁, X, E₂}`
   joins the cutout containing `(E₂, X, E₁)` and the one containing `(E₁, X, E₂)`.
3. Part (iii) of `part(σ)` adds the edges in `R_N(s)` together with their ends (which lie in the
   graphs of (i) and (ii) in every case the paper uses, by its Lemma 8.2). -/

open SimpleGraph

universe u

variable {V : Type u}

/-- `ori(N)`: the set of all orientations of the `r`-local separations in `N` (p.51). -/
def ori (N : Set (ULSep V)) : Set (LSep V) := {s | s.unorient ∈ N}

/-- The relation `s₁ Σ^vx_N s₂` on `ori(N)` (p.52): `X(s₁)` and `X(s₂)` share a vertex `v` with
`s₁ ≻ s₂*`, and there is no `s ∈ ori(N)` with `v ∈ X(s)` and `s₁ ≻ s ≻ s₂*`. -/
def SigmaVx (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s₁ s₂ : LSep V) : Prop :=
  ∃ v, v ∈ s₁.X ∧ v ∈ s₂.X ∧ LSucc G r s₁ s₂.inv ∧
    ¬ ∃ s ∈ ori N, v ∈ s.X ∧ LSucc G r s₁ s ∧ LSucc G r s s₂.inv

/-- `R_N(s) := R(s) ∖ ⋃ { R(s') : s' ∈ ori(N), X(s') meets X(s), s ≻ s' }` (p.52). -/
def RN (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s : LSep V) : Set (Sym2 V) :=
  s.E₂ \ ⋃ (s' ∈ ori N) (_ : (s'.X ∩ s.X).Nonempty ∧ LSucc G r s s'), s'.E₂

/-- `⋃ X(N)`: the union of the separators of the elements of `N` (p.52). -/
def sepUnion (N : Set (ULSep V)) : Set V := ⋃ u ∈ N, u.X

/-- `K(N)`: the set of (vertex sets of) components of `G − ⋃ X(N)` (p.52). -/
def KN (G : SimpleGraph V) (N : Set (ULSep V)) : Set (Set V) :=
  {K | IsCompOn G (sepUnion N)ᶜ K}

/-- The relation `s₁ Σ^K_N s₂` (p.52): some `K ∈ K(N)` has `∂K` meeting `R_N(sᵢ)` for both
`i = 1, 2`. -/
def SigmaK (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s₁ s₂ : LSep V) : Prop :=
  ∃ K ∈ KN G N, (boundary G K ∩ RN G r N s₁).Nonempty ∧ (boundary G K ∩ RN G r N s₂).Nonempty

/-- The edge `e` **bridges** `X(N)` (p.50): both ends of `e` lie in `⋃ X(N)` but every separator
in `X(N)` contains at most one end of `e`. -/
def Bridges (G : SimpleGraph V) (N : Set (ULSep V)) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ a b, e = s(a, b) ∧ a ∈ sepUnion N ∧ b ∈ sepUnion N ∧
    ∀ u ∈ N, ¬ (a ∈ u.X ∧ b ∈ u.X)

/-- The relation `s₁ Σ^X_N s₂` (p.52): some `X(N)`-bridging edge lies in `R_N(sᵢ)` for both
`i = 1, 2`. -/
def SigmaX (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s₁ s₂ : LSep V) : Prop :=
  ∃ e, Bridges G N e ∧ e ∈ RN G r N s₁ ∧ e ∈ RN G r N s₂

/-- The union of `Σ^vx_N`, `Σ^K_N` and `Σ^X_N` on `ori(N)`. -/
def SigmaRel (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s₁ s₂ : LSep V) : Prop :=
  s₁ ∈ ori N ∧ s₂ ∈ ori N ∧ (SigmaVx G r N s₁ s₂ ∨ SigmaK G r N s₁ s₂ ∨ SigmaX G r N s₁ s₂)

/-- The `Σ_N`-class of `s`, where `Σ_N` is the reflexive transitive closure of the union of the
three symmetric relations (p.52). -/
def cutoutOf (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (s : LSep V) : Set (LSep V) :=
  {t | Relation.ReflTransGen (SigmaRel G r N) s t}

/-- `σ` is a **cutout** of `N` (p.52): an equivalence class of `Σ_N` on `ori(N)`. -/
def IsCutout (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (σ : Set (LSep V)) : Prop :=
  ∃ s ∈ ori N, σ = cutoutOf G r N s

/-- The **`σ`-part** `part(σ)` of `G` (pp.51–52): the union of (i) `G[X(s)]` for `s ∈ σ`, (ii) the
components `K ∈ K(N)` such that `∂K` shares an edge with `R_N(s)` for some `s ∈ σ`, and (iii) the
edges in `R_N(s)` for `s ∈ σ`. -/
noncomputable def partOf (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) (σ : Set (LSep V)) :
    G.Subgraph :=
  (⨆ s ∈ σ, (⊤ : G.Subgraph).induce s.X) ⊔
    (⨆ (K : Set V) (_ : K ∈ KN G N ∧ ∃ s ∈ σ, (boundary G K ∩ RN G r N s).Nonempty),
      (⊤ : G.Subgraph).induce K) ⊔
    ⨆ s ∈ σ, edgeSubgraph G (RN G r N s)

/-- A chosen orientation of an unoriented triple. -/
noncomputable def ULSep.rep (u : ULSep V) : LSep V := ⟨u.sides.out.1, u.X, u.sides.out.2⟩

theorem ULSep.rep_unorient (u : ULSep V) : u.rep.unorient = u := by
  ext1
  · exact Quot.out_eq u.sides
  · rfl

theorem rep_mem_ori {N : Set (ULSep V)} (e : {u : ULSep V // u ∈ N}) : e.1.rep ∈ ori N := by
  simp [ori, ULSep.rep_unorient, e.2]

theorem rep_inv_mem_ori {N : Set (ULSep V)} (e : {u : ULSep V // u ∈ N}) :
    e.1.rep.inv ∈ ori N := by
  simp [ori, LSep.unorient_inv, ULSep.rep_unorient, e.2]

/-- The candidate **`H(N)`** for a graph-decomposition with parts (Construction 8.17, p.54). If
`N = ∅`, the trivial decomposition: one node (here the empty set) with part `G`. Otherwise the
nodes are the cutouts of `N`, the edges are the elements of `N`, the edge `{E₁, X, E₂}` joins the
cutouts `σ₁ ∋ (E₂, X, E₁)` and `σ₂ ∋ (E₁, X, E₂)`, and the part of a cutout `h` is the
`h`-part of `G`. -/
noncomputable def Hdecomp (G : SimpleGraph V) (r : ℕ) (N : Set (ULSep V)) :
    GraphDecomp.{u, u} G where
  Node := {σ : Set (LSep V) // IsCutout G r N σ ∨ (N = ∅ ∧ σ = ∅)}
  Edge := {u : ULSep V // u ∈ N}
  ends e := s(⟨cutoutOf G r N e.1.rep.inv, Or.inl ⟨_, rep_inv_mem_ori e, rfl⟩⟩,
    ⟨cutoutOf G r N e.1.rep, Or.inl ⟨_, rep_mem_ori e, rfl⟩⟩)
  part h := if N = ∅ then ⊤ else partOf G r N h.1

/-- **`H^{≤k}_r(G) := H(N^{≤k}_r(G))`** (§9, p.56), with `N^{≤k}_r(G)` built from the set of all
`r`-local bottlenecks of order `≤ k`. -/
noncomputable def Hle (G : SimpleGraph V) (r k : ℕ) : GraphDecomp.{u, u} G :=
  Hdecomp G r (NleSec9 G r k)

/-- The edges `N` of `H(N)` **represent all the `r`-local bottlenecks in `G` of order `≤ k`**
(p.56): every `r`-local bottleneck of order `≤ k` contains an element of `N`. -/
def RepresentsLBottlenecks (G : SimpleGraph V) (r k : ℕ) (N : Set (ULSep V)) : Prop :=
  ∀ j ≤ k, ∀ β, IsLocalBottleneck G r j β → (β ∩ N).Nonempty

/-- The graph-decomposition `H̄(N) = (H̄, Ḡ)` of `G` obtained from `H(N̂)`, a decomposition of the
cover `C`, by folding via `p` (Construction 2.6; Theorem 8.21, p.55): nodes and edges are the
orbits of the cutouts and of the elements of `N̂` under the natural action of the deck
transformations of `p`. -/
noncomputable def foldedH {W : Type u} {G : SimpleGraph V} {C : SimpleGraph W} (p : C →g G)
    (r : ℕ) (Nh : Set (ULSep W)) : GraphDecomp.{u, u} G :=
  foldDecomp (Hdecomp C r Nh) p
    (fun a b => ∃ φ : C ≃g C, IsDeck p φ ∧ b.1 = LSep.map φ '' a.1)
    (fun a b => ∃ φ : C ≃g C, IsDeck p φ ∧ b.1 = ULSep.map φ a.1)

/-- The isomorphism `ψ : H(N) → H̄(N)` is the map `τ` of Theorem 8.21 (p.55): `τ(σ)` is the set of
all cutouts `σ̂` of `N̂` with `p(σ̂) = σ` (the node class of `σ̂` is `ψ(σ)` iff `p(σ̂) = σ`), and
`τ(s)` is the set of all lifts of `s` (the edge class of `ŝ` is `ψ(s)` iff `ŝ` is a lift of `s`).
For `N = ∅` this sends the trivial node to the class of the trivial node of `H(∅)`. -/
def IsTauIso {W : Type u} {G : SimpleGraph V} {C : SimpleGraph W} (p : C →g G) (r : ℕ)
    (N : Set (ULSep V)) (Nh : Set (ULSep W))
    (ψ : DecompIso (Hdecomp G r N) (foldedH p r Nh)) : Prop :=
  (∀ (σ : (Hdecomp G r N).Node) (σh : (Hdecomp C r Nh).Node),
      ψ.node σ = Quot.mk _ σh ↔ lsepProj p '' σh.1 = σ.1) ∧
    ∀ (s : (Hdecomp G r N).Edge) (sh : (Hdecomp C r Nh).Edge),
      ψ.edge s = Quot.mk _ sh ↔ IsULSepLift p r sh.1 s.1

end LocalSepDecomp


