-- Prove2me | Definitions.Def_MinColorPath_MinorFree_ColoredGraph
-- name    : MinColorPath_MinorFree_ColoredGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:10:32.069979+00:00
-- url     : https://prove2.me/theorems/d52ea0c9-cee4-4e1d-ae7b-462e80de0cc4
-- title:
--   Colored graphs, the color intersection graph Γ and Γ^d, cdeg, ply, cs, colored length, cdist, clean and semi-clean
-- statement:
--   A **colored graph** $\mathcal G=(G,P,\mathrm{cl})$ consists of a finite simple graph $G$, a finite **palette** $P$ and a **coloring function** $\mathrm{cl}:V(G)\to 2^P$ such that for every color $\tau\in P$ the class $V_\tau(G)=\{v:\tau\in\mathrm{cl}(v)\}$ is nonempty and $G[V_\tau(G)]$ is connected. The coloring extends to vertex sets by union, $\mathrm{cl}(S)=\bigcup_{v\in S}\mathrm{cl}(v)$.
--
--   The **color intersection graph** $\Gamma_{\mathcal G}$ has vertex set $P$, two different colors being adjacent when some vertex carries both; $\Gamma^d_{\mathcal G}$ joins two different colors at distance at most $d$ in $\Gamma_{\mathcal G}$. The **color-degree** $\mathrm{cdeg}(\mathcal G)$ is the maximum degree of $\Gamma_{\mathcal G}$, $\mathrm{ply}(\mathcal G)=\max_v|\mathrm{cl}(v)|$ and $\mathrm{cs}(\mathcal G)=\max_\tau|V_\tau(\mathcal G)|$. The **colored length** of a path $\pi$ is $|\mathrm{cl}(V(\pi))|$ and
--   $$\mathrm{cdist}(\mathcal G,a,b)=\min\{|\mathrm{cl}(V(\pi))| : \pi \text{ an } (a,b)\text{-path}\},$$
--   a **min-color** $(s,t)$-path attaining it. For $Q\subseteq P$, $\mathcal G-Q$ removes the colors of $Q$ from every vertex. With $V_0(\mathcal G)=\{v:\mathrm{cl}(v)=\emptyset\}$, $\mathcal G$ is **clean** (for terminals $s,t$) if $V_0=\{s,t\}$ and **semi-clean** if $V_0$ is an independent set containing $s$ and $t$.
--
--   **Formalization Note.** The base graph is a `SimpleGraph V` on a type `V`, colors live in a type `C`, the palette is `P : Finset C` and `cl : V → Finset C`. `IsColoredGraph` also requires `cl v ⊆ P`; "connected" is nonempty plus `Preconnected`. `colorGraph cl` is $\Gamma$ on the whole color type (colors outside $P$ are isolated); `colorPowGraph cl d` uses `edist`. `cdeg P cl` is the maximum over `P` of the number of $\Gamma$-neighbours in `P` ($0$ for empty `P`). `cdist` takes values in `ℕ∞` and is `⊤` when there is no path; `G − Q` is passed as the coloring `fun v => cl v \ Q`. Clean and semi-clean take the terminals explicitly.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 1 (problem), p. 17 'Colored graphs and related notions', p. 19 'Clean and semi-clean instances'

import Mathlib

set_option autoImplicit false

/-!
# Colored graphs and the notions of §1 and §3 (pp. 1, 17, 19)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), p. 1 (problem statement), p. 17 ("Colored graphs and related
notions"), p. 19 ("Clean and semi-clean instances").

Conventions.
* The base graph is a `SimpleGraph V` on a finite vertex type `V`; colors live in a type `C`, the
  palette is a finite set `P : Finset C`, and the coloring function is `cl : V → Finset C`.
* `G − Q` only changes the coloring (`fun v => cl v \ Q`), so every notion that depends on a
  colored graph takes `cl` (and `P` where the palette matters) as an argument.
* `cdist` takes values in `ℕ∞`; it is `⊤` when there is no path, the infimum over the empty set.
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

variable {V C : Type}

/-- `V_τ = {v : τ ∈ cl(v)}`, the vertices carrying color `τ` (p. 17). -/
def Vtau (cl : V → Finset C) (τ : C) : Set V := {v | τ ∈ cl v}

/-- `(G, P, cl)` is a colored graph (pp. 1, 17): `cl(v) ⊆ P` for every vertex, and for every
color `τ ∈ P` the class `V_τ` is nonempty and induces a connected subgraph of `G`. -/
def IsColoredGraph (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) : Prop :=
  (∀ v, cl v ⊆ P) ∧ ∀ τ ∈ P, (Vtau cl τ).Nonempty ∧ (G.induce (Vtau cl τ)).Preconnected

/-- The color intersection graph `Γ_G` (p. 17): two different colors are adjacent iff some vertex
carries both. It is a graph on the whole color type; colors outside the palette carry no vertex
and are isolated. -/
def colorGraph (cl : V → Finset C) : SimpleGraph C where
  Adj τ τ' := τ ≠ τ' ∧ ∃ v, τ ∈ cl v ∧ τ' ∈ cl v
  symm := ⟨fun _ _ ⟨h, v, h1, h2⟩ => ⟨Ne.symm h, v, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `Γ^d_G` (p. 17): two different colors are adjacent iff their distance in `Γ_G` is at most
`d` (`edist`, which is `⊤` between different components). `Γ^0_G` has no edges and
`Γ^1_G = Γ_G`. -/
def colorPowGraph (cl : V → Finset C) (d : ℕ) : SimpleGraph C where
  Adj τ τ' := τ ≠ τ' ∧ (colorGraph cl).edist τ τ' ≤ d
  symm := ⟨fun τ τ' h => ⟨Ne.symm h.1, by rw [SimpleGraph.edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `cdeg(G)`, the maximum degree of `Γ_G` on the palette `P` (p. 17); `0` for an empty
palette or an edgeless `Γ_G`. -/
noncomputable def cdeg (P : Finset C) (cl : V → Finset C) : ℕ :=
  P.sup fun τ => (P.filter fun τ' => (colorGraph cl).Adj τ τ').card

/-- `ply(G) = max_v |cl(v)|` (p. 17). -/
noncomputable def ply [Fintype V] (cl : V → Finset C) : ℕ :=
  Finset.univ.sup fun v => (cl v).card

/-- `cs(G) = max_{τ ∈ P} |V_τ(G)|` (p. 17). -/
noncomputable def cs [Fintype V] (P : Finset C) (cl : V → Finset C) : ℕ :=
  P.sup fun τ => (Finset.univ.filter fun v => τ ∈ cl v).card

/-- The colors of a vertex set, `cl(S) = ⋃_{v ∈ S} cl(v)` (p. 1). -/
def colSet (cl : V → Finset C) (S : Finset V) : Finset C := S.biUnion cl

/-- The colored length `|cl(V(π))|` of a walk (p. 17). -/
def colLen {G : SimpleGraph V} (cl : V → Finset C) {a b : V} (π : G.Walk a b) : ℕ :=
  (colSet cl π.support.toFinset).card

/-- The colored distance `cdist(G, a, b)` (p. 17): the minimum colored length of an `(a, b)`-path,
`⊤` when there is none. For `G − Q` pass `fun v => cl v \ Q`. -/
noncomputable def cdist (G : SimpleGraph V) (cl : V → Finset C) (a b : V) : ℕ∞ :=
  ⨅ (π : G.Walk a b) (_ : π.IsPath), (colLen cl π : ℕ∞)

/-- A min-color `(s, t)`-path (p. 17): an `(s, t)`-path of colored length `cdist(G, s, t)`. -/
def IsMinColorPath {G : SimpleGraph V} (cl : V → Finset C) {s t : V} (π : G.Walk s t) : Prop :=
  π.IsPath ∧ (colLen cl π : ℕ∞) = cdist G cl s t

/-- `V_0(G) = {v : cl(v) = ∅}`, the uncolored vertices (p. 19). -/
def V0 (cl : V → Finset C) : Set V := {v | cl v = ∅}

/-- `G` is clean for the terminals `s, t` (p. 19): `{v : cl(v) = ∅} = {s, t}`. -/
def IsClean (cl : V → Finset C) (s t : V) : Prop :=
  ∀ v, cl v = ∅ ↔ (v = s ∨ v = t)

/-- `G` is semi-clean for the terminals `s, t` (p. 19): `{v : cl(v) = ∅}` is an independent set
of `G` containing `s` and `t`. -/
def IsSemiClean (G : SimpleGraph V) (cl : V → Finset C) (s t : V) : Prop :=
  cl s = ∅ ∧ cl t = ∅ ∧ ∀ u v, G.Adj u v → ¬ (cl u = ∅ ∧ cl v = ∅)

end

end MinColorPath.MinorFree


