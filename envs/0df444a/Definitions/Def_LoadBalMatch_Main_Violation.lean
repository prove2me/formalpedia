-- Prove2me | Definitions.Def_LoadBalMatch_Main_Violation
-- name    : LoadBalMatch_Main_Violation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:59.769706+00:00
-- url     : https://prove2.me/theorems/3e4ef18b-0350-46d8-82be-e8c7f2df2a02
-- title:
--   Spanning forests of the contracted graph $\widehat G_H$, the weights $w$ and $q$, violating edges $F(x)$ (Definitions 7.5, 7.12, eq. (36))
-- statement:
--   Let $H\subseteq G$ be graphs on $V$, $(D,A,C)$ the Gallai–Edmonds decomposition of $H$ with components $D_1,\dots,D_r$ of $H[D]$, and $x$ a fractional matching of $H$ with loads $x_v$ and levels $\ell_v$ in $H$.
--
--   The **contracted graph** $\widehat G_H$ (Definition 7.5) is obtained from $G[D]$ by contracting each $D_i$ to one vertex and deleting self-loops, keeping parallel edges; each of its edges is an edge of $G$. A **spanning forest** $T$ of $\widehat G_H$ is a set of such edges (edges of $G$ between different components $D_i$) that contains no cycle of $\widehat G_H$ and connects every connected component of $\widehat G_H$.
--
--   The **weight** of eq. (36) of an edge $e=(u,v)$ is
--   $$w(e)=\begin{cases}(\ell_v-x_u)^2 & \text{if } u\in D,\ v\in A\cup C,\ \ell_v>x_u,\\ 0&\text{otherwise,}\end{cases}$$
--   the same weight Lemma 7.4 writes with the $A\cup C$ endpoint first; for an edge $uv$ between different components of $H[D]$, $q(uv)=(1-x_u)^2$.
--
--   An edge $(u,v)$ of $G$ **violates** $x$ (Definition 7.12) if $u\in A\cup C$, $v\in D$ and $\ell_u>x_v$, or $u,v\in D$ lie in different components of $H[D]$; $F(x)$ is the set of violating edges, and for a vector $z$ the **mass** of $z$ on $F(x)$ is $\sum_{e\in F(x)}z_e$.
--
--   These objects drive one iteration of Algorithms 3 and 4: $w$ is the weight of the external matching, $\widehat G_H$ carries the spanning forest, and the sampling probabilities are doubled on $F(x)$.
--
--   **Formalization Note.** `IsContractedSpanningForest G H T`: every `e ∈ T` is an edge `uv` of `G` with `u, v ∈ D` in different components; any two vertices of `D` connected in $(G\cup H)[D]$ are connected in $(H\cup T)[D]$ (spanning); and for no `e = uv ∈ T` are `u, v` connected in $(H\cup(T\setminus\{e\}))[D]$ (acyclic, parallel edges included). `extWeight H x` is $w$ on unordered pairs, the sum of the two orientations (at most one is nonzero since $D$ and $A\cup C$ are disjoint). `qWeight x` on $uv$ is $((1-x_u)^2+(1-x_v)^2)/2$, which is $q(uv)$ whenever $x_u=x_v$. `dCompsWithExit G H` is the set of components $D_i$ with $E_G[D_i,D\setminus D_i]\neq\emptyset$. `violMass G H x z` is $\sum_{e\in F(x)}z_e$.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 36, Definition 7.5; pp. 41-42, Definition 7.12; p. 46, eq. (36); p. 32 and p. 42 (weight q)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds

/-!
# Spanning forests of the contracted graph Ĝ_H, the weights w and q, violating edges F(x)

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…):
* Definition 7.5, p. 36: "The contracted graph Ĝ_H is obtained from G[D] by contracting each Dᵢ
  to a single vertex and deleting self-loops. We retain parallel edges and identify each edge of
  Ĝ_H with its corresponding edge of G. In particular, we regard a spanning forest F of Ĝ_H as a
  subset of E."
* eq. (36), p. 46 (= eq. (23), p. 40): `w(e) = (ℓ_v − x_u)²` if `u ∈ D, v ∈ A ∪ C` and
  `ℓ_v > x_u`, and `0` otherwise, for `e = (u, v)`. Lemma 7.4 (p. 34) writes the same weight with
  the `A ∪ C` endpoint first.
* p. 32 and proof of Lemma 7.13, p. 42: for an edge `uv` of `G[D]` between different components
  of `H[D]`, `q(uv) = (1 − x_u)² = (1 − x_v)²`.
* Definition 7.12, pp. 41–42: `(u, v) ∈ G` violates `x` if `u ∈ A ∪ C, v ∈ D` and `ℓ_u > x_v`, or
  `u, v ∈ D` lie in different connected components of `H[D]`; `F(x)` is the set of violating
  edges of `G`.

Formalization Note.
* `IsContractedSpanningForest G H T`: `T` is a set of edges of `G` joining vertices of `D` in
  different components of `H[D]` (the edges of `Ĝ_H`); two vertices of `D` connected in
  `(G ∪ H)[D]` (equivalently, whose components are connected in `Ĝ_H`) are connected in
  `(H ∪ T)[D]` (spanning); and no `e ∈ T` has its ends connected in `(H ∪ (T \ {e}))[D]` (no cycle
  of `Ĝ_H`, parallel edges included).
* `extWeight H x` is eq. (36) on unordered pairs: the sum of the two orientations, at most one of
  which is nonzero because `D` and `A ∪ C` are disjoint.
* `qWeight x uv = ((1 − x_u)² + (1 − x_v)²)/2`; it equals the paper's `(1 − x_u)² = (1 − x_v)²`
  on every edge where the two loads agree (Lemma 6.9 gives this on `G[D]` for stable `H`).
* `violMass G H x z = Σ_{e ∈ F(x)} z_e`, the mass of a vector `z` on the violating edges (with
  `z = x⋆` in Lemma 7.13 and Definition 8.2, `z = p` in Lemma 8.1).
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `T` (a set of edges of `G`) is a spanning forest of the contracted graph `Ĝ_H`
(Definition 7.5). -/
def IsContractedSpanningForest (G H : SimpleGraph V) (T : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ T, ∃ u v, e = s(u, v) ∧ G.Adj u v ∧ u ∈ gD H ∧ v ∈ gD H ∧ ¬ SameDComp H u v) ∧
  (∀ u v, u ∈ gD H → v ∈ gD H → (restrictTo (G ⊔ H) (gD H)).Reachable u v →
    (restrictTo (addEdges H ↑T) (gD H)).Reachable u v) ∧
  (∀ e ∈ T, ∀ u v, e = s(u, v) →
    ¬ (restrictTo (addEdges H ↑(T.erase e)) (gD H)).Reachable u v)

/-- The weight of eq. (36) on the ordered pair `(u, v)`: `(ℓ_v − x_u)²` if `u ∈ D`,
`v ∈ A ∪ C` and `ℓ_v > x_u`, else `0` (decomposition and levels of `H`). -/
noncomputable def wDir (H : SimpleGraph V) (x : Sym2 V → ℝ) (u v : V) : ℝ := by
  classical
  exact if u ∈ gD H ∧ v ∈ gA H ∪ gC H ∧ load x u < level H x v then
    (level H x v - load x u) ^ 2 else 0

/-- The weight `w(e)` of eq. (36) (and of Lemma 7.4) on an unordered pair. -/
noncomputable def extWeight (H : SimpleGraph V) (x : Sym2 V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => wDir H x u v + wDir H x v u, fun _ _ => add_comm _ _⟩

/-- `q(uv) = (1 − x_u)²`, written symmetrically as `((1 − x_u)² + (1 − x_v)²)/2`. -/
noncomputable def qWeight (x : Sym2 V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => ((1 - load x u) ^ 2 + (1 - load x v) ^ 2) / 2,
    fun _ _ => by simp only [add_comm]⟩

/-- The components `Dᵢ` of `H[D]` with `E_G[Dᵢ, D \ Dᵢ] ≠ ∅`. -/
noncomputable def dCompsWithExit (G H : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (dComps H).filter (fun S => ∃ u ∈ S, ∃ v, v ∈ gD H ∧ v ∉ S ∧ G.Adj u v)

/-- Definition 7.12: the edge `e` of `G` violates `x` (decomposition and levels of `H`). -/
def IsViolating (G H : SimpleGraph V) (x : Sym2 V → ℝ) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ u v, e = s(u, v) ∧
    ((u ∈ gA H ∪ gC H ∧ v ∈ gD H ∧ load x v < level H x u) ∨
     (u ∈ gD H ∧ v ∈ gD H ∧ ¬ SameDComp H u v))

/-- `Σ_{e ∈ F(x)} z_e`: the mass of `z` on the edges of `G` that violate `x`. -/
noncomputable def violMass (G H : SimpleGraph V) (x z : Sym2 V → ℝ) : ℝ := by
  classical
  exact ∑ e, if IsViolating G H x e then z e else 0

end LoadBalMatch.Main


