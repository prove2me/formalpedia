-- Prove2me | Definitions.Def_CoDecompFO_Supplement_StarStrat
-- name    : CoDecompFO_Supplement_StarStrat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:48:03.916652+00:00
-- url     : https://prove2.me/theorems/ea8c9304-4e37-4597-a80a-633432566554
-- title:
--   Tree-shaped diagrams, cones and limits; the co-decomposition $\mathcal T_*S$ of projected strategies
-- statement:
--   Let $\mathcal T=(T,\{G_a\},\{g^e_t\})$ be a tree co-decomposition with limit $\lim\mathcal T$ and projections $\pi_a:\lim\mathcal T\to G_a$, with $\pi_e=g^e_t\circ\pi_t$.
--
--   1. A **diagram of the shape of $T$** in a category $\mathcal C$ is an object $D_a$ for each node and edge $a$ and an arrow $D_t\to D_e$ for each node $t$ and incident edge $e$ (a diagram indexed by the barycentric subdivision of $T$, footnote 1). Legs $\nu_a:Y\to D_a$ form a **cone** if they commute with these arrows; a cone is a **limit** if every cone factors through it by a unique arrow (Prop. 2.12).
--
--   2. For $\beta:[k]\to\lim\mathcal T$ and an $m$-strategy $S$ on $(\lim\mathcal T,\beta)$, the diagram $\mathcal T_*S$ in the total category of strategies has at $a$ the object $(G_a,\pi_a\beta,\pi_{a*}S)$ and, for $t\in e$, the arrow $(g^e_t,g^e_{t*})$, whose second component is the canonical isomorphism $g^e_{t*}(\pi_{t*}S)\cong\pi_{e*}S$. The legs $(\pi_a,\mathrm{id}):(\lim\mathcal T,\beta,S)\to(G_a,\pi_a\beta,\pi_{a*}S)$ are also defined.
--
--   These are the objects of Theorem 5.70.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), footnote 1, p.3; Prop. 2.12, p.8; Theorem 5.70, p.36 (PDF pp.5, 10, 38)

import Mathlib
import Definitions.Def_CoDecompFO_Lim
import Definitions.Def_CoDecompFO_Supplement_StratTotal

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory FirstOrder

variable {σ : Sig}

/-- A **co-decomposition-shaped diagram** in a category `C` over the auxiliary tree of `T` (Bumpus et al.,
arXiv:2611.04658, held file sha256 d550d7af…, footnote 1, p.3: "A co-decomposition in a category C is a structured
decomposition in C^op"; ¶1.6, p.2): an object for each node and for each edge of the tree, and for each edge `e`
and each of its two endpoints `t` an arrow from the object at `t` to the object at `e`. This is a diagram indexed
by the barycentric subdivision of the tree (nodes and edges, with an incidence arrow `t → e`), which has no
composable pair of non-identity arrows, so a diagram is exactly this data. -/
structure TreeDiagram (T : CoDecomp σ) (C : Type 1) [Category.{0} C] : Type 1 where
  /-- The object at each node. -/
  node : Fin T.b → C
  /-- The object at each edge. -/
  edge : Fin T.m → C
  /-- The arrow from the first endpoint of `e` to `e`. -/
  left : ∀ e, node (T.ends e).1 ⟶ edge e
  /-- The arrow from the second endpoint of `e` to `e`. -/
  right : ∀ e, node (T.ends e).2 ⟶ edge e

variable {T : CoDecomp σ} {C : Type 1} [Category.{0} C]

/-- Legs `ν_a : Y → D_a` form a **cone** over `D` (¶2.9–2.10, pp.7–8): they commute with every incidence arrow. -/
def TreeDiagram.IsCone (D : TreeDiagram T C) (Y : C) (νn : ∀ t, Y ⟶ D.node t) (νe : ∀ e, Y ⟶ D.edge e) :
    Prop :=
  ∀ e, νn (T.ends e).1 ≫ D.left e = νe e ∧ νn (T.ends e).2 ≫ D.right e = νe e

/-- A cone is a **limit** of `D` (Proposition 2.12, p.8: "universal among cones"): for every cone `(Z, μ)` there
is a unique arrow `Z → Y` commuting with the legs. -/
def TreeDiagram.IsLimit (D : TreeDiagram T C) (Y : C) (νn : ∀ t, Y ⟶ D.node t) (νe : ∀ e, Y ⟶ D.edge e) :
    Prop :=
  D.IsCone Y νn νe ∧ ∀ (Z : C) (μn : ∀ t, Z ⟶ D.node t) (μe : ∀ e, Z ⟶ D.edge e), D.IsCone Z μn μe →
    ∃! u : Z ⟶ Y, (∀ t, u ≫ νn t = μn t) ∧ ∀ e, u ≫ νe e = μe e

/-- The projection `π_t : lim T → G_t` to a bag. -/
def limProj (T : CoDecomp σ) (t : Fin T.b) (x : T.Lim) : Fin (T.bag t).n := x.val t

theorem limProj_isHom (T : CoDecomp σ) (t : Fin T.b) : IsHom σ (limProj T t) :=
  fun _ _ h => h t

theorem edgeProj_isHom (T : CoDecomp σ) (e : Fin T.m) : IsHom σ (CoDecomp.Lim.edgeProj (T := T) e) :=
  fun i _ h => T.gl_hom e i _ (h (T.ends e).1)

/-- The position `(lim T, β)`. -/
def limPos (T : CoDecomp σ) {k : ℕ} (β : Fin k → T.Lim) : Pos σ k := ⟨T.Lim, β⟩

/-- The position `(G_t, π_t ∘ β)` of a bag. -/
def nodePos (T : CoDecomp σ) {k : ℕ} (β : Fin k → T.Lim) (t : Fin T.b) : Pos σ k :=
  ⟨Fin (T.bag t).n, limProj T t ∘ β⟩

/-- The position `(G_e, π_e ∘ β)` of an adhesion. -/
def edgePos (T : CoDecomp σ) {k : ℕ} (β : Fin k → T.Lim) (e : Fin T.m) : Pos σ k :=
  ⟨Fin (T.adh e).n, CoDecomp.Lim.edgeProj e ∘ β⟩

/-- **The co-decomposition `T ∗ S`** (Theorem 5.70, p.36): at each node `t` the object `(G_t, π_t β, π_{t*} S)` and
at each edge `e` the object `(G_e, π_e β, π_{e*} S)` of the total category of strategies, and for each node `t` and
incident edge `e` the induced morphism of strategies `(g^e_t, g^e_{t*})`: the map `g^e_t` of positions with the
canonical coherence isomorphism `g^e_{t*}(π_{t*} S) ≅ π_{e*} S` along `π_e = g^e_t ∘ π_t` (`StratObj.pushComp`).

**Formalization Note** The theorem prints "π_{a*}S ∈ Strat_m(lim T, π_a ∘ β)"; the projection lives in
`Strat_m(G_a, π_a ∘ β)`, as the same sentence says ("the projection of S to (G_a, π_a ∘ β)"). -/
def starDiagram (T : CoDecomp σ) (m : ℕ) {k : ℕ} (β : Fin k → T.Lim) (S : StratObj T.Lim m) :
    TreeDiagram T (StratTot σ m k) where
  node t := ⟨nodePos T β t, StratObj.push (limProj T t) m S⟩
  edge e := ⟨edgePos T β e, StratObj.push (CoDecomp.Lim.edgeProj e) m S⟩
  left e := ⟨⟨T.gl e, T.gl_hom e, rfl⟩,
    StratObj.pushComp (limProj T (T.ends e).1) (T.gl e) (CoDecomp.Lim.edgeProj e) (fun _ => rfl) m S⟩
  right e := ⟨⟨T.gr e, T.gr_hom e, funext fun j => ((β j).compat e).symm⟩,
    StratObj.pushComp (limProj T (T.ends e).2) (T.gr e) (CoDecomp.Lim.edgeProj e)
      (fun x => (x.compat e).symm) m S⟩

/-- The object `(lim T, β, S)` of the total category of strategies. -/
def limStrat (T : CoDecomp σ) (m : ℕ) {k : ℕ} (β : Fin k → T.Lim) (S : StratObj T.Lim m) : StratTot σ m k :=
  ⟨limPos T β, S⟩

/-- The leg `(π_t, 𝟙) : (lim T, β, S) → (G_t, π_t β, π_{t*} S)` (proof of Theorem 5.70, p.36). -/
def starNodeLeg (T : CoDecomp σ) (m : ℕ) {k : ℕ} (β : Fin k → T.Lim) (S : StratObj T.Lim m) (t : Fin T.b) :
    limStrat T m β S ⟶ (starDiagram T m β S).node t :=
  ⟨⟨limProj T t, limProj_isHom T t, rfl⟩, StratObj.pushHom (limProj T t) m S⟩

/-- The leg `(π_e, 𝟙) : (lim T, β, S) → (G_e, π_e β, π_{e*} S)` (proof of Theorem 5.70, p.36). -/
def starEdgeLeg (T : CoDecomp σ) (m : ℕ) {k : ℕ} (β : Fin k → T.Lim) (S : StratObj T.Lim m) (e : Fin T.m) :
    limStrat T m β S ⟶ (starDiagram T m β S).edge e :=
  ⟨⟨CoDecomp.Lim.edgeProj e, edgeProj_isHom T e, rfl⟩, StratObj.pushHom (CoDecomp.Lim.edgeProj e) m S⟩

end Supplement

end CoDecompFO


