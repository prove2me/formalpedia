-- Prove2me | Definitions.Def_TermCycDich_Supplement_RailedAnnulus
-- name    : TermCycDich_Supplement_RailedAnnulus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:48:52.852724+00:00
-- url     : https://prove2.me/theorems/5317bdf3-881e-4c4e-804c-ecf58ea558a8
-- title:
--   Railed annuli: separating, $S$-calm, trimming and combed $R$-cycles
-- statement:
--   Let $w,r\ge2$. A **$(w,r)$-railed annulus** $A_{w,r}$ is the union of pairwise vertex-disjoint cycles $C_1,\dots,C_w$ (the **circles**) and pairwise vertex-disjoint paths $R_1,\dots,R_r$ (the **rails**) such that (i) the union is planar, (ii) each $R_i$ has one end on $C_1$, the other on $C_w$, and is otherwise disjoint from $C_1\cup C_w$, (iii) every $R_i\cap C_j$ is a path, and (iv) traversed from its end on $C_1$, $R_i$ visits $C_1,\dots,C_w$ in this order.
--
--   Let $\rho$ be a $\Sigma$-rendition of $G-A$. A railed annulus $H\subseteq G-A$ is **separating** in $\rho$ with **domain** $\circledcirc$ if $H$ is grounded, $\circledcirc\subseteq\Sigma$ is an annulus whose boundary components are the traces of $C_1$ and $C_w$ and which contains the trace of every grounded subpath of a rail, $\circledcirc$ avoids the closures of the vortices, and the trace of every circle is a separating curve. The **crop** by $\circledcirc$ is the union of the $\sigma(c)$ over the cells $c\subseteq\circledcirc$. For an $R$-cycle $S$, $H$ is **$S$-calm** if this crop contains no red vertex (blank) and is disjoint from $N_S(A\cap V(S))$.
--
--   For $p\ge0$, $q\ge2$ the **$p$-trimming** of $A_{2p+q,r}$ keeps the circles $C_{p+1},\dots,C_{p+q}$ and the minimal $C_{p+1}$-$C_{p+q}$-subpaths of the rails. An $R$-cycle is **combed** in $H$ if, inside the crop by the domain after deleting the vertices of the two boundary circles, it coincides with a union of rails; it **uses at most $q$ rails** if $q$ rails suffice.
--
--   These are the objects of the annulus combing lemma, Theorem 5.2.
--
--   **Formalization Note** The circles and rails are given as data, rails oriented from $C_1$. An annulus is the image of an injective continuous map of $\{z\in\mathbb C:1\le|z|\le2\}$, its boundary components the images of the two circles. A curve is separating if removing it disconnects the component of $\Sigma$ containing it. Planarity is the public `RobertsonSeymour1986.GM5.IsPlanar` of the union.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §5 "A partially embedded railed annulus" and "Combed R-cycles", p.34 (PDF 36)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_TermCycDich_Supplement_Village

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Railed annuli: separating, domain, blank, `S`-calm, trimming, combed `R`-cycles

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §5 "A partially embedded railed annulus" and "Combed R-cycles",
p.34 (PDF 36).

* `RailData w r`: circles `C₁, …, C_w` (subgraphs) and rails `R₁, …, R_r` (paths).
  `IsRailedAnnulus K H` (`w, r ≥ 2`): pairwise vertex-disjoint cycles and pairwise vertex-disjoint
  paths in `K`, (i) their union is planar (the public `RobertsonSeymour1986.GM5.IsPlanar` of the
  union as a graph on its vertex set), (ii) `Rᵢ` runs from `C₁` to `C_w` and is otherwise disjoint
  from `C₁ ∪ C_w`, (iii) every `Rᵢ ∩ Cⱼ` is a path, (iv) traversed from its end on `C₁`, `Rᵢ`
  visits `C₁, …, C_w` in this order. The rails are stored oriented from `C₁`.
* `IsSeparatingWith ρ H O` (`ρ` a `Σ`-rendition of `G − A`): (i) `H` is grounded, (ii) `O` is a
  closed annulus whose two boundary circles are traces of `C₁` and `C_w`, and every grounded
  subpath of a rail has a trace in `O`, (iii) `O` is disjoint from the closures of the vortices,
  (iv) every circle has a trace that is a separating curve. `O` is the domain of `H`.
* `IsCalm ρ R A S O`: the crop by `O` (the union of the `σ(c)` with `c ⊆ O`) contains no vertex of
  `R` (blank) and is disjoint from `N_S(A ∩ V(S))`.
* `IsTrimming H p H'` (`q ≥ 2`, `a = 2p + q`): the circles of `H'` are `C_{p+1}, …, C_{p+q}` and its
  rails the minimal `C_{p+1}`-`C_{p+q}`-subpaths of the rails of `H`.
* `CombedUsing ρ O H' S I`: within the crop by `O` minus the vertices of the two boundary circles
  of `H'`, `S` coincides with the union of the rails indexed by `I`.

**Formalization Note** The closed annulus is the image of an injective continuous map of
`{z ∈ ℂ : 1 ≤ |z| ≤ 2}`; its boundary components are the images of the two circles. A curve `T` is
separating if removing it disconnects the connected component of `Σ` containing it (on a connected
surface: `Σ − T` is disconnected). Indices are `0`-based (`C₁` is circle `0`).
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- The closed annulus `{z ∈ ℂ : 1 ≤ |z| ≤ 2}`. -/
abbrev annulusSet : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

/-- `O` is a closed annulus in `X` with boundary circles `T₁` and `T₂`. -/
def IsAnnulusWith (O T₁ T₂ : Set X) : Prop :=
  ∃ e : C(annulusSet, X), Function.Injective e ∧ Set.range e = O ∧
    e '' {z | ‖(z : ℂ)‖ = 1} = T₁ ∧ e '' {z | ‖(z : ℂ)‖ = 2} = T₂

/-- `T` is a separating curve: removing it disconnects the component of `X` containing it. -/
def IsSeparatingCurve (T : Set X) : Prop :=
  ∃ x ∈ T, ¬ IsConnected (connectedComponent x \ T)

/-- Candidate data of a `(w, r)`-railed annulus: circles and (oriented) rails. -/
structure RailData (G : SimpleGraph V) (w r : ℕ) where
  /-- the circles `C₁, …, C_w` -/
  circ : Fin w → G.Subgraph
  /-- the rails `R₁, …, R_r` -/
  rail : Fin r → GPath G

namespace RailData

variable {w r : ℕ} (H : RailData G w r)

/-- The circle with (`0`-based) index `n`, or `⊥` out of range. -/
def circAt (n : ℕ) : G.Subgraph := if h : n < w then H.circ ⟨n, h⟩ else ⊥

/-- The railed annulus as a subgraph. -/
def sub : G.Subgraph := (⨆ i, H.circ i) ⊔ ⨆ i, (H.rail i).sub

end RailData

/-- `H` is a `(w, r)`-railed annulus inside `K` (p.34). -/
def IsRailedAnnulus {w r : ℕ} (K : G.Subgraph) (H : RailData G w r) : Prop :=
  2 ≤ w ∧ 2 ≤ r ∧
  (∀ j, IsCycleSub (H.circ j) ∧ H.circ j ≤ K) ∧
  Pairwise (fun j j' => Disjoint (H.circ j).verts (H.circ j').verts) ∧
  (∀ i, (H.rail i).sub ≤ K) ∧
  Pairwise (fun i i' => Disjoint (H.rail i).verts (H.rail i').verts) ∧
  RobertsonSeymour1986.GM5.IsPlanar H.sub.coe ∧
  (∀ i, (H.rail i).s ∈ (H.circAt 0).verts ∧ (H.rail i).t ∈ (H.circAt (w - 1)).verts ∧
    (H.rail i).InternallyDisjoint ((H.circAt 0).verts ∪ (H.circAt (w - 1)).verts)) ∧
  (∀ i j, IsPathSub ((H.rail i).sub ⊓ H.circ j)) ∧
  ∀ i (j j' : Fin w), j < j' → ∀ x ∈ (H.rail i).verts, x ∈ (H.circ j).verts →
    ∀ y ∈ (H.rail i).verts, y ∈ (H.circ j').verts → (H.rail i).pos x < (H.rail i).pos y

namespace Rendition

variable {H₀ : G.Subgraph} (ρ : Rendition X H₀)

/-- The railed annulus `H` is separating in `ρ` with domain `O` (p.34). -/
def IsSeparatingWith {w r : ℕ} (H : RailData G w r) (O : Set X) : Prop :=
  ρ.GroundedSub H.sub ∧
  (∃ T₁ T₂, ρ.IsTraceCycle (H.circAt 0) T₁ ∧ ρ.IsTraceCycle (H.circAt (w - 1)) T₂ ∧
    IsAnnulusWith O T₁ T₂) ∧
  (∀ i, ∀ P : GPath G, P.sub ≤ (H.rail i).sub → ρ.GroundedPath P →
    ∃ γ, ρ.IsTracePath P γ ∧ γ ⊆ O) ∧
  (∀ c ∈ ρ.vortices, Disjoint O (closure c)) ∧
  ∀ j, ∃ T, ρ.IsTraceCycle (H.circ j) T ∧ IsSeparatingCurve T

/-- A separating railed annulus with domain `O` is `S`-calm for the annotated graph `(G, R)` and the
apex set `A`: the crop by `O` contains no vertex of `R` and no vertex of `N_S(A ∩ V(S))`. -/
def IsCalm (R : Set V) (A : Set V) {u : V} (S : G.Walk u u) (O : Set X) : Prop :=
  Disjoint (ρ.cropUnion O).verts R ∧
    Disjoint (ρ.cropUnion O).verts (nbrOn S (A ∩ {v | v ∈ S.support}))

/-- Within the crop by `O` minus the vertices of the boundary circles of `H`, the closed walk `S`
coincides with the union of the rails indexed by `I`. -/
def CombedUsing {q r : ℕ} (O : Set X) (H : RailData G q r) {u : V} (S : G.Walk u u)
    (I : Finset (Fin r)) : Prop :=
  let K := (ρ.cropUnion O).deleteVerts ((H.circAt 0).verts ∪ (H.circAt (q - 1)).verts)
  S.toSubgraph ⊓ K = (⨆ i ∈ I, (H.rail i).sub) ⊓ K

end Rendition

/-- `H'` is the `p`-trimming of the railed annulus `H = A_{a,r}` with `a = 2p + q`, `q ≥ 2`. -/
def IsTrimming {a q r : ℕ} (H : RailData G a r) (p : ℕ) (H' : RailData G q r) : Prop :=
  2 ≤ q ∧ a = 2 * p + q ∧ (∀ j : Fin q, H'.circ j = H.circAt (p + j)) ∧
    ∀ i, (H'.rail i).sub ≤ (H.rail i).sub ∧ (H'.rail i).s ∈ (H.circAt p).verts ∧
      (H'.rail i).t ∈ (H.circAt (p + q - 1)).verts ∧
      (H'.rail i).InternallyDisjoint ((H.circAt p).verts ∪ (H.circAt (p + q - 1)).verts)

end Supplement

end TermCycDich


