-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Graph
-- name    : MultiplierAssoc206_Resolution_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:21.076018+00:00
-- url     : https://prove2.me/theorems/0350ff31-2433-45c8-b069-4ddc9ef9c2bc
-- title:
--   Bipartite graphs, the perfect-matching CNF $\mathsf{PM}(H)$, its star-local extension $\mathsf{SPM}(H)$, and boundary expanders
-- statement:
--   A bipartite graph $H=(U,V,E)$ has finite parts $U,V$ and edge set $E\subseteq U\times V$; an edge is written $e=(u_e,v_e)$. The **star** $E(w)$ of a vertex $w\in U\cup V$ is the set of edges incident to $w$, and its degree is $|E(w)|$. A **matching** is a set of pairwise disjoint edges; it covers a vertex set if every vertex of the set is an endpoint of one of its edges.
--
--   **Perfect-matching CNF (Definition 5.1).** With one variable $X_e$ per edge,
--   $$\mathsf{PM}(H)=\bigwedge_{w\in U\cup V}\mathrm{ExactOne}(X_{E(w)}),$$
--   where $\mathrm{ExactOne}(X_{E(w)})$ consists of the clause $\bigvee_{e\in E(w)}X_e$ and the clauses $\neg X_e\vee\neg X_f$ for $e\ne f$ in $E(w)$.
--
--   **Star-local extension (Definition 5.2).** For each vertex $w$ and each Boolean function $f:\{0,1\}^{E(w)}\to\{0,1\}$ there is an extension variable $Z_{w,f}$, defined by the clauses $\mathrm{Def}(Z_{w,f})$: for each assignment $\beta$ of the star, the clause $\bigvee_{e\in E(w)}(X_e\ne\beta_e)\vee(Z_{w,f}=f(\beta))$. Then
--   $$\mathsf{SPM}(H)=\bigwedge_{w\in U\cup V}\Big(\mathrm{ExactOne}(X_{E(w)})\wedge\bigwedge_{f:\{0,1\}^{E(w)}\to\{0,1\}}\mathrm{Def}(Z_{w,f})\Big).$$
--   Every clause has width at most $\Delta+1$ when every degree is at most $\Delta$.
--
--   **Boundary expander (Definition 5.3).** For $S\subseteq U$, the boundary $\delta(S)\subseteq V$ is the set of vertices of $V$ with exactly one neighbour in $S$; $H$ is an $(r,\Gamma)$-boundary expander if $|\delta(S)|\ge\Gamma|S|$ for every $S\subseteq U$ with $|S|\le r$.
--
--   When $|U|=m+1>|V|=m$, $\mathsf{PM}(H)$ and $\mathsf{SPM}(H)$ are unsatisfiable; $\mathsf{SPM}(H)$ is the source of hardness of the reduction.
--
--   **Formalization Note** Vertices of $U\cup V$ are elements of the disjoint union $U\oplus V$; $E\subseteq U\times V$ excludes parallel edges. The definition of $\mathrm{Def}(Z_{w,f})$ is the one-clause-per-assignment encoding, which realizes the width bound $\Delta+1$ stated on PDF p.9.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.8–9 (printed pp.7–8), §2 Bipartite graphs and matchings (PDF p.5), Definitions 5.1–5.3 (PDF pp.8–9)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

namespace MultiplierAssoc206.Resolution

open Classical

/-! # Bipartite graphs, the perfect-matching CNF and its star-local extension

Liew, *Associativity of Multiplication Is Hard for Resolution*, §2 "Bipartite graphs and
matchings" (PDF p. 5), Definitions 5.1–5.3 (PDF pp. 8–9). A bipartite graph `H = (U, V, E)`
is given by finite types `U`, `V` and an edge set `E ⊆ U × V` (no parallel edges); an edge `e`
is written `(u_e, v_e)`. Vertices of `U ∪ V` are elements of `U ⊕ V`. -/

variable {U V : Type} [Fintype U] [Fintype V]

/-- The edges of `E`, as a type. -/
abbrev Edge (E : Finset (U × V)) := {e : U × V // e ∈ E}

/-- The edge `e` is incident to the vertex `w`. -/
def Incident {E : Finset (U × V)} (w : U ⊕ V) (e : Edge E) : Prop :=
  match w with
  | Sum.inl u => e.1.1 = u
  | Sum.inr v => e.1.2 = v

/-- The star `E(w)`: the set of edges incident to the vertex `w`. -/
noncomputable def star (E : Finset (U × V)) (w : U ⊕ V) : Finset (Edge E) :=
  Finset.univ.filter fun e => Incident w e

/-- Every vertex has degree `|E(w)|` at most `Δ`. -/
def MaxDegLE (E : Finset (U × V)) (Δ : ℕ) : Prop := ∀ w : U ⊕ V, (star E w).card ≤ Δ

/-- No vertex is isolated: every star is nonempty. -/
def NoIsolated (E : Finset (U × V)) : Prop := ∀ w : U ⊕ V, (star E w).Nonempty

/-- `ExactOne(X_{E(w)})`: the clause `⋁_{e ∈ E(w)} X_e` and the clauses `¬X_e ∨ ¬X_f` for
`e ≠ f` in `E(w)`, over the edge variables. -/
noncomputable def exactOne (E : Finset (U × V)) (w : U ⊕ V) : CNF (Edge E) :=
  insert ((star E w).image fun e => (e, true))
    (((star E w ×ˢ star E w).filter fun p => p.1 ≠ p.2).image
      fun p => ({(p.1, false), (p.2, false)} : Clause (Edge E)))

/-- Definition 5.1: the exact-one perfect-matching CNF `PM(G) = ⋀_{w ∈ U ∪ V} ExactOne(X_{E(w)})`,
with one variable `X_e` per edge. -/
noncomputable def PM (E : Finset (U × V)) : CNF (Edge E) :=
  Finset.univ.biUnion fun w => exactOne E w

/-- The variables of `SPM(H)`: the edge variables `X_e` and one extension variable `Z_{w,f}`
for each vertex `w` and each Boolean function `f : {0,1}^{E(w)} → {0,1}`. -/
abbrev ExtVar (E : Finset (U × V)) :=
  Edge E ⊕ (Σ w : U ⊕ V, ({e // e ∈ star E w} → Bool) → Bool)

/-- The clause of `Def(Z_{w,f})` for the assignment `β` of the star: it is falsified exactly
when `X_{E(w)} = β` and `Z_{w,f} ≠ f(β)`. -/
noncomputable def defClause (E : Finset (U × V)) (w : U ⊕ V)
    (f : ({e // e ∈ star E w} → Bool) → Bool) (β : {e // e ∈ star E w} → Bool) :
    Clause (ExtVar E) :=
  insert (Sum.inr ⟨w, f⟩, f β) (Finset.univ.image fun e => (Sum.inl e.1, !β e))

/-- `Def(Z_{w,f})`: the clauses over `{Z_{w,f}} ∪ {X_e : e ∈ E(w)}` expressing
`Z_{w,f} = f((X_e)_{e ∈ E(w)})`, one clause per assignment of the star (width `|E(w)| + 1`). -/
noncomputable def defZ (E : Finset (U × V)) (w : U ⊕ V)
    (f : ({e // e ∈ star E w} → Bool) → Bool) : CNF (ExtVar E) :=
  Finset.univ.image (defClause E w f)

/-- Definition 5.2: the star-local extension
`SPM(H) = ⋀_{w ∈ U ∪ V} (ExactOne(X_{E(w)}) ∧ ⋀_{f : {0,1}^{E(w)} → {0,1}} Def(Z_{w,f}))`. -/
noncomputable def SPM (E : Finset (U × V)) : CNF (ExtVar E) :=
  Finset.univ.biUnion fun w =>
    (exactOne E w).rename Sum.inl ∪ Finset.univ.biUnion fun f => defZ E w f

/-- Definition 5.3: the boundary `δ(S) ⊆ V` of `S ⊆ U`, the vertices of `V` with exactly one
neighbour in `S`. -/
noncomputable def boundary (E : Finset (U × V)) (S : Finset U) : Finset V :=
  Finset.univ.filter fun v => (S.filter fun u => (u, v) ∈ E).card = 1

/-- Definition 5.3: `G` is an `(r, Γ)`-boundary expander if `|δ(S)| ≥ Γ |S|` for every
`S ⊆ U` with `|S| ≤ r`. -/
def IsBoundaryExpander (E : Finset (U × V)) (r Γ : ℝ) : Prop :=
  ∀ S : Finset U, (S.card : ℝ) ≤ r → Γ * S.card ≤ (boundary E S).card

/-- A matching: a set of pairwise disjoint edges. -/
def IsMatching (E M : Finset (U × V)) : Prop :=
  M ⊆ E ∧ ∀ e ∈ M, ∀ e' ∈ M, (e.1 = e'.1 ∨ e.2 = e'.2) → e = e'

/-- `H` has a matching covering `V`. -/
def HasMatchingCoveringV (E : Finset (U × V)) : Prop :=
  ∃ M, IsMatching E M ∧ ∀ v : V, ∃ e ∈ M, e.2 = v

end MultiplierAssoc206.Resolution


