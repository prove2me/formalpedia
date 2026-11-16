-- Prove2me | Definitions.Def_MetricMSO_Supplement_Interpretation
-- name    : MetricMSO_Supplement_Interpretation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:56:46.41821+00:00
-- url     : https://prove2.me/theorems/ee370461-7efd-4dfc-8337-920e524175a3
-- title:
--   Monadic lifts, interpretations and monadic $L$-dependence
-- statement:
--   A **graph class** $\mathcal C$ is any set of finite graphs; no closure assumption is made. A parameter is **bounded** on $\mathcal C$ if one constant bounds it on every member. The **component diameter** $D(G)$ is the maximum diameter of a connected component of $G$. $\mathcal C$ is **hereditary** if it is closed under induced subgraphs (up to isomorphism).
--
--   A **monadic lift** of $G$ adds a fixed number of unary predicates with freely chosen extensions: on vertices for the adjacency logics ($\mathrm{MSO}_1$ variants), on vertices and edges for the incidence logics ($\mathrm{MSO}_2$ variants). An **$L$-interpretation** is a domain formula $\nu(x)$ and an adjacency formula $\eta(x,y)$ in $L$; its output on a lifted structure has the elements satisfying $\nu$ as vertices (each output vertex is one input element: no copies or tuples) and the edges $ab$ with $a\ne b$ satisfying $\eta(a,b)$. For incidence logics, elements are the vertices and edges of $G$, so $\nu$ is a pair and $\eta$ a quadruple of formulas, one per sort combination. Metric atoms are always evaluated in $G$.
--
--   $\mathcal C$ is **monadically $L$-dependent** (Definition 7.1) if no fixed $L$-interpretation produces every finite graph, up to isomorphism, from monadic lifts of members of $\mathcal C$.
--
--   **Formalization Note** The output adjacency is the symmetrization $a\ne b\wedge\eta(a,b)\wedge\eta(b,a)$; it equals $\eta$ when $\eta$ is symmetric and irreflexive, as the paper requires, and is definable in the same logic, so the class of interpretations is the paper's. "Every finite graph" includes the graph with no vertex.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), §1, p.10 (PDF 12); §7.1, Definition 7.1, p.43 (PDF 45); §7.3, p.45 (PDF 47)

import Mathlib
import Definitions.Def_MetricMSO_Supplement_XSat

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO

/-- **A graph class**: a set of finite graphs, given as a predicate on graphs `SimpleGraph (Fin n)`
for every `n`. No closure assumption ("Our equivalence holds for arbitrary graph classes, without
closure assumptions", p.11 (PDF 13)). -/
abbrev GraphClass : Type := (n : ℕ) → SimpleGraph (Fin n) → Prop

/-- The class `C` has **bounded** parameter `par`: one constant bounds `par(G)` on every member. -/
def BoundedOn (par : (n : ℕ) → SimpleGraph (Fin n) → ℕ) (C : GraphClass) : Prop :=
  ∃ k : ℕ, ∀ n (G : SimpleGraph (Fin n)), C n G → par n G ≤ k

/-- **Component diameter** `D(G)` (§7.3, p.45 (PDF 47)): "Write D(G) for the maximum diameter of a
connected component of G": the largest distance between two vertices in the same component (`0`
for the graph with no vertex). -/
noncomputable def compDiam {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {d : ℕ | ∃ u v : Fin n, G.Reachable u v ∧ G.dist u v = d}

/-- A **hereditary** class (closed under induced subgraphs, up to isomorphism): every graph with an
induced embedding (`↪g`) into a member is a member. -/
def Hereditary (C : GraphClass) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), C n G →
    ∀ m (H : SimpleGraph (Fin m)), Nonempty (H ↪g G) → C m H

/-- **A monadic lift of the adjacency structure** of `G` (§1, p.10; §7.1, p.43 (PDF 45)): `G`
expanded by `q` unary predicates on vertices with freely chosen extensions `P`, and no edge
predicate ("For the variations of MSO1 we use adjacency structures and vertex colors"). -/
def adjLift {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (P : Fin q → Finset (Fin n)) : Instance :=
  ⟨n, G, q, P, 0, fun j => j.elim0, fun j => j.elim0⟩

/-- **The output graph of an interpretation on an adjacency structure** (§1, p.10 (PDF 12); §7.1,
p.43 (PDF 45)): "a domain formula ν(x), keeping all vertices that satisfy ν in the output, and an
adjacency formula η(x, y), defining all the edges uv that satisfy η(u, v)". Each output vertex is
one input vertex ("We use transductions in which each output vertex is one input element, so we do
not use copies or tuples").

The vertices are the `a` with `I ⊨ ν(a)` (`ν` read with `a` as the vertex variable of level `0`);
`a ≠ b` are adjacent iff `I ⊨ η(a, b)` and `I ⊨ η(b, a)` (`a`, `b` the levels `0`, `1`).

**Formalization Note** The paper requires `η` to be symmetric and irreflexive; the output relation
here is the symmetrization `a ≠ b ∧ η(a, b) ∧ η(b, a)`, which equals `η` when `η` is symmetric and
irreflexive and is itself defined by a formula of the same logic, so the class of interpretations
is the paper's. Metric atoms are evaluated in the input graph `G` (`XSat`), "even when the domain
formula selects only some of its vertices" (p.43). No numerical parameter symbol is used. -/
def adjOutput (I : Instance) (ν η : XFormula) :
    SimpleGraph {a : Fin I.n // XSat I [] ⟨[a], [], [], []⟩ ν} where
  Adj a b := a ≠ b ∧ XSat I [] ⟨[a.1, b.1], [], [], []⟩ η ∧ XSat I [] ⟨[b.1, a.1], [], [], []⟩ η
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- **Monadic `L`-dependence of a class on adjacency structures** (Definition 7.1, p.43 (PDF 45)):
"A graph class C is monadically L-dependent if there is no fixed L-interpretation that produces
every finite graph, up to isomorphism, from monadic lifts of members of C in the appropriate
encoding."

There are no fixed number `q` of unary predicates and fixed formulas `ν, η ∈ L` such that every
finite graph `H` (every `m` and every `H` on `Fin m`) is isomorphic to the output of `(ν, η)` on
some monadic lift with `q` predicates of some member of `C`. -/
def MonDepAdj (L : XFormula → Prop) (C : GraphClass) : Prop :=
  ¬ ∃ (q : ℕ) (ν η : XFormula), L ν ∧ L η ∧
    ∀ (m : ℕ) (H : SimpleGraph (Fin m)), ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
      ∃ P : Fin q → Finset (Fin n), Nonempty (adjOutput (adjLift G q P) ν η ≃g H)

/-- An element of the incidence structure `I(G)`: a vertex or an edge. -/
abbrev IncElem (I : Instance) : Type := Fin I.n ⊕ I.G.edgeSet

/-- **An interpretation on incidence structures** (§7.1, p.43): output vertices may be vertex
elements or edge elements of `I(G)`. The domain formula is a pair (`νV` with one free vertex
variable, `νE` with one free edge variable), the adjacency formula a quadruple for the four sort
combinations of `(x, y)`: `ηVV` (vertex variables of levels `0, 1`), `ηVE` (`x` the vertex variable
of level `0`, `y` the edge variable of level `0`), `ηEV` (`x` the edge variable of level `0`, `y`
the vertex variable of level `0`), `ηEE` (edge variables of levels `0, 1`). -/
structure IncInterp where
  νV : XFormula
  νE : XFormula
  ηVV : XFormula
  ηVE : XFormula
  ηEV : XFormula
  ηEE : XFormula

/-- All six formulas of an incidence interpretation belong to `L`. -/
def IncInterp.In (Φ : IncInterp) (L : XFormula → Prop) : Prop :=
  L Φ.νV ∧ L Φ.νE ∧ L Φ.ηVV ∧ L Φ.ηVE ∧ L Φ.ηEV ∧ L Φ.ηEE

/-- The domain formula of an incidence interpretation at an element. -/
def incDom (I : Instance) (Φ : IncInterp) : IncElem I → Prop
  | .inl a => XSat I [] ⟨[a], [], [], []⟩ Φ.νV
  | .inr e => XSat I [] ⟨[], [e.1], [], []⟩ Φ.νE

/-- The adjacency formula of an incidence interpretation at an ordered pair of elements. -/
def incRel (I : Instance) (Φ : IncInterp) : IncElem I → IncElem I → Prop
  | .inl a, .inl b => XSat I [] ⟨[a, b], [], [], []⟩ Φ.ηVV
  | .inl a, .inr e => XSat I [] ⟨[a], [e.1], [], []⟩ Φ.ηVE
  | .inr e, .inl b => XSat I [] ⟨[b], [e.1], [], []⟩ Φ.ηEV
  | .inr e, .inr f => XSat I [] ⟨[], [e.1, f.1], [], []⟩ Φ.ηEE

/-- **The output graph of an incidence interpretation**: the elements `x` of `I(G)` satisfying the
domain formula, `x ≠ y` adjacent iff the adjacency formula holds for `(x, y)` and for `(y, x)`
(symmetrization, as in `adjOutput`). Metric atoms are evaluated in `G` ("Note that also in the
incidence encoding of a graph we evaluate the metric atoms in the original input graph", p.10). -/
def incOutput (I : Instance) (Φ : IncInterp) : SimpleGraph {x : IncElem I // incDom I Φ x} where
  Adj x y := x ≠ y ∧ incRel I Φ x.1 y.1 ∧ incRel I Φ y.1 x.1
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- **Monadic `L`-dependence on incidence structures** (Definition 7.1; §1, p.10: "for the
variations of MSO2 we work with incidence structures and hence may color vertices and edges"): no
fixed numbers `q, q'` of unary predicates on vertices and on edges and fixed incidence
interpretation with formulas in `L` produce every finite graph, up to isomorphism, from monadic
lifts of the incidence structures of members of `C`. -/
def MonDepInc (L : XFormula → Prop) (C : GraphClass) : Prop :=
  ¬ ∃ (q q' : ℕ) (Φ : IncInterp), Φ.In L ∧
    ∀ (m : ℕ) (H : SimpleGraph (Fin m)), ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
      ∃ (P : Fin q → Finset (Fin n)) (Q : Fin q' → Finset (Sym2 (Fin n)))
        (hQ : ∀ j, ∀ e ∈ Q j, e ∈ G.edgeSet),
        Nonempty (incOutput ⟨n, G, q, P, q', Q, hQ⟩ Φ ≃g H)

end MetricMSO.Supplement


