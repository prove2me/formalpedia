-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Restricted
-- name    : FasterExactColoring_ThreeColor_Supplement_Restricted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:22.415143+00:00
-- url     : https://prove2.me/theorems/70be1a32-602e-4133-b9ba-6ea033c33e71
-- title:
--   Restricted 4-coloring instances and finite encodings
-- statement:
--   Let $G$ be a finite simple undirected graph with vertices $0,\ldots,n-1$. A restricted instance is $P=(G,I,S)$, with disjoint vertex sets $I,S$, where $I$ is independent and every neighbor of $I$ belongs to $S$. Put $U=V(G)\setminus(I\cup S)$. A valid coloring is a proper four-coloring assigning color $4$ on $I$ and one of colors $1,2,3$ on $S$; vertices of $U$ may use all four colors.
--
--   $$P\text{ is terminal}\quad\Longleftrightarrow\quad\text{every component of }G[U]\text{ is }K_3\text{ or }K_4.$$
--
--   The component sets, numbers $n_{K_3},n_{K_4}$, initial instance $(G,\varnothing,\varnothing)$, and children $(G,I_j,S_j)$ are computed from this data. The graph and both subsets have explicit finite encodings. These objects support every Section 5 algorithm without imposing terminality on the headline theorems.
--
--   **Formalization Note** The published graph model is reused. Colors are numbered $0,1,2,3$ in Lean, so the distinguished color is $3$. Connected components are the distinct bounded flood-fill sets starting at vertices of $U$; the empty set contributes no component. The original graph and its vertex order are retained by every child.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 5.1, pp. 9–10 (PDF pp. 11–12)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_GraphInput

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

/-- Section 5.1: the graph is retained throughout the branching tree. -/
structure Restricted (n : ℕ) where
  G : GraphInput n
  I : Finset (Fin n)
  S : Finset (Fin n)

def Restricted.U {n : ℕ} (P : Restricted n) : Finset (Fin n) :=
  vertices \ (P.I ∪ P.S)

def Restricted.valid {n : ℕ} (P : Restricted n) : Prop :=
  Disjoint P.I P.S ∧
  (∀ u ∈ P.I, ∀ v ∈ P.I, ¬ P.G.graph.Adj u v) ∧
  ∀ u ∈ P.I, ∀ v, P.G.graph.Adj u v → v ∈ P.S

def Restricted.colorable {n : ℕ} (P : Restricted n) : Prop :=
  ∃ f : Fin n → Fin 4, properColoring P.G f ∧
    (∀ v ∈ P.I, f v = 3) ∧ (∀ v ∈ P.S, (f v).val < 3)

def Restricted.code {n : ℕ} (P : Restricted n) : List ℕ :=
  graphCode P.G ++ vertexSetCode P.I ++ vertexSetCode P.S

def initial {n : ℕ} (G : GraphInput n) : Restricted n := ⟨G, ∅, ∅⟩

def clique {n : ℕ} (G : GraphInput n) (C : Finset (Fin n)) (m : ℕ) : Prop :=
  C.card = m ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.graph.Adj u v

def Restricted.components {n : ℕ} (P : Restricted n) : Finset (Finset (Fin n)) :=
  P.U.image (component P.G P.U)

noncomputable def Restricted.cliques {n : ℕ} (P : Restricted n) (m : ℕ) :
    Finset (Finset (Fin n)) := by
  classical
  exact P.components.filter (fun C => clique P.G C m)

noncomputable def Restricted.nClique {n : ℕ} (P : Restricted n) (m : ℕ) : ℕ :=
  (P.cliques m).card

def Restricted.terminal {n : ℕ} (P : Restricted n) : Prop :=
  ∀ C ∈ P.components, clique P.G C 3 ∨ clique P.G C 4

/-- Children are changes of I,S on exactly the same graph. -/
def child {n : ℕ} (P : Restricted n) (IS : Finset (Fin n) × Finset (Fin n)) :
    Restricted n := ⟨P.G, IS.1, IS.2⟩

def childrenCode {n : ℕ} (L : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  L.length :: L.flatMap (fun IS => vertexSetCode IS.1 ++ vertexSetCode IS.2)

end FasterExactColoring.ThreeColor.Supplement


