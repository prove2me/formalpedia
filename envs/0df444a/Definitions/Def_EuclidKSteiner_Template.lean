-- Prove2me | Definitions.Def_EuclidKSteiner_Template
-- name    : EuclidKSteiner_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:53.025911+00:00
-- url     : https://prove2.me/theorems/d69488db-a7b4-4b93-bdb6-6bbac3013ba6
-- title:
--   Augmented tree templates (Definition 4.2), realizations, the families $D[u,i,v]$ and the recurrence (4.3)–(4.4)
-- statement:
--   **Definition 4.2.** For bounds $b,k$, an **augmented tree template** is a rooted tree with a left-to-right order on the children of each vertex, each vertex having a terminal or a candidate role; an edge between two terminal-role vertices is **virtual**, every other edge is a **Steiner** edge, and
--   1. there are at most $2b$ vertices and at least one vertex of each role;
--   2. at most $k$ vertices have a candidate role;
--   3. every terminal-role vertex has a candidate-role neighbor;
--   4. there are at most $b$ Steiner edges.
--
--   A **realization** of a template in the graph setting is a map $\varphi$ from template vertices to $V$ with (i) terminal roles to $P$ and candidate roles to $Q$; (ii) distinct terminal-role vertices have distinct images (candidate images may repeat); (iii) adjacent vertices have distinct images; (iv) every Steiner edge $xy$ has $\varphi(x)\varphi(y)\in E(G)$ with weight $w(\varphi(x)\varphi(y))$; (v) every virtual edge $xy$ has weight $\ell(\varphi(x),\varphi(y))$. The **cost** is the sum of these weights.
--
--   For a vertex $u$ with children $u_1,\dots,u_{\mathrm{child}(u)}$, the **partial template** $T_{u,i}$ consists of $u$ and the subtrees of $u_1,\dots,u_i$. The **full table entry** $D[u,i,v]$ is the set of pairs $(A,w)$ ($A$ the terminal images, $w$ the cost) of realizations of $T_{u,i}$ mapping $u$ to $v$. The **recurrence** is
--   $$D[u,0,v]=\begin{cases}\{(\{v\},0)\}&u\text{ terminal},\\ \{(\emptyset,0)\}&u\text{ candidate},\end{cases}\qquad(4.3)$$
--   (empty if $v$ does not fit the role of $u$), and
--   $$D[u,i,v]=\bigcup_{\substack{v'\ne v\\ v'\text{ fits }u_i}}\{(A\cup A',w+w'+w_{uu_i}(v,v')):(A,w)\in D[u,i-1,v],\,(A',w')\in D[u_i,\mathrm{child}(u_i),v'],\,A\cap A'=\emptyset\},\qquad(4.4)$$
--   where $w_{uu_i}(v,v')$ is $\ell(v,v')$ for a virtual edge and $w(vv')$ for a Steiner edge (which requires $vv'\in E(G)$).
--
--   **Formalization Note** A template is stored as its depth-first parenthesis word and its list of roles; vertices are numbered in preorder and children are ordered by their numbers. Parenthesis codes are in bijection with rooted ordered trees, so equal codes are exactly isomorphic templates (preserving root, child orders and roles). The recurrence is evaluated with a fuel argument equal to the number of vertices. The machine code of a template is its word length, its letters, then its roles.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §4.2–4.4, Definition 4.2 p.16 (PDF p.18), pp.16–18 (PDF pp.18–20), (4.3), (4.4)

import Mathlib
import Definitions.Def_EuclidKSteiner_GraphSetting

namespace EuclidKSteiner

open Classical

/-!
# Augmented tree templates, realizations, the dynamic-programming families D[u, i, v] and the
recurrence (4.3)–(4.4)

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §4.2–4.4, pp.16–18 (PDF pp.18–20).

**Formalization Note**
* A template is stored as its depth-first **parenthesis word** (`true` = opening, `false` =
  closing; a balanced word with `h − 1` opening letters encodes a rooted tree with a left-to-right
  child order on `h` vertices, as in the proof of Lemma 4.3) and a list of `h` roles. Vertices are
  `0, …, h − 1` in depth-first preorder, `0` is the root, and the children of a vertex are ordered by
  their numbers. Balanced words are in bijection with rooted ordered trees, so two templates are
  isomorphic (preserving root, child orders and roles) exactly when their codes are equal; a set of
  codes is a set of templates "up to isomorphism".
* The edges of a template are the pairs `(par j, j)` for `1 ≤ j < h`; an edge is *virtual* when both
  endpoints have the terminal role, otherwise it is a *Steiner* edge (Definition 4.2).
* A realization is a map `φ : ℕ → V`; only its values on the vertices concerned matter.
* The partial template `T_{u,i}` consists of `u` and the complete subtrees of its first `i` children.
* Families are sets of pairs `(A, w)` (`A` the set of terminal images, `w` the cost), as in §2.1.
* The recurrence is evaluated with a fuel argument equal to the number of vertices, which is at
  least the depth of the template plus one, so the fuel never runs out on a well-formed template.
-/

/-- The role of a template vertex. -/
inductive Role
  | terminal
  | candidate
  deriving DecidableEq

/-- An augmented tree template, by its code: the depth-first parenthesis word of the underlying
rooted ordered tree and the role of each vertex in preorder. -/
structure Template where
  /-- Depth-first parenthesis word: `true` = down an edge, `false` = back up. -/
  word : List Bool
  /-- The role of vertex `j` (preorder numbering). -/
  roles : List Role

namespace Template

/-- A balanced parenthesis word. -/
def Balanced (w : List Bool) : Prop :=
  w.count true = w.count false ∧ ∀ n, (w.take n).count false ≤ (w.take n).count true

/-- Number of vertices `h` (one more than the number of opening letters). -/
def size (T : Template) : ℕ := T.word.count true + 1

/-- A well-formed code: balanced word, one role per vertex. -/
def WellFormed (T : Template) : Prop := Balanced T.word ∧ T.roles.length = T.size

/-- Parents of the vertices `1, 2, …` produced by a depth-first scan with a stack. -/
def parentsAux : List Bool → List ℕ → ℕ → List ℕ
  | [], _, _ => []
  | true :: w, st, nxt => st.headD 0 :: parentsAux w (nxt :: st) (nxt + 1)
  | false :: w, st, nxt => parentsAux w st.tail nxt

/-- The parent of vertex `j ≥ 1` (and `0` for the root). -/
def par (T : Template) (j : ℕ) : ℕ :=
  if j = 0 then 0 else (parentsAux T.word [0] 1).getD (j - 1) 0

/-- The role of vertex `j`. -/
def role (T : Template) (j : ℕ) : Role := T.roles.getD j Role.terminal

/-- The edge `(par j, j)` is **virtual**: both endpoints have the terminal role. Every other edge is a
Steiner edge. Source: Definition 4.2, p.16 (PDF p.18). -/
def IsVirtual (T : Template) (j : ℕ) : Prop :=
  T.role (T.par j) = Role.terminal ∧ T.role j = Role.terminal

/-- `x` and `y` are adjacent in the template. -/
def Adj (T : Template) (x y : ℕ) : Prop :=
  (0 < y ∧ y < T.size ∧ T.par y = x) ∨ (0 < x ∧ x < T.size ∧ T.par x = y)

/-- **Definition 4.2 (augmented tree template) for the bounds `b, k`.** A well-formed code such that
1. there are at most `2b` vertices and at least one vertex of each role;
2. at most `k` vertices have a candidate role;
3. every terminal-role vertex has a candidate-role neighbor;
4. there are at most `b` Steiner edges.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, STOC 2027 submission (manuscript sha256 75361687…),
Definition 4.2, p.16 (PDF p.18). -/
def IsTemplateFor (b k : ℕ) (T : Template) : Prop :=
  T.WellFormed ∧
  (T.size ≤ 2 * b ∧ (∃ j < T.size, T.role j = Role.terminal) ∧
    (∃ j < T.size, T.role j = Role.candidate)) ∧
  ((Finset.range T.size).filter (fun j => T.role j = Role.candidate)).card ≤ k ∧
  (∀ j < T.size, T.role j = Role.terminal →
    ∃ i < T.size, T.role i = Role.candidate ∧ T.Adj i j) ∧
  ((Finset.Ico 1 T.size).filter (fun j => ¬ T.IsVirtual j)).card ≤ b

/-- The children `u_1, …, u_child(u)` of `u`, left to right. -/
def children (T : Template) (u : ℕ) : List ℕ :=
  (List.range T.size).filter (fun j => decide (0 < j ∧ T.par j = u))

/-- `child(u)`, the number of children of `u`. -/
def nch (T : Template) (u : ℕ) : ℕ := (T.children u).length

/-- `j` is in the subtree rooted at `u`. -/
def InSubtree (T : Template) (u j : ℕ) : Prop := j < T.size ∧ ∃ n : ℕ, (T.par)^[n] j = u

/-- The vertex set of the partial template `T_{u,i}`: `u` and the subtrees of its first `i`
children. Source: §4.3, p.17 (PDF p.19). -/
noncomputable def partialVerts (T : Template) (u i : ℕ) : Finset ℕ :=
  (Finset.range T.size).filter
    (fun j => j = u ∨ ∃ c ∈ (T.children u).take i, T.InSubtree c j)

/-- The edges of `T_{u,i}`, each named by its child endpoint `j` (the edge is `(par j, j)`). -/
noncomputable def partialEdges (T : Template) (u i : ℕ) : Finset ℕ :=
  (T.partialVerts u i).filter (fun j => j ≠ u)

/-- The number of terminal roles among the vertices `U`. -/
noncomputable def termCount (T : Template) (U : Finset ℕ) : ℕ :=
  (U.filter (fun j => T.role j = Role.terminal)).card

/-- The number `r` of terminal roles of the whole template. -/
noncomputable def numTerminals (T : Template) : ℕ := T.termCount (Finset.range T.size)

/-- The code of a template on the machine: the word length, the letters (`1` = opening,
`0` = closing), then the roles (`0` = terminal, `1` = candidate). -/
noncomputable def encode (T : Template) : List ℝ :=
  (T.word.length : ℝ) :: (T.word.map fun c => if c then (1 : ℝ) else 0) ++
    T.roles.map fun r => if r = Role.terminal then (0 : ℝ) else 1

/-- A list of templates on the machine: their number, then their codes. -/
noncomputable def encodeList (Ts : List Template) : List ℝ :=
  (Ts.length : ℝ) :: Ts.flatMap encode

end Template

namespace GraphSetting

variable {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V)

/-- The realization conditions (i)–(iv) of §4.2 on the template vertices `Vs` and the template edges
`Es` (edges named by their child endpoint): roles; terminal injectivity; distinct adjacent images;
Steiner edges map to edges of `G`. Candidate images may repeat. Condition (v) (virtual edges carry
`ℓ`, their images need not be adjacent) is in the cost.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §4.2, p.16 (PDF p.18), and §4.3 p.17 for partial
templates. -/
def RealizesOn (T : Template) (Vs Es : Finset ℕ) (φ : ℕ → V) : Prop :=
  (∀ j ∈ Vs, (T.role j = Role.terminal → φ j ∈ S.P) ∧ (T.role j = Role.candidate → φ j ∉ S.P)) ∧
  (∀ j ∈ Vs, ∀ j' ∈ Vs, T.role j = Role.terminal → T.role j' = Role.terminal → j ≠ j' →
    φ j ≠ φ j') ∧
  (∀ j ∈ Es, φ (T.par j) ≠ φ j) ∧
  (∀ j ∈ Es, ¬ T.IsVirtual j → s(φ (T.par j), φ j) ∈ S.E)

/-- The realized weight of the template edge `(par j, j)`: `ℓ` of the images for a virtual edge,
`w` of the image edge for a Steiner edge. -/
noncomputable def edgeCost (T : Template) (φ : ℕ → V) (j : ℕ) : ℝ :=
  if T.IsVirtual j then S.ell (φ (T.par j)) (φ j) else S.w s(φ (T.par j), φ j)

/-- The set of terminal images of the vertices `Vs`. -/
noncomputable def termImages {W : Type*} [DecidableEq W] (T : Template) (Vs : Finset ℕ) (φ : ℕ → W) :
    Finset W :=
  (Vs.filter (fun j => T.role j = Role.terminal)).image φ

/-- The set of candidate images of the vertices `Vs`. -/
noncomputable def candImages {W : Type*} [DecidableEq W] (T : Template) (Vs : Finset ℕ) (φ : ℕ → W) :
    Finset W :=
  (Vs.filter (fun j => T.role j = Role.candidate)).image φ

/-- A **realization** of the template `T`: conditions (i)–(iv) on all vertices and edges.
Source: §4.2, p.16 (PDF p.18). -/
def IsRealization (T : Template) (φ : ℕ → V) : Prop :=
  S.RealizesOn T (Finset.range T.size) (Finset.Ico 1 T.size) φ

/-- The **cost** `w` of a realization: the sum of the realized weights of all template edges.
Source: §4.2, p.17 (PDF p.19). -/
noncomputable def realCost (T : Template) (φ : ℕ → V) : ℝ :=
  ∑ j ∈ Finset.Ico 1 T.size, S.edgeCost T φ j

/-- **The full table entry `D[u, i, v]`**: all pairs `(A, w)` arising from realizations of `T_{u,i}`
whose root `u` is mapped to `v`; `A` is the set of terminal images and `w` the realization cost.
Source: §4.3, p.17 (PDF p.19). -/
def Dfull (T : Template) (u i : ℕ) (v : V) : Set (Finset V × ℝ) :=
  {x | ∃ φ : ℕ → V, S.RealizesOn T (T.partialVerts u i) (T.partialEdges u i) φ ∧ φ u = v ∧
    x = (termImages T (T.partialVerts u i) φ, ∑ j ∈ T.partialEdges u i, S.edgeCost T φ j)}

/-- The host `v'` fits the role of the template vertex `c`. -/
def Fits (T : Template) (c : ℕ) (v' : V) : Prop :=
  (T.role c = Role.terminal ∧ v' ∈ S.P) ∨ (T.role c = Role.candidate ∧ v' ∉ S.P)

/-- The prescribed weight `w_{uu_i}(v, v')` of the joining edge to the child `c = u_i`: `ℓ(v, v')`
if it is virtual, `w(vv')` if it is Steiner. -/
noncomputable def joinWeight (T : Template) (c : ℕ) (v v' : V) : ℝ :=
  if T.IsVirtual c then S.ell v v' else S.w s(v, v')

/-- The hosts allowed for the child `c` when its parent is at `v`: `v' ≠ v`, `v'` fits the role of
`c`, and if the joining edge is Steiner then `vv' ∈ E(G)`. -/
def JoinOK (T : Template) (c : ℕ) (v v' : V) : Prop :=
  v' ≠ v ∧ S.Fits T c v' ∧ (T.IsVirtual c ∨ s(v, v') ∈ S.E)

/-- **The transition of (4.4)** applied to the families `D₁` (for `T_{u,i−1}` at `v`) and `D₂ v'`
(for the full subtree of the child `c = u_i` at `v'`):
`⋃_{v'} {(A ∪ A', w + w' + w_{uu_i}(v, v')) : (A, w) ∈ D₁, (A', w') ∈ D₂ v', A ∩ A' = ∅}`, the
union over the allowed hosts `v'`. Source: (4.4), p.18 (PDF p.20); Corollary 4.7, p.19. -/
def transition (T : Template) (c : ℕ) (D₁ : Set (Finset V × ℝ)) (D₂ : V → Set (Finset V × ℝ))
    (v : V) : Set (Finset V × ℝ) :=
  {x | ∃ v', S.JoinOK T c v v' ∧ ∃ a ∈ D₁, ∃ b ∈ D₂ v', Disjoint a.1 b.1 ∧
    x = (a.1 ∪ b.1, a.2 + b.2 + S.joinWeight T c v v')}

/-- **The base entries (4.3)**: `{({v}, 0)}` for a terminal role, `{(∅, 0)}` for a candidate role,
and empty when `v` does not fit the role of `u`. Source: (4.3), p.18 (PDF p.20). -/
def Dbase (T : Template) (u : ℕ) (v : V) : Set (Finset V × ℝ) :=
  if S.Fits T u v then
    (if T.role u = Role.terminal then {({v}, 0)} else {(∅, 0)})
  else ∅

/-- The recurrence (4.3)–(4.4) with fuel `f`. -/
def DrecF (T : Template) : ℕ → ℕ → ℕ → V → Set (Finset V × ℝ)
  | 0, _, _, _ => ∅
  | _ + 1, u, 0, v => S.Dbase T u v
  | f + 1, u, i + 1, v =>
    match (T.children u)[i]? with
    | some c => transition S T c (DrecF T (f + 1) u i v) (fun v' => DrecF T f c (T.nch c) v') v
    | none => ∅
termination_by f _ i _ => (f, i)

/-- **The families computed by (4.3)–(4.4)**, with fuel the number of template vertices. -/
def Drec (T : Template) (u i : ℕ) (v : V) : Set (Finset V × ℝ) :=
  S.DrecF T T.size u i v

end GraphSetting

end EuclidKSteiner


