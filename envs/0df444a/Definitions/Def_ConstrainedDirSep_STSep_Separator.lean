-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_Separator
-- name    : ConstrainedDirSep_STSep_Separator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:04:56.844014+00:00
-- url     : https://prove2.me/theorems/06934530-0721-4fdb-96cb-4343e9b53336
-- title:
--   Loopless digraphs, s–t vertex separators, hereditary classes and feasible separators
-- statement:
--   A **digraph** $D$ on the vertex set $\{0,\dots,n-1\}$ is an adjacency relation (Mathlib's `Digraph (Fin n)`): there are no parallel arcs, and both $uv$ and $vu$ may be arcs. It is **loopless** if no $vv$ is an arc.
--
--   For vertices $s, t$ and a vertex set $S$, $D-S$ keeps the arcs of $D$ with neither end in $S$. $S$ is an **$s$–$t$ vertex separator** if $s, t \notin S$ and $D - S$ contains no directed walk (equivalently, no directed path) from $s$ to $t$. It is **inclusion-minimal** if no proper subset is an $s$–$t$ vertex separator.
--
--   A **class of digraphs** $\mathcal H$ is given by its members on each vertex set $\{0,\dots,m-1\}$. It is **closed under isomorphism** if relabelling a member by a permutation gives a member. $D[S] \in \mathcal H$ means: the subdigraph of $D$ induced by the finite set $S$, relabelled to $\{0,\dots,|S|-1\}$ by some bijection, lies in $\mathcal H$. The class is **hereditary** if $F[X] \in \mathcal H$ for every member $F$ and every $X \subseteq V(F)$; taking $X=\emptyset$, a nonempty hereditary class contains the null digraph.
--
--   A **feasible $s$–$t$ separator** (with budget $k$) is an $s$–$t$ vertex separator $S$ with $|S| \le k$ and $D[S]\in\mathcal H$. For nonnegative integer weights $w$, $w(S)=\sum_{v\in S} w(v)$.
--
--   **Formalization Note.** Walks replace paths, as the paper allows (§3). A class is a predicate `(m : ℕ) → Digraph (Fin m) → Prop`; the paper's classes consist of loopless digraphs, and nothing in the mission asks a class about a digraph with a loop.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 2 (PDF 5), §1.1.1; pp. 13–14 (PDF 16–17), §3; p. 27 (PDF 30), §5.2.2

import Mathlib

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **Loopless digraph.** Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027
submission (manuscript sha256 4dd06c29…), §3, p. 13 (PDF 16): "All input digraphs are finite and
have neither loops nor parallel arcs, but may contain both arcs uv and vu."

**Formalization Note.** A digraph is Mathlib's `Digraph V` (an adjacency relation, so there are no
parallel arcs and both `uv` and `vu` may be present); looplessness is this predicate. -/
def Loopless {V : Type*} (D : Digraph V) : Prop :=
  ∀ v : V, ¬ D.Adj v v

/-- **An arc of `D − S`.** §3, p. 14 (PDF 17): `D − S` is `D` with the vertices of `S` deleted;
`avoidStep D S u v` says that `uv` is an arc of `D` with neither end in `S`. -/
def avoidStep {V : Type*} (D : Digraph V) (S : Set V) (u v : V) : Prop :=
  D.Adj u v ∧ u ∉ S ∧ v ∉ S

/-- **s–t vertex separator.** §1.1.1, p. 2 (PDF 5) and §3, p. 14 (PDF 17): "For distinct vertices
s, t of a digraph D, an s–t vertex separator is a set S ⊆ V(D) \ {s, t} such that D − S contains no
directed path from s to t."

**Formalization Note.** "No directed path from `s` to `t` in `D − S`" is the negation of the
reflexive–transitive closure of `avoidStep D S` (a directed walk; the paper uses walks and paths
interchangeably, §3, p. 13). Distinctness of `s` and `t` is a hypothesis of every statement that
uses this notion. -/
def IsSTSeparator {V : Type*} (D : Digraph V) (s t : V) (S : Set V) : Prop :=
  s ∉ S ∧ t ∉ S ∧ ¬ Relation.ReflTransGen (avoidStep D S) s t

/-- **Inclusion-minimal s–t vertex separator.** §3, p. 14 (PDF 17): "Either object is
inclusion-minimal if none of its proper subsets has the same separation property." -/
def IsMinimalSTSeparator {V : Type*} (D : Digraph V) (s t : V) (S : Set V) : Prop :=
  IsSTSeparator D s t S ∧ ∀ S' : Set V, S' ⊂ S → ¬ IsSTSeparator D s t S'

/-- **A class of finite digraphs.** §3, p. 14 (PDF 17). A class is given by its members on each
vertex set `Fin m`: `H m F` says that the digraph `F` on `{0, …, m-1}` belongs to the class.

**Formalization Note.** Isomorphism-closure is the separate predicate `IsoClosed`; the class of
the paper consists of loopless digraphs, and nothing here or downstream ever asks the class about a
digraph with a loop. -/
def DigraphClass : Type := (m : ℕ) → Digraph (Fin m) → Prop

/-- **Closed under isomorphism.** §3, p. 14 (PDF 17): "Classes are closed under isomorphism."
If `σ` is an isomorphism from `F` onto `F'` (both on `Fin m`) and `F ∈ H`, then `F' ∈ H`. -/
def IsoClosed (H : DigraphClass) : Prop :=
  ∀ (m : ℕ) (F F' : Digraph (Fin m)) (σ : Equiv.Perm (Fin m)),
    (∀ a b : Fin m, F'.Adj (σ a) (σ b) ↔ F.Adj a b) → H m F → H m F'

/-- **The induced subdigraph `D[S]` belongs to `H`.** §1.1.1, p. 2 (PDF 5): `D[S]` is the
subdigraph induced by `S`; it is a digraph on `|S|` vertices, relabelled to `Fin |S|` by some
bijection `e`.

**Formalization Note.** Existence of one labelling `e : Fin |S| ≃ S` with the relabelled digraph
in `H`; for an isomorphism-closed `H` this is equivalent to "every labelling". -/
def InducedMem (H : DigraphClass) {V : Type*} (D : Digraph V) (S : Finset V) : Prop :=
  ∃ e : Fin S.card ≃ {x // x ∈ S}, H S.card ⟨fun a b => D.Adj (e a : V) (e b : V)⟩

/-- **Hereditary class.** §3, p. 14 (PDF 17): "A class H of digraphs is hereditary if H[X] ∈ H
for every H ∈ H and every X ⊆ V(H)." In particular (X = ∅) a nonempty hereditary class contains
the null digraph. -/
def Hereditary (H : DigraphClass) : Prop :=
  ∀ (m : ℕ) (F : Digraph (Fin m)) (X : Finset (Fin m)), H m F → InducedMem H F X

/-- **Feasible s–t separator.** §1.1.1, p. 2 (PDF 5), problem *H-Directed s–t Separator*: an s–t
vertex separator `S` with `|S| ≤ k` and `D[S] ∈ H`. -/
def IsFeasible (H : DigraphClass) {V : Type*} (D : Digraph V) (s t : V) (k : ℕ)
    (S : Finset V) : Prop :=
  IsSTSeparator D s t (S : Set V) ∧ S.card ≤ k ∧ InducedMem H D S

/-- **Weight of a vertex set.** §5.2.2, p. 27 (PDF 30): `w(S) = ∑_{v ∈ S} w(v)` for nonnegative
integer vertex weights `w`. -/
def wsum {V : Type*} (w : V → ℕ) (S : Finset V) : ℕ :=
  ∑ v ∈ S, w v

end ConstrainedDirSep.STSep


