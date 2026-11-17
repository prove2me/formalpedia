-- Prove2me | Definitions.Def_RevRedSAT_Supplement_ColInstance
-- name    : RevRedSAT_Supplement_ColInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:57:07.131204+00:00
-- url     : https://prove2.me/theorems/d8474195-4f50-4abe-8e47-2b790d4ecba4
-- title:
--   q-Coloring and List q-Coloring instances, and the minimum treedepth-$h$ modulator
-- statement:
--   Fix $q\ge2$. A **proper $q$-coloring** of a graph $G$ is a map $\alpha:V(G)\to[q]$ with $\alpha(u)\neq\alpha(v)$ for every edge $uv$; **q-Coloring** asks whether one exists. In **List q-Coloring** every vertex has a list $L(v)\subseteq[q]$ and the coloring must satisfy $\alpha(v)\in L(v)$ (App. C.2). The codes list $n$, the edges, and for the list version the lists of the vertices in vertex order.
--
--   For $h\ge1$, a **treedepth-$h$ modulator** is a set $X$ of vertices with $\mathrm{td}(G-X)\le h$, and
--
--   $$\mathrm{mod}_h(G)=\min\{|X| : \mathrm{td}(G-X)\le h\}$$
--
--   is the parameter $k$ of Theorem 1.4. The treedepth is the minimum height of an elimination forest, the height counting vertices on a root-to-leaf path, and the empty graph has treedepth $0$.
--
--   **Formalization Note** Colors are `Fin q`, a relabelling of $[q]$. The treedepth is the published `SNPTreedepth.treedepth`. Taking $X=V(G)$ shows that the minimum exists.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.2, p.93 (coloring, treedepth, modulators); Theorem 1.4, p.6

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_RevRedSAT_Supplement_IsEdgeListing

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **An instance of q-Coloring**: a graph on the vertices `0, …, n − 1`.
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.2, p.93: "Fix an integer q ≥ 2 and write [q] = {1, . . . , q}. A proper q-coloring of G is
a map α : V(G) → [q] such that α(u) ≠ α(v) whenever uv ∈ E(G). The q-Coloring problem asks whether
such a map exists. In List q-Coloring, each vertex also has a list L(v) ⊆ [q], and we require
α(v) ∈ L(v)." -/
structure ColInstance where
  /-- the number of vertices -/
  n : ℕ
  /-- the graph -/
  G : SimpleGraph (Fin n)

/-- The codes of a q-Coloring instance: `n`, then a listing of the edges (`IsEdgeListing`). -/
def IsColCode (I : ColInstance) (w : List Bool) : Prop :=
  ∃ E : List (Fin I.n × Fin I.n), IsEdgeListing I.G E ∧ w = encNat I.n ++ encList encEdge E

/-- `G` has a proper `q`-coloring (colors `Fin q`, i.e. `[q]` relabelled). -/
def Colorable (q : ℕ) (I : ColInstance) : Prop :=
  ∃ α : Fin I.n → Fin q, ∀ u v, I.G.Adj u v → α u ≠ α v

/-- **An instance of List q-Coloring**: a graph and a list `L(v) ⊆ [q]` for every vertex. -/
structure ListColInstance (q : ℕ) where
  /-- the number of vertices -/
  n : ℕ
  /-- the graph -/
  G : SimpleGraph (Fin n)
  /-- the list of admissible colors of each vertex -/
  L : Fin n → Finset (Fin q)

/-- The codes of a List q-Coloring instance: `n`, a listing of the edges, then the lists of the
vertices `0, …, n − 1` in vertex order, each without repetition and in any order. -/
def IsListColCode {q : ℕ} (I : ListColInstance q) (w : List Bool) : Prop :=
  ∃ E : List (Fin I.n × Fin I.n), IsEdgeListing I.G E ∧
    ∃ Ls : Fin I.n → List (Fin q), (∀ v, (Ls v).Nodup ∧ (Ls v).toFinset = I.L v) ∧
      w = encNat I.n ++ encList encEdge E ++ encList encSet (List.ofFn Ls)

/-- The instance has a proper `q`-coloring with `α(v) ∈ L(v)` for every vertex. -/
def ListColorable {q : ℕ} (I : ListColInstance q) : Prop :=
  ∃ α : Fin I.n → Fin q, (∀ v, α v ∈ I.L v) ∧ ∀ u v, I.G.Adj u v → α u ≠ α v

/-- **The minimum size of a treedepth-`h` modulator** (App. C.2, p.93: "a treedepth-d modulator is
a set X such that td(G − X) ≤ d. The coloring result in Corollary 7.5 uses
k = min{|X| : td(G − X) ≤ d}"; Theorem 1.4, p.6, with `h` for this `d`).

**Formalization Note** `td` is the published `SNPTreedepth.treedepth` (minimum height of a rooted
forest whose closure contains the graph, height counted in vertices, `0` for the empty graph),
which is App. C.2's elimination-forest treedepth. `G − X` is the subgraph induced on the
complement of `X`. `X = V(G)` is always a modulator, so the infimum is a minimum. -/
noncomputable def modNum (h : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ X : Finset (Fin n), X.card = k ∧
    SNPTreedepth.treedepth (G.induce ((Finset.univ \ X : Finset (Fin n)) : Set (Fin n))) ≤ h}

end RevRedSAT.Supplement


