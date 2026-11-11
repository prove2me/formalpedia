-- Prove2me | Definitions.Def_EuclidKSteiner_Layouts
-- name    : EuclidKSteiner_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:37.448718+00:00
-- url     : https://prove2.me/theorems/ce4d8cfe-5c15-4585-90ae-9bca89c57a4f
-- title:
--   Real-RAM input and output layouts for Lemmas 4.3, 4.4, Corollary 5.4 and Theorem 3.8
-- statement:
--   Machine layouts (lists of reals, counts first) for the algorithmic milestones:
--
--   1. **Lemma 4.3**: input $(b,k)$; output the number of templates, then their codes.
--   2. **Lemma 4.4**: input $|V|,|E|,b,k$, a terminal flag per vertex, each edge as $(u,v,w(uv))$, the template code and the images of its vertices; output the number of tree edges, then their endpoints.
--   3. **Corollary 5.4**: input $(n,s,r)$; output the number $N$ of strings, then each string as $n$ cells in $\{0,1\}$.
--   4. **Theorem 3.8**: input $n,r,p,|\mathcal A|$, the $n-1$ edges of $M$ as $(u,v,w(uv))$, then each pair of $\mathcal A$ as its $p$ elements and its weight; output the number of retained pairs, then their positions in the input list.
--
--   An edge listing lists each edge exactly once.
--
--   **Formalization Note** Vertices of an $n$-vertex graph are $0,\dots,n-1$. Outputs are read from the cell right after the input.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.3 p.16 (PDF p.18), Lemma 4.4 p.17 (PDF p.19), Corollary 5.4 p.23 (PDF p.25), Theorem 3.8 p.12 (PDF p.14); real-RAM model p.3 (PDF p.5)

import Mathlib
import Definitions.Def_EuclidKSteiner_Instance
import Definitions.Def_EuclidKSteiner_Template

namespace EuclidKSteiner

open Classical

/-!
# Machine input and output layouts for Lemma 4.4, Corollary 5.4 and Theorem 3.8

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.4 p.17 (PDF p.19), Corollary 5.4 p.23
(PDF p.25), Theorem 3.8 p.12 (PDF p.14). The machine is the real RAM of p.3 (PDF p.5).

**Formalization Note** Every layout is a list of reals read from cell `0`; counts come first, so a
program can read the rest with counting loops. Vertices of an `nV`-vertex graph are `Fin nV`,
written as their numbers. An edge list `Ls` lists each edge of `G` exactly once (`IsEdgeListing`).
Outputs are read from the cell right after the input (`OutputIs`).
-/

/-- `Ls` lists the edge set `E` without repetition (as ordered pairs of endpoints). -/
def IsEdgeListing {n : ℕ} (Ls : List (Fin n × Fin n)) (E : Finset (Sym2 (Fin n))) : Prop :=
  (Ls.map fun e => s(e.1, e.2)).Nodup ∧ (Ls.map fun e => s(e.1, e.2)).toFinset = E

/-- The edge set of a list of ordered pairs. -/
def edgesOf {n : ℕ} (Ls : List (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  (Ls.map fun e => s(e.1, e.2)).toFinset

/-- Three cells per edge: its endpoints and its weight. -/
noncomputable def edgeCells {n : ℕ} (w : Sym2 (Fin n) → ℝ) (Ls : List (Fin n × Fin n)) : List ℝ :=
  Ls.flatMap fun e => [((e.1 : ℕ) : ℝ), ((e.2 : ℕ) : ℝ), w s(e.1, e.2)]

/-- **Input of Lemma 4.4.** The reals `|V|, |E|, b, k`; the terminal flag of each vertex (`1` for a
terminal); each edge as `(u, v, w(uv))`; the template code (`Template.encode`); the images
`φ(0), …, φ(h − 1)` of the template vertices. The tree `M` is not part of the input. -/
noncomputable def realizationLayout {nV : ℕ} (S : GraphSetting (Fin nV))
    (Ls : List (Fin nV × Fin nV)) (b k : ℕ) (T : Template) (φ : ℕ → Fin nV) : List ℝ :=
  (nV : ℝ) :: (Ls.length : ℝ) :: (b : ℝ) :: (k : ℝ) ::
    ((List.finRange nV).map (fun v => if v ∈ S.P then (1 : ℝ) else 0) ++ edgeCells S.w Ls ++
      T.encode ++ (List.range T.size).map (fun j => (((φ j : Fin nV) : ℕ) : ℝ)))

/-- An output edge list: the number of edges, then the two endpoints of each. -/
noncomputable def encodeEdgeList {n : ℕ} (L : List (Fin n × Fin n)) : List ℝ :=
  (L.length : ℝ) :: L.flatMap fun e => [((e.1 : ℕ) : ℝ), ((e.2 : ℕ) : ℝ)]

/-- **Input of Corollary 5.4**: the reals `n, s, r`. -/
noncomputable def stringLayout (n s r : ℕ) : List ℝ := [(n : ℝ), (s : ℝ), (r : ℝ)]

/-- **Output of Corollary 5.4**: the number `N` of strings, then each string as `n` cells in
`{0, 1}`. -/
noncomputable def encodeStrings {n : ℕ} (X : List (Fin n → Bool)) : List ℝ :=
  (X.length : ℝ) :: X.flatMap fun x => (List.finRange n).map fun i => if x i then (1 : ℝ) else 0

/-- **Input of Theorem 3.8.** The reals `n, r, p, |𝒜|`; the `n − 1` edges of the tree `M` on
`{0, …, n − 1}` as `(u, v, w(uv))`; each pair of the family as its `p` elements, then its weight. -/
noncomputable def repLayout {n : ℕ} (w : Sym2 (Fin n) → ℝ) (Ls : List (Fin n × Fin n)) (r p : ℕ)
    (fam : List (List (Fin n) × ℝ)) : List ℝ :=
  (n : ℝ) :: (r : ℝ) :: (p : ℝ) :: (fam.length : ℝ) ::
    (edgeCells w Ls ++ fam.flatMap fun a => a.1.map (fun i => ((i : ℕ) : ℝ)) ++ [a.2])

/-- The weighted family listed by `fam`: the pairs `(A, w)` with `A` the set of listed elements. -/
def famSet {n : ℕ} (fam : List (List (Fin n) × ℝ)) : Set (Finset (Fin n) × ℝ) :=
  {x | ∃ a ∈ fam, x = (a.1.toFinset, a.2)}

/-- The subfamily at the positions `L` of `fam`. -/
def famAt {n : ℕ} (fam : List (List (Fin n) × ℝ)) (L : List ℕ) : Set (Finset (Fin n) × ℝ) :=
  {x | ∃ j ∈ L, ∃ a, fam[j]? = some a ∧ x = (a.1.toFinset, a.2)}

/-- **Output of Theorem 3.8**: the number `m` of retained positions, then the positions
(0-based) into the input list of pairs. -/
noncomputable def encodePositions (L : List ℕ) : List ℝ :=
  (L.length : ℝ) :: L.map fun j => (j : ℝ)

/-- **Input of Lemma 4.3**: the reals `b, k`. -/
noncomputable def boundsLayout (b k : ℕ) : List ℝ := [(b : ℝ), (k : ℝ)]

end EuclidKSteiner


