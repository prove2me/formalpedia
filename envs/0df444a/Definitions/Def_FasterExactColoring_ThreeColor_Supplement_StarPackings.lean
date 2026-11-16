-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_StarPackings
-- name    : FasterExactColoring_ThreeColor_Supplement_StarPackings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:53.891214+00:00
-- url     : https://prove2.me/theorems/7c971e66-30aa-41c2-a7d1-688a1f9e56d1
-- title:
--   Two maximal star packings and computed terminal counts
-- statement:
--   A star consists of one center and three distinct adjacent leaves. Extra graph edges are permitted: these are copies of $K_{1,3}$ as subgraphs. The first packing is an inclusion-maximal list of pairwise vertex-disjoint stars in $G[S]$. Its vertex union is $S_{\star1}$. The second packing is inclusion-maximal among vertex-disjoint stars with centers in $U$ and leaves in $S\setminus S_{\star1}$. Write $U_{\star2}$ and $S_{\star2}$ for its center and leaf sets and $S'=S\setminus(S_{\star1}\cup S_{\star2})$.
--
--   $$s_{\star1}=|S_{\star1}|,\quad u_{\star2}=|U_{\star2}|,\quad s'=|S'|,\quad
--    a_i=\#\{K_3\text{ components with }i\text{ centers}\},\quad
--    b_i=\#\{K_4\text{ components with }i\text{ centers}\}.$$
--
--   All eleven coordinates $(s_{\star1},s',a_0,\ldots,a_3,b_0,\ldots,b_4)$ are computed from the instance and its supplied valid packings. Packings carry explicit vertex encodings. This interface supplies the structural data shared by the terminal algorithms; it does not assume the numerical identities or the degree consequences of maximality.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 5.2, Eq. (6), p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Restricted

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

/-- A K_1,3 subgraph; extra edges among its vertices are allowed. -/
structure Star (n : ℕ) where
  center : Fin n
  leaves : Finset (Fin n)

def Star.verts {n : ℕ} (s : Star n) : Finset (Fin n) := insert s.center s.leaves

def Star.valid {n : ℕ} (s : Star n) (G : GraphInput n) : Prop :=
  s.leaves.card = 3 ∧ s.center ∉ s.leaves ∧ ∀ v ∈ s.leaves, G.graph.Adj s.center v

def Star.code {n : ℕ} (s : Star n) : List ℕ := s.center.val :: vertexSetCode s.leaves

def packingVertices {n : ℕ} (L : List (Star n)) : Finset (Fin n) :=
  L.foldl (fun X s => X ∪ s.verts) ∅

def packingLeaves {n : ℕ} (L : List (Star n)) : Finset (Fin n) :=
  L.foldl (fun X s => X ∪ s.leaves) ∅

def packingCenters {n : ℕ} (L : List (Star n)) : Finset (Fin n) :=
  (L.map Star.center).toFinset

structure StarPackings (n : ℕ) where
  first : List (Star n)
  second : List (Star n)

def StarPackings.firstVertices {n : ℕ} (K : StarPackings n) := packingVertices K.first
def StarPackings.secondCenters {n : ℕ} (K : StarPackings n) := packingCenters K.second
def StarPackings.secondLeaves {n : ℕ} (K : StarPackings n) := packingLeaves K.second
def StarPackings.remainingS {n : ℕ} (K : StarPackings n) (P : Restricted n) :=
  P.S \ (K.firstVertices ∪ K.secondLeaves)

/-- Inclusion maximality, separately in the two admissible families of stars. -/
def StarPackings.valid {n : ℕ} (K : StarPackings n) (P : Restricted n) : Prop :=
  (∀ s ∈ K.first, s.valid P.G ∧ s.verts ⊆ P.S) ∧
  K.first.Pairwise (fun s t => Disjoint s.verts t.verts) ∧
  (∀ s : Star n, s.valid P.G → s.verts ⊆ P.S →
    ¬ Disjoint s.verts K.firstVertices) ∧
  (∀ s ∈ K.second, s.valid P.G ∧ s.center ∈ P.U ∧
    s.leaves ⊆ P.S \ K.firstVertices) ∧
  K.second.Pairwise (fun s t => Disjoint s.verts t.verts) ∧
  ∀ s : Star n, s.valid P.G → s.center ∈ P.U →
    s.leaves ⊆ P.S \ K.firstVertices →
    ¬ Disjoint s.verts (packingVertices K.second)

def StarPackings.code {n : ℕ} (K : StarPackings n) : List ℕ :=
  [K.first.length] ++ K.first.flatMap Star.code ++
    [K.second.length] ++ K.second.flatMap Star.code

def terminalCode {n : ℕ} (P : Restricted n) (K : StarPackings n) : List ℕ :=
  P.code ++ K.code

noncomputable def cliqueCount {n : ℕ} (P : Restricted n) (K : StarPackings n)
    (m i : ℕ) : ℕ :=
  ((P.cliques m).filter (fun C => (C ∩ K.secondCenters).card = i)).card

/-- Appendix E's parameter vector; all coordinates are computed cardinalities. -/
noncomputable def terminalParameters {n : ℕ} (P : Restricted n) (K : StarPackings n) :
    Fin 11 → ℝ :=
  ![(K.firstVertices.card : ℝ), (K.remainingS P).card,
    cliqueCount P K 3 0, cliqueCount P K 3 1, cliqueCount P K 3 2, cliqueCount P K 3 3,
    cliqueCount P K 4 0, cliqueCount P K 4 1, cliqueCount P K 4 2, cliqueCount P K 4 3,
    cliqueCount P K 4 4]

end FasterExactColoring.ThreeColor.Supplement


