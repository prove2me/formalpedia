-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_Assumption1
-- name    : SparseCCE_ThreePlayer_Assumption1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:23.561188+00:00
-- url     : https://prove2.me/theorems/fe1b4e80-acad-4b71-887f-f5261c7ad879
-- title:
--   Bipartite polymatrix games and Assumption 1 (PCP-for-PPAD)
-- statement:
--   A **bipartite polymatrix game** with two actions per vertex has left vertices $\mathrm{Fin}\,a$, right vertices $\mathrm{Fin}\,b$, a list $E$ of distinct edges $(v,w)$, and on each edge a two-player game with payoffs $PL_e(c,d)$ to $v$ and $PR_e(c,d)$ to $w$. Instances have maximum degree three and edge payoffs in $[0,1]$. Each vertex picks one mixed action used in all its incident games; its utility is one third of the sum of its utilities in these games, and its **regret** is its best pure utility minus its utility.
--
--   `PolymatrixWeakNE ε δ` asks for a rational mixed profile in which at most $\delta(a+b)$ vertices have regret greater than $\varepsilon$ ("all but a $\delta$ fraction of the vertices have regret at most $\varepsilon$").
--
--   **Assumption 1** is the proposition: there are $\varepsilon^*,\delta^*\in(0,1)$ such that `PolymatrixWeakNE ε* δ*` is PPAD-hard (`CEPolytopeHard.PPADHard`). It is never asserted; it only appears as a hypothesis.
--
--   The input code contains one vertex marker per vertex, including isolated vertices, in addition to binary counts and the edge/payoff list. Thus this is an explicit graph encoding: the input length is at least the number of vertices.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §2.4, Assumption 1, p. 14.

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- A bipartite polymatrix game with two actions per vertex (§2.4, p. 14): left vertices
`Fin a`, right vertices `Fin b`, the edge list `E` (pairs `(left, right)`), and on each edge a
two-player game with payoffs `PL e c d` to the left vertex and `PR e c d` to the right vertex
when the left vertex plays `c` and the right vertex plays `d`. -/
structure BipartitePolymatrix where
  a : ℕ
  b : ℕ
  E : List (Fin a × Fin b)
  PL : Fin a × Fin b → Fin 2 → Fin 2 → ℚ
  PR : Fin a × Fin b → Fin 2 → Fin 2 → ℚ

namespace BipartitePolymatrix

variable (P : BipartitePolymatrix)

/-- Admissible instances: no repeated edge, maximum degree three, edge payoffs in `[0, 1]`. -/
def Valid : Prop :=
  P.E.Nodup ∧ (∀ v, (P.E.filter (fun e => e.1 = v)).length ≤ 3) ∧
    (∀ w, (P.E.filter (fun e => e.2 = w)).length ≤ 3) ∧
    ∀ e ∈ P.E, ∀ c d, 0 ≤ P.PL e c d ∧ P.PL e c d ≤ 1 ∧ 0 ≤ P.PR e c d ∧ P.PR e c d ≤ 1

/-- The binary code of the game: `a`, `b`, the number of edges, then for each edge its two
endpoints and the eight rational payoffs. A vertex marker for each vertex makes the graph
explicit even when it has isolated vertices. -/
def code : List Bool :=
  QAlgorithms.LocalHamiltonian.encBin P.a ++ QAlgorithms.LocalHamiltonian.encBin P.b ++
    List.replicate (P.a + P.b) false ++ QAlgorithms.LocalHamiltonian.encBin P.E.length ++
    P.E.flatMap (fun e =>
      QAlgorithms.LocalHamiltonian.encBin e.1 ++ QAlgorithms.LocalHamiltonian.encBin e.2 ++
        (List.finRange 2).flatMap (fun c => (List.finRange 2).flatMap (fun d =>
          QAlgorithms.LocalHamiltonian.encRat (P.PL e c d) ++
            QAlgorithms.LocalHamiltonian.encRat (P.PR e c d))))

/-- Utility of left vertex `v` playing `c` against the mixed actions `xR` of the right vertices:
one third of the sum of its utilities in its incident edge games. -/
def utilL (xR : Fin P.b → Fin 2 → ℝ) (v : Fin P.a) (c : Fin 2) : ℝ :=
  (1 / 3) * ((P.E.filter (fun e => e.1 = v)).map
    (fun e => ∑ d, xR e.2 d * (P.PL e c d : ℝ))).sum

/-- Utility of right vertex `w` playing `d` against the mixed actions `xL` of the left vertices. -/
def utilR (xL : Fin P.a → Fin 2 → ℝ) (w : Fin P.b) (d : Fin 2) : ℝ :=
  (1 / 3) * ((P.E.filter (fun e => e.2 = w)).map
    (fun e => ∑ c, xL e.1 c * (P.PR e c d : ℝ))).sum

/-- Regret of left vertex `v`: best pure utility minus its utility under its mixed action. -/
def regretL (xL : Fin P.a → Fin 2 → ℝ) (xR : Fin P.b → Fin 2 → ℝ) (v : Fin P.a) : ℝ :=
  max (P.utilL xR v 0) (P.utilL xR v 1) - ∑ c, xL v c * P.utilL xR v c

/-- Regret of right vertex `w`. -/
def regretR (xL : Fin P.a → Fin 2 → ℝ) (xR : Fin P.b → Fin 2 → ℝ) (w : Fin P.b) : ℝ :=
  max (P.utilR xL w 0) (P.utilR xL w 1) - ∑ d, xR w d * P.utilR xL w d

end BipartitePolymatrix

/-- The search problem of Assumption 1 (p. 14): given a bipartite polymatrix game of maximum
degree three with two actions per vertex, find a (rational) mixed profile in which all but a
`δ` fraction of the vertices have regret at most `ε`. -/
def PolymatrixWeakNE (ε δ : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ P : BipartitePolymatrix, P.Valid ∧ s = P.code
  answer s t := ∃ P : BipartitePolymatrix, P.Valid ∧ s = P.code ∧
    ∃ (xL : Fin P.a → Fin 2 → ℚ) (xR : Fin P.b → Fin 2 → ℚ),
      t = (List.finRange P.a).flatMap (fun v => CardinalMatching.encRatVec 2 (xL v)) ++
        (List.finRange P.b).flatMap (fun w => CardinalMatching.encRatVec 2 (xR w)) ∧
      (∀ v, IsDist (fun c => (xL v c : ℝ))) ∧ (∀ w, IsDist (fun d => (xR w d : ℝ))) ∧
      (((Finset.univ.filter (fun v => ε < P.regretL (fun v c => (xL v c : ℝ))
            (fun w d => (xR w d : ℝ)) v)).card +
        (Finset.univ.filter (fun w => ε < P.regretR (fun v c => (xL v c : ℝ))
            (fun w d => (xR w d : ℝ)) w)).card : ℕ) : ℝ) ≤ δ * ((P.a + P.b : ℕ) : ℝ)

/-- **Assumption 1 (PCP-for-PPAD)** (§2.4, p. 14): there are constants `ε*, δ* ∈ (0, 1)` such that
`PolymatrixWeakNE ε* δ*` is PPAD-hard. A proposition; it is only ever a hypothesis. -/
def Assumption1 : Prop :=
  ∃ ε δ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < δ ∧ δ < 1 ∧ CEPolytopeHard.PPADHard (PolymatrixWeakNE ε δ)

end SparseCCE.ThreePlayer


