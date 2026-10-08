-- Prove2me | Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate
-- name    : GilmoreGomoryTSP_MinCost_Underestimate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:20.017991+00:00
-- url     : https://prove2.me/theorems/c222d886-ac6b-4171-b11b-7f638b037674
-- title:
--   pp. 665–668 — the intervals P_q (15), P (16), the underestimate c* (17) and the graph G_ψ* with conditions (22a)/(22b)
-- statement:
--   These are the objects of the sections "An underestimate of the cost of a permutation" and "An underestimate of the cost of a tour" of Gilmore and Gomory's paper. Throughout, $A_i, B_i$ are the starting and final states of the jobs, $f, g$ the cost densities, and $\varphi$ a permutation ranking the $A$.
--
--   1. For $q = 1,\dots,N-1$ the interval (15)
--   $$P_q = [B_q, B_{q+1}] \cap [A_{\varphi(q)}, A_{\varphi(q+1)}],$$
--   and their union (16) $P = \bigcup_{q=1}^{N-1} P_q$.
--   2. The underestimating cost (17) of having job $j$ follow job $i$,
--   $$c^*_{ij} = \big|[B_i,+\infty]\cap[-\infty,A_j]\cap P\big|_f + \big|[-\infty,B_i]\cap[A_j,+\infty]\cap P\big|_g,\qquad |S|_f = \int_S f(x)\,dx,$$
--   and the underestimate $c^*(\psi) = \sum_i c^*_{i\psi(i)}$ of a permutation $\psi$.
--   3. The graph $G_\psi^*$: it contains all the arcs of $G_\varphi$, and the arc $R_{q,q+1}$ for every $q$ for which either (22a) $i \le q < \varphi^{-1}\psi(i)$ holds for some $i$, or (22b) $\varphi^{-1}\psi(j) \le q < j$ holds for some $j$.
--
--   The underestimate $c^*$ yields the lower bound $c(\psi)\ge c(\varphi)+c^*(\psi)$ (Theorem 4), and $G_\psi^*$ connects the cost of a tour to the cost of a spanning tree of $G_\varphi$.
--
--   **Formalization Note** In 0-based indexing $P_q$ is indexed by `q : Fin n` and uses the jobs `q.castSucc`, `q.succ`; (22a)/(22b) compare indices in `Fin (n + 1)` with `q.castSucc`, which is the same as comparing the paper's 1-based indices. The sets $|S|_f$ are set integrals over closed intervals intersected with $P$; endpoints have measure zero, so open or closed intervals give the same values.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), pp. 665–668, Eqs. (15)–(17), (22a), (22b), and the definition of G_ψ* on p. 668

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

/-- The interval (15) `P_q = [B_q, B_{q+1}] ∩ [A_{φ(q)}, A_{φ(q+1)}]`, for the adjacent pair
`q.castSucc`, `q.succ` (the paper's `q`, `q + 1`). -/
def Pq (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) : Set ℝ :=
  Set.Icc (B q.castSucc) (B q.succ) ∩ Set.Icc (A (φ q.castSucc)) (A (φ q.succ))

/-- The set (16) `P = ⋃_{q=1}^{N−1} P_q`. -/
def P (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) : Set ℝ :=
  ⋃ q, Pq A B φ q

/-- The underestimating cost (17) of having job `j` follow job `i`:
`c*_ij = |[B_i, +∞] ∩ [−∞, A_j] ∩ P|_f + |[−∞, B_i] ∩ [A_j, +∞] ∩ P|_g`, where `|S|_f = ∫_S f`. -/
noncomputable def cStar (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : ℝ :=
  (∫ x in Set.Icc (B i) (A j) ∩ P A B φ, f x) + ∫ x in Set.Icc (A j) (B i) ∩ P A B φ, g x

/-- The underestimate `c*(ψ) = ∑_i c*_{i ψ(i)}` (p. 665). -/
noncomputable def costStar (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) :
    ℝ :=
  ∑ i, cStar f g A B φ i (ψ i)

/-- The adjacent arcs `R_{q,q+1}` for which (22a) `i ≤ q < φ⁻¹ψ(i)` holds for some `i` or (22b)
`φ⁻¹ψ(j) ≤ q < j` holds for some `j` (here `q` stands for the lower node `q.castSucc`). -/
def starArcs (φ ψ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    (∃ i, i ≤ q.castSucc ∧ q.castSucc < φ.symm (ψ i)) ∨
      ∃ j, φ.symm (ψ j) ≤ q.castSucc ∧ q.castSucc < j

/-- The graph `G_ψ*` (p. 668): all the arcs of `G_φ`, plus every arc `R_{q,q+1}` for which (22a)
holds for some `i` or (22b) holds for some `j`. -/
def graphStar (φ ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  graphWith φ (adjArcs (starArcs φ ψ))

end GilmoreGomoryTSP.MinCost


