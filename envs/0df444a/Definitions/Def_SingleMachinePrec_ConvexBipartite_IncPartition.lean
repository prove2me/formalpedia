-- Prove2me | Definitions.Def_SingleMachinePrec_ConvexBipartite_IncPartition
-- name    : SingleMachinePrec_ConvexBipartite_IncPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:32:31.739329+00:00
-- url     : https://prove2.me/theorems/6b37d8df-e086-4bb8-8b49-0e293f7a986a
-- title:
--   The sets $E_1, E_2, E_3$ of incomparable pairs and $\bar E_m = E_m \cup P$ (Appendix)
-- statement:
--   Let $\mathbf P$ be a convex bipartite order with minus jobs $j_1,\dots,j_a$ and plus jobs $j_{a+1},\dots,j_n$. The Appendix of Ambühl, Mastrolilli, Mutsanas and Svensson sorts the incomparable pairs $(j_i, j_j) \in \mathrm{inc}(\mathbf P)$ into three sets.
--
--   1. $(j_i, j_j) \in E_1$ if $i > j$ and $j_i, j_j \in J^-$; else, if $i < j$ and $j_i, j_j \in J^+$; else, if $j_i \in J^-$ and $j_j \in J^+$.
--   2. $(j_i, j_j) \in E_2$ if $i < j$ and $j_i, j_j \in J^-$; else, if $j_i \in J^+$, $j_j \in J^-$ and there is a $k > i$ with $(j_j, j_k) \in P$.
--   3. $(j_i, j_j) \in E_3$ if $i > j$ and $j_i, j_j \in J^+$; else, if $j_i \in J^+$, $j_j \in J^-$ and $(j_j, j_k) \notin P$ for all $k > i$.
--
--   Each $E_m$ consists of incomparable pairs only. For $m = 1,2,3$ put
--   $$
--   \bar E_m = E_m \cup P .
--   $$
--   A pair $(x,y) \in \bar E_m$ is read as "$x$ comes before $y$" in the $m$-th linear order of the realizer built in the Appendix.
--
--   **Formalization Note** In the second clauses of $E_2$ and $E_3$ the index $k$ exceeds the index of a plus job, so $k$ ranges over plus jobs; with plus jobs indexed by `Fin b`, "$k > i$" compares plus indices. The relation $\bar E_m$ is `Ebar C E` applied to `E = E1`, `E2` or `E3`.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 667, Appendix (definition of E_1, E_2, E_3), and p. 668, Lemma A.2 (definition of Ē_m)

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder

namespace SingleMachinePrec.ConvexBipartite

namespace ConvexBipartiteOrder

variable {a b : ℕ}

/-- `E₁` (Appendix, p. 667): an incomparable pair `(x, y)` lies in `E₁` if both are minus jobs
and `x` has the larger index; else, if both are plus jobs and `x` has the smaller index; else,
if `x` is a minus job and `y` a plus job. -/
def E1 (C : ConvexBipartiteOrder a b) (x y : Job a b) : Prop :=
  SingleMachinePrec.Framework.Incomparable C.prec x y ∧
    match x, y with
    | Sum.inl i, Sum.inl j => j < i
    | Sum.inr i, Sum.inr j => i < j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => False

/-- `E₂` (Appendix, p. 667): an incomparable pair `(x, y)` lies in `E₂` if both are minus jobs
and `x` has the smaller index; else, if `x` is a plus job `i`, `y` is a minus job `j`, and there
is a plus job `k` with larger index than `i` such that `(j, k) ∈ P`. -/
def E2 (C : ConvexBipartiteOrder a b) (x y : Job a b) : Prop :=
  SingleMachinePrec.Framework.Incomparable C.prec x y ∧
    match x, y with
    | Sum.inl i, Sum.inl j => i < j
    | Sum.inr i, Sum.inl j => ∃ k : Fin b, i < k ∧ C.prec (Sum.inl j) (Sum.inr k)
    | _, _ => False

/-- `E₃` (Appendix, p. 667): an incomparable pair `(x, y)` lies in `E₃` if both are plus jobs
and `x` has the larger index; else, if `x` is a plus job `i`, `y` is a minus job `j`, and
`(j, k) ∉ P` for every plus job `k` with larger index than `i`. -/
def E3 (C : ConvexBipartiteOrder a b) (x y : Job a b) : Prop :=
  SingleMachinePrec.Framework.Incomparable C.prec x y ∧
    match x, y with
    | Sum.inr i, Sum.inr j => j < i
    | Sum.inr i, Sum.inl j => ∀ k : Fin b, i < k → ¬ C.prec (Sum.inl j) (Sum.inr k)
    | _, _ => False

/-- `Ē = E ∪ P` (Appendix, Lemma A.2, p. 668): `(x, y) ∈ Ē` iff `(x, y) ∈ P` or `(x, y) ∈ E`. -/
def Ebar (C : ConvexBipartiteOrder a b) (E : Job a b → Job a b → Prop) (x y : Job a b) : Prop :=
  C.prec x y ∨ E x y

end ConvexBipartiteOrder

end SingleMachinePrec.ConvexBipartite


