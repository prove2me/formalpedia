-- Prove2me | Definitions.Def_KelsoCrawford_NoCore_Notions
-- name    : KelsoCrawford_NoCore_Notions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:06.883273+00:00
-- url     : https://prove2.me/theorems/f28b2f8b-866a-40c7-88fc-98f94b9afba1
-- title:
--   Subadditivity (p. 1500), total product of an assignment, single-coalition strict improvement
-- statement:
--   Three auxiliary notions for a job-matching market with workers $W$ and firms $F$.
--
--   1. A technology $y : 2^W \to \mathbb{R}$ is **subadditive** (p. 1500) if unions of disjoint sets of workers produce no more than the sum of their separate products:
--   $$y(A \cup B) \le y(A) + y(B) \qquad \text{whenever } A \cap B = \emptyset.$$
--   2. For an assignment $g : W \to F$ of workers to firms, write $g^{-1}(j) = \{i : g(i) = j\}$ for the workers sent to firm $j$; the **total product** of $g$ is
--   $$Y(g) = \sum_{j \in F} y^j\big(g^{-1}(j)\big).$$
--   3. Given an allocation (assignment $f$, salaries $s_{if(i)}$) and permitted salary sets $R_{ij}$, the single coalition of firm $j$ and the set of workers $C$ **can strictly improve upon** the allocation if there are salaries $r_{ij} \in R_{ij}$ ($i \in C$) with $u^i(j; r_{ij}) > u^i(f(i); s_{if(i)})$ for every $i \in C$ and $\pi^j(C; r^j) > \pi^j(C^j; s^j)$.
--
--   The third notion is the coalition-by-coalition form of D3: an allocation can be strictly improved upon exactly when some single pair $(j, C)$ can strictly improve upon it. It lets one state the paper's inequalities (24)–(27), each of which comes from one named coalition.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1500 (subadditivity), p. 1503 (total product), p. 1488, D3

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_Returns_Technology

namespace KelsoCrawford.NoCore

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- The set of workers that an assignment `g` (worker ↦ firm) sends to firm `j`. -/
def assignedTo (g : W → F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => g i = j)

/-- Total product of an assignment `g`: the sum over firms of the gross product of the workers
assigned to each firm. -/
def Market.totalProduct (M : Market W F) (g : W → F) : ℝ :=
  ∑ j, M.y j (assignedTo g j)

/-- The single coalition of firm `j` and the set of workers `C` can strictly improve upon `A`
(with salaries from `R`): there are salaries `r` making every member of `C` strictly better off
and firm `j`'s KelsoCrawford.Process.profit strictly larger, i.e. (3) and (4) of p. 1488 with strict inequality. -/
def Market.CoalitionCanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) (j : F) (C : Finset W) : Prop :=
  ∃ r : W → ℝ,
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r

end KelsoCrawford.NoCore


