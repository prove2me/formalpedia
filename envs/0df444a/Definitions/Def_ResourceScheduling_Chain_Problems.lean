-- Prove2me | Definitions.Def_ResourceScheduling_Chain_Problems
-- name    : ResourceScheduling_Chain_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:24:23.013156+00:00
-- url     : https://prove2.me/theorems/b4f2171a-6ecd-4f33-be81-47bfe1afa7cc
-- title:
--   The decision problems $P2\mid res111, chain, p_j=1\mid C_{\max}$ and $P3\mid res1\cdot\cdot, p_j=1\mid C_{\max}$
-- statement:
--   This file defines the two scheduling problems of the mission as decision problems whose instances are pairs $(I, y)$ of a scheduling instance $I$ (see the model definition) and a threshold $y \in \mathbb{N}$.
--
--   **Numeric description.** An instance $I$ is described by the list of natural numbers
--   $$n,\ m,\ l,\ s_1,\dots,s_l,\ r_{11},\dots,r_{1n},\ \dots,\ r_{l1},\dots,r_{ln},\ |A|,\ j_1, k_1,\ \dots,\ j_{|A|}, k_{|A|},$$
--   where $(j_1,k_1),\dots$ are the arcs $A$ of the precedence graph $H$; the pair $(I,y)$ is described by this list followed by $y$. Written in unary, this is the encoding under which NP-hardness in the strong sense is stated.
--
--   1. **$P2\mid res111, chain, p_j = 1\mid C_{\max}$.** Two identical machines ($m=2$); one resource ($\lambda = 1$) of size one ($\sigma = 1$); every requirement at most one ($\rho = 1$); $H$ acyclic and chain-like (indegree and outdegree at most one at every vertex); unit processing times. $(I,y)$ is a yes-instance when $I$ is of this type and some feasible schedule has $C_{\max} \le y$.
--   2. **$P3\mid res1\cdot\cdot, p_j = 1\mid C_{\max}$.** Three identical machines ($m=3$); one resource ($\lambda=1$) whose size is a positive integer that is part of the input ($\sigma = \cdot$); requirements arbitrary ($\rho=\cdot$); no precedence constraints ($H$ has no arcs); unit processing times. $(I,y)$ is a yes-instance when $I$ is of this type and some feasible schedule has $C_{\max} \le y$.
--
--   These are the problems of Theorems 7 and 4 of the paper.
--
--   **Formalization Note.** The class conditions are part of the yes-predicate, so the code of an instance outside the class is not in the language. Thresholds are natural numbers; all data of these problems are integers, and restricting the thresholds to integers makes a hardness statement stronger, not weaker.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 12–13, Section 2 (resλσρ); pp. 22–23, Appendix; p. 16, Theorem 4; p. 18, Theorem 7

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Model

/-!
# The problems `P2 | res111, chain, p_j = 1 | C_max` and `P3 | res1··, p_j = 1 | C_max`

Decision versions, with instances `(I, y)` for an instance `I` and a threshold `y ∈ ℕ`.
Błażewicz, Lenstra & Rinnooy Kan (1983), pp. 12–13 and 22–23.
-/

namespace ResourceScheduling.Chain

namespace Instance

/-- The numbers describing an instance, in order: `n, m, l`, the sizes `s_h`, the requirements
`r_hj` (row by row), the number of arcs, and the arcs `(j, k)` as index pairs. -/
def code (I : Instance) : List ℕ :=
  [I.n, I.m, I.l] ++ List.ofFn I.s ++ (List.ofFn fun h => List.ofFn (I.r h)).flatten ++
    [I.arcs.length] ++ I.arcs.flatMap (fun e => [(e.1 : ℕ), (e.2 : ℕ)])

/-- The numbers describing a decision instance `(I, y)`: those of `I` followed by `y`. -/
def decisionCode (x : Instance × ℕ) : List ℕ := x.1.code ++ [x.2]

end Instance

/-- `I` is an instance of `P2 | res111, chain, p_j = 1`: two machines, one resource of size one,
every requirement at most one, and an acyclic chain-like precedence digraph. -/
def IsP2Res111Chain (I : Instance) : Prop :=
  I.m = 2 ∧ I.l = 1 ∧ (∀ h, I.s h = 1) ∧ (∀ h j, I.r h j ≤ 1) ∧ I.IsChain ∧ I.Acyclic

/-- Yes-instances of the decision version of `P2 | res111, chain, p_j = 1 | C_max`. -/
def P2Res111Chain (x : Instance × ℕ) : Prop :=
  IsP2Res111Chain x.1 ∧ x.1.HasScheduleWithin x.2

/-- `I` is an instance of `P3 | res1··, p_j = 1`: three machines, one resource of arbitrary
positive size, arbitrary requirements, and no precedence arcs. -/
def IsP3Res1 (I : Instance) : Prop :=
  I.m = 3 ∧ I.l = 1 ∧ I.SizesPositive ∧ I.arcs = []

/-- Yes-instances of the decision version of `P3 | res1··, p_j = 1 | C_max`. -/
def P3Res1 (x : Instance × ℕ) : Prop :=
  IsP3Res1 x.1 ∧ x.1.HasScheduleWithin x.2

end ResourceScheduling.Chain


