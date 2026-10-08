-- Prove2me | Definitions.Def_SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder
-- name    : SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:23:02.448698+00:00
-- url     : https://prove2.me/theorems/869855c8-484e-48df-a903-dd70432e5c78
-- title:
--   Convex bipartite orders (Section 4.1)
-- statement:
--   A *convex bipartite order* $\mathbf P = (N = J^- \cup J^+, P)$ (§4.1 of Ambühl, Mastrolilli, Mutsanas and Svensson) is given as follows.
--
--   1. The jobs are divided into two disjoint sets: the *minus jobs* $J^- = \{j_1, \dots, j_a\}$ and the *plus jobs* $J^+ = \{j_{a+1}, \dots, j_n\}$, with $b = n - a$ plus jobs.
--   2. Each plus job $j_k$ carries two indices $l(k), r(k)$ of minus jobs with $1 \le l(k) \le r(k) \le a$, and
--   $$
--   (j_i, j_k) \in P \iff l(k) \le i \le r(k) \qquad (j_i \in J^-,\ j_k \in J^+).
--   $$
--
--   Apart from the reflexive pairs $(x,x)$, these are the only pairs of $P$: precedences run only from minus jobs to plus jobs (bipartiteness), and the predecessors of each plus job form an interval of consecutive minus jobs (convexity). In particular every plus job has at least one predecessor, two minus jobs are always incomparable, and so are two plus jobs. The relation $P$ is a partial order, and this file records that fact.
--
--   **Formalization Note** The jobs are the type `Fin a ⊕ Fin b`: `Sum.inl i` is the minus job $j_{i+1}$ and `Sum.inr k` is the plus job $j_{a+k+1}$ (indices start at $0$). The interval ends are maps `l r : Fin b → Fin a` with `l k ≤ r k`. Every convex bipartite order in the paper's sense is, after naming its jobs, one of these; the empty cases $a = 0$ or $b = 0$ are allowed (with $a = 0$ forcing $b = 0$).
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 657, Section 4.1, items (i)-(ii)

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_Realizer

namespace SingleMachinePrec.ConvexBipartite

/-- The jobs of a convex bipartite order with `a` minus jobs and `b` plus jobs: `Sum.inl i` is the
minus job `j_{i+1}` (`i : Fin a`) and `Sum.inr k` is the plus job `j_{a+k+1}` (`k : Fin b`). -/
abbrev Job (a b : ℕ) : Type := Fin a ⊕ Fin b

/-- A *convex bipartite order* (Ambühl et al. 2011, §4.1, p. 657) with minus jobs
`J⁻ = Fin a` and plus jobs `J⁺ = Fin b`: every plus job `k` carries two indices
`l k ≤ r k` of minus jobs, and minus job `i` precedes plus job `k` exactly when
`l k ≤ i ≤ r k`. -/
structure ConvexBipartiteOrder (a b : ℕ) where
  /-- left end `l(k)` of the interval of predecessors of the plus job `k` -/
  l : Fin b → Fin a
  /-- right end `r(k)` of the interval of predecessors of the plus job `k` -/
  r : Fin b → Fin a
  /-- `l(k) ≤ r(k)` -/
  l_le_r : ∀ k, l k ≤ r k

namespace ConvexBipartiteOrder

variable {a b : ℕ}

/-- The (reflexive) precedence relation `P` of the convex bipartite order: `(x, y) ∈ P` iff
`x = y`, or `x` is a minus job `i`, `y` is a plus job `k` and `l(k) ≤ i ≤ r(k)`. -/
def prec (C : ConvexBipartiteOrder a b) : Job a b → Job a b → Prop
  | x, y => x = y ∨ ∃ i k, x = Sum.inl i ∧ y = Sum.inr k ∧ C.l k ≤ i ∧ i ≤ C.r k

/-- The precedence relation of a convex bipartite order is a partial order. -/
instance (C : ConvexBipartiteOrder a b) : IsPartialOrder (Job a b) C.prec where
  refl x := Or.inl rfl
  trans x y z hxy hyz := by
    rcases hxy with rfl | ⟨i, k, rfl, rfl, h1, h2⟩
    · exact hyz
    · rcases hyz with rfl | ⟨i', k', h, -, -, -⟩
      · exact Or.inr ⟨i, k, rfl, rfl, h1, h2⟩
      · cases h
  antisymm x y hxy hyx := by
    rcases hxy with h | ⟨i, k, rfl, rfl, -, -⟩
    · exact h
    · rcases hyx with h | ⟨i', k', h, -, -, -⟩
      · exact h.symm
      · cases h

end ConvexBipartiteOrder

end SingleMachinePrec.ConvexBipartite


