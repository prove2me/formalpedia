-- Prove2me | Definitions.Def_OnlineStochMatching_Hardness_SixCycle
-- name    : OnlineStochMatching_Hardness_SixCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:46:28.116978+00:00
-- url     : https://prove2.me/theorems/66baae8c-27f9-4ffa-a884-4acf84c4b7ff
-- title:
--   The 6-cycle instance and its k disjoint copies (Section 3, Appendix B)
-- statement:
--   This definition fixes the hard instances of Feldman, Mehta, Mirrokni and Muthukrishnan (§3 and Appendix B).
--
--   1. **The 6-cycle.** The advertisers are $A = \{a, b, c\}$, the impression types are $I = \{x, y, z\}$, and the edge set is
--   $$E = \{(x, a), (y, a), (y, b), (z, b), (z, c), (x, c)\},$$
--   so $x$ is adjacent to $a$ and $c$, $y$ to $a$ and $b$, and $z$ to $b$ and $c$. Together with the uniform distribution $(1/3, 1/3, 1/3)$ on $I$ and $n = 3$ arrivals this is the paper's single hard instance.
--   2. **$k$ disjoint 6-cycles.** For $k \ge 1$, the advertisers are $\{1, \dots, k\} \times \{a, b, c\}$ and the impression types $\{1, \dots, k\} \times \{x, y, z\}$; $(j, p)$ and $(j', i)$ are adjacent iff $j = j'$ and $(i, p) \in E$. With the uniform distribution on the $3k$ impression types and $n = 3k$ arrivals this is the paper's family of instances with $n \to \infty$.
--
--   The single 6-cycle is the case $k = 1$ of the family, up to renaming the one copy.
--
--   **Formalization Note** The 6-cycle's sides are the three-element types `Adv` and `Imp`; edges are stored as (advertiser, impression type) pairs. The copies are indexed by `Fin k`. The single instance and the family are defined separately (the family through the 6-cycle's edge relation), and the theorems use the single cycle for $n = 3$ and the family for $n = 3k$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Section 3 (the 6-cycle); p. 13, Appendix B (k copies of 6-cycles)

import Mathlib

namespace OnlineStochMatching.Hardness

/-- The advertisers `A = {a, b, c}` of the 6-cycle instance (§3, p. 4). -/
inductive Adv
  | a
  | b
  | c
  deriving DecidableEq, Repr

instance : Fintype Adv := ⟨{.a, .b, .c}, fun p => by cases p <;> decide⟩

/-- The impression types `I = {x, y, z}` of the 6-cycle instance (§3, p. 4). -/
inductive Imp
  | x
  | y
  | z
  deriving DecidableEq, Repr

instance : Fintype Imp := ⟨{.x, .y, .z}, fun i => by cases i <;> decide⟩

/-- The edge set `E = {(x, a), (y, a), (y, b), (z, b), (z, c), (x, c)}` of the 6-cycle (§3, p. 4),
written as (advertiser, impression type) pairs. -/
def cycleEdges : Finset (Adv × Imp) :=
  {(.a, .x), (.a, .y), (.b, .y), (.b, .z), (.c, .z), (.c, .x)}

/-- Adjacency in the 6-cycle: `cycleEdge p i` iff `(p, i) ∈ E`. -/
def cycleEdge (p : Adv) (i : Imp) : Prop := (p, i) ∈ cycleEdges

instance : DecidableRel cycleEdge := fun p i => by
  unfold cycleEdge
  infer_instance

/-- The `k` disjoint copies of the 6-cycle (App. B, p. 13): advertisers `Fin k × A`, impression
types `Fin k × I`, and `((j, p), (j', i))` is an edge iff the two lie in the same copy (`j = j'`)
and `(p, i)` is an edge of the 6-cycle. -/
def kCycleEdge (k : ℕ) (p : Fin k × Adv) (i : Fin k × Imp) : Prop :=
  p.1 = i.1 ∧ cycleEdge p.2 i.2

instance (k : ℕ) : DecidableRel (kCycleEdge k) := fun p i => by
  unfold kCycleEdge
  infer_instance

end OnlineStochMatching.Hardness


