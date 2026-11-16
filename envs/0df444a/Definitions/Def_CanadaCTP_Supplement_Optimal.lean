-- Prove2me | Definitions.Def_CanadaCTP_Supplement_Optimal
-- name    : CanadaCTP_Supplement_Optimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:34:52.1131+00:00
-- url     : https://prove2.me/theorems/fac5ba26-4a5e-47d0-bb91-746161b1dda9
-- title:
--   Optimal adaptive policies and the first move of a policy
-- statement:
--   A policy $\pi$ of a CTP instance is an **optimal adaptive policy** if it is feasible (it reaches $t$ almost surely) and its expected cost equals
--   $$\mathbb E[\pi]=\mathbb E[\mathrm{Opt}]=\inf\{\mathbb E[\pi']:\pi'\text{ feasible}\}.$$
--
--   A policy **traverses edge $(i,j)$ as its first move** if $j$ is the first edge of path $i$ (only edges at $s$ can be first moves) and, almost surely, the first edge it traverses is the first edge of path $i$. On instances whose paths all have at least two edges this is expressed through revealed weights: traversing the first edge of a path $i'$ reveals the second edge of $i'$, and nothing else reveals it earlier, so the first move is the first edge of path $i$ iff, in every positive-probability configuration, the second edge of path $i$ is revealed as soon as the second edge of any path is.
--
--   These notions state the first-move decision problem of Theorems 2 and 6.
--
--   **Formalization Note** The infimum is the published `CanadaCTP.optCost` over all feasible randomized stateful policies; optimality is attainment. Every realization has positive probability, so "for every configuration in the support of the run" means almost surely.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), §2, p.5 (optimal adaptive policy); Theorem 6, p.26 and Theorem 2, p.29 (first move)

import Mathlib
import Definitions.Def_CanadaCTP_Model

namespace CanadaCTP.Supplement

open CanadaCTP
open scoped ENNReal

/-- An **optimal adaptive policy** (Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled*,
manuscript, sha256 8117348e…3a33, §2, p.5): a feasible policy (it reaches `t` almost surely)
whose expected cost equals `E[Opt]`, the infimum over all feasible randomized stateful policies.

**Formalization Note.** `optCost` is the published `CanadaCTP.optCost`; optimality is attainment
of that infimum, not `ε`-optimality. -/
def IsOptimal (I : Inst) {Mem : Type} (π : Policy I Mem) : Prop :=
  Feasible I π ∧ expCost I π = optCost I

/-- Almost surely, the first edge `π` traverses is the first edge of path `i` (*Canada
Retravelled*, Theorems 2 and 6, pp.26, 29: "traverses a given edge as its first move").

The run starts at `s`, so the first traversal is the first edge `(i', 0)` of some path `i'`; it
makes the traveller reach vertex `1` of path `i'`, which reveals edge `1` of path `i'`, and no other
step reveals that edge earlier. So on instances in which every path has at least two edges, "the
first traversal is `(i, 0)`" holds in every positive-probability configuration of every
realization iff: whenever edge `1` of some path is revealed, edge `1` of path `i` is revealed.

**Formalization Note.** Every realization has positive probability (all listed probabilities are
positive) and the support of `lawN` is the set of positive-probability configurations, so the
universal quantifiers below are "almost surely". The predicate is used only on instances whose
paths have exactly two edges. -/
def FirstMoveIsPath (I : Inst) {Mem : Type} (π : Policy I Mem) (i : Fin I.k) : Prop :=
  ∀ (ι : Realz I) (N : ℕ), ∀ c ∈ (lawN I π ι N).support,
    ∀ (i' : Fin I.k) (e : Fin (I.m i')), e.val = 1 → c.rev i' e = true →
      ∃ e' : Fin (I.m i), e'.val = 1 ∧ c.rev i e' = true

/-- `π` traverses edge `j` of path `i` as its first move, almost surely. Only an edge at `s`
(`j = 0`) can be a first move; for `j ≠ 0` the predicate is false. -/
def TraversesFirst (I : Inst) {Mem : Type} (π : Policy I Mem) (i : Fin I.k)
    (j : Fin (I.m i)) : Prop :=
  j.val = 0 ∧ FirstMoveIsPath I π i

end CanadaCTP.Supplement


