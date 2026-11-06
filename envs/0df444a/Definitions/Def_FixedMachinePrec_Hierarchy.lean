-- Prove2me | Definitions.Def_FixedMachinePrec_Hierarchy
-- name    : FixedMachinePrec_Hierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:06.570097+00:00
-- url     : https://prove2.me/theorems/611ece90-20f6-49e5-abbd-0d590a2942b0
-- title:
--   Definition 5.7: a hierarchy described by two families $(\mathcal F,\mathcal F_{\mathrm{cut}})$
-- statement:
--   A **hierarchy** for a feasible full instance on $J$ is a finite rooted tree of job sets with root $J$. At each nonempty node $W$ one chooses a feasible full schedule $S_W=(S_1,\dots,S_q)$, $q=|W|/m$, and marked positions $1\le t_1<\dots<t_k\le q$ with $k\ge1$. With $t_0=0$ and $t_{k+1}=q+1$ the **open gaps** are
--   $$A_i=\bigcup_{t_i<t<t_{i+1}}S_t\qquad(i=0,\dots,k),$$
--   and the children of $W$ are its nonempty gaps. The hierarchy is **described by** $(\mathcal F,\mathcal F_{\mathrm{cut}})$ if every node set belongs to $\mathcal F$ and, at every nonempty node, each prefix $L_i=\bigcup_{t<t_i}S_t$ before a marked slot satisfies $L_i=W\cap C_i$ for some global cut $C_i\in\mathcal F_{\mathrm{cut}}$.
--
--   $W$ is the root of a described hierarchy if either $W=\emptyset\in\mathcal F$, or $W\in\mathcal F$ is nonempty and carries such a schedule, marks and cuts, with a described hierarchy rooted at every nonempty gap.
--
--   This certificate is what the evaluation algorithm can follow: every nonempty node has at least one marked slot, so every child has at most $|W|-m$ jobs.
--
--   **Formalization Note** The tree is encoded as an inductive predicate; the children of a node are determined by its own schedule and marks, so this is the paper's tree.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Definition 5.7, p.15

import Mathlib
import Definitions.Def_FixedMachinePrec_FullSchedule

namespace FixedMachinePrec

/-- The open gaps `A_0, …, A_k` of a node with schedule `S = (S_1, …, S_q)` and marked positions
`t_1 < ⋯ < t_k`: with `t_0 = 0`, `t_{k+1} = q + 1`, `A_i = ⋃_{t_i < t < t_{i+1}} S_t`
(Definition 5.7, p.15). -/
def gaps {N : ℕ} (S : List (Finset (Fin N))) (marks : List ℕ) : List (Finset (Fin N)) :=
  let bs := 0 :: marks ++ [S.length + 1]
  (bs.zip bs.tail).map fun ab => slotsBetween S ab.1 ab.2

/-- **A hierarchy described by two families** (Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines*, manuscript, sha256 08cdf3e1…, Definition 5.7, p.15). "A hierarchy for a
feasible full instance on J is a finite rooted tree whose nodes are labelled by job sets, with
root J. At each nonempty node W, choose a feasible full schedule S_W = (S_1, . . . , S_q),
q = |W|/m, and choose marked positions 1 ≤ t_1 < · · · < t_k ≤ q, 1 ≤ k ≤ q. … The children of W
are exactly its nonempty gap sets A_i … The hierarchy is described by (F, F_cut) if every node set
belongs to F and, at every nonempty node W, the prefix L_i := ⋃_{t<t_i} S_t before each marked slot
Z_i satisfies L_i = W ∩ C_i for some global cut C_i ∈ F_cut."

`Described prec m F Fcut W` says that `W` is the root of such a described hierarchy: either
`W = ∅ ∈ F` (an empty node, no children), or `W ∈ F` is nonempty and carries a full schedule `S`,
a nonempty strictly increasing list of marked positions in `{1, …, q}`, a cut `C ∈ F_cut` with
`⋃_{t < t_i} S_t = W ∩ C` for each mark, and a described hierarchy at every nonempty gap.

**Formalization Note** The tree is the derivation: the children of a node are determined by the
node's own schedule and marks, so an inductive predicate is equivalent to the paper's tree. The
last sentence of Theorem 5.8 ("Every nonempty node has at least one marked full slot, and every
child has at most |W| − m jobs") is built in: `marks ≠ []`, and every gap misses the `m` jobs of a
marked slot. -/
inductive Described {N : ℕ} (prec : Fin N → Fin N → Prop) (m : ℕ)
    (F Fcut : Finset (Finset (Fin N))) : Finset (Fin N) → Prop
  | empty (hF : (∅ : Finset (Fin N)) ∈ F) : Described prec m F Fcut ∅
  | node (W : Finset (Fin N)) (hW : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
      (hS : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
      (hinc : marks.Pairwise (· < ·)) (hrange : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
      (hcut : ∀ t ∈ marks, ∃ C ∈ Fcut, slotsBetween S 0 t = W ∩ C)
      (hchild : ∀ A ∈ gaps S marks, A.Nonempty → Described prec m F Fcut A) :
      Described prec m F Fcut W

end FixedMachinePrec


