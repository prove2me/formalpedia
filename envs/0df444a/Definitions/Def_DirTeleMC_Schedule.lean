-- Prove2me | Definitions.Def_DirTeleMC_Schedule
-- name    : DirTeleMC_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:58.994203+00:00
-- url     : https://prove2.me/theorems/e4484d3a-20a2-4a17-8bb7-5d8dcc61472c
-- title:
--   Telephone schedules, valid schedules and informing $k$ terminals
-- statement:
--   A **schedule** is a finite sequence of rounds, each a list of calls $(u, v)$ meaning that $u$ calls $v$. Initially only $s$ is informed; a called vertex is informed at the end of the round. The length of a schedule is its number of rounds.
--
--   A schedule is **valid** when in every round:
--   1. every call $(u,v)$ is an arc of $G$ and its caller $u$ was informed before the round;
--   2. no vertex takes part in more than one call of the round.
--
--   A schedule **informs $k$ terminals** when at least $k$ terminals of $K$ are informed after its last round. The optimum OPT is the least length of a valid schedule informing $k$ terminals; statements compare with every such schedule instead of taking a minimum.
--
--   **Formalization Note** Calls to an already informed vertex are allowed and harmless; a vertex calling itself is excluded by the second condition.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §1, p.1 (PDF p.2); §3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_DirTeleMC_Inst

namespace DirTeleMC

/-- **Telephone schedules.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §1, p.1: "A schedule specifies the calls made in each round".

A schedule on `Fin n` is a list of rounds; round `j + 1` is the `j`-th list, and a call `(u, v)` in it means
that `u` calls `v` in that round. Its length is its number of rounds. -/
abbrev Schedule (n : ℕ) : Type := List (List (Fin n × Fin n))

/-- The set of vertices informed after the first `j` rounds of `S`, starting from `{s}` (p.1: "Initially,
only s is informed"; the called vertex "receives the message at the end of the round"). Rounds beyond the
end of `S` are empty. -/
def informedAfter {n : ℕ} (s : Fin n) (S : Schedule n) : ℕ → Finset (Fin n)
  | 0 => {s}
  | j + 1 => informedAfter s S j ∪ ((S.getD j []).map Prod.snd).toFinset

/-- **A valid (feasible) schedule** (p.1: "In each round, every vertex that knows the message may call at most
one neighbour, which receives the message at the end of the round, and no vertex takes part in more than one
call per round"; "calls must follow the direction of the edges").

In every round, every call `(u, v)` is an arc of `G` whose caller `u` is informed before the round, and the
callers and callees of the round's calls are pairwise distinct vertices.

**Formalization Note.** Calls to an already informed vertex are allowed (they are harmless). Distinct endpoints
also exclude a vertex calling itself. -/
def Schedule.Valid (I : Inst) (S : Schedule I.n) : Prop :=
  ∀ j (hj : j < S.length),
    (∀ c ∈ S[j], I.adj c.1 c.2 = true ∧ c.1 ∈ informedAfter I.s S j) ∧
    (S[j].flatMap fun c => [c.1, c.2]).Nodup

/-- The schedule informs at least `k` terminals of `K` (all of them for DTM, where `k = |K|`) by its last
round. -/
def Schedule.InformsK (I : Inst) (S : Schedule I.n) : Prop :=
  I.k ≤ (I.K ∩ informedAfter I.s S S.length).card

/-- A schedule with its vertices written as natural numbers (the output format of the machine in
Theorem 1.1). -/
def Schedule.toNat {n : ℕ} (S : Schedule n) : List (List (ℕ × ℕ)) :=
  S.map (List.map fun c => (c.1.val, c.2.val))

end DirTeleMC


