-- Prove2me | Definitions.Def_IgnallSchrage_Makespan_Procedure
-- name    : IgnallSchrage_Makespan_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:23.127966+00:00
-- url     : https://prove2.me/theorems/5f800709-51a7-4396-b9a6-8371ef70f196
-- title:
--   The branch-and-bound procedure of p. 402, with its tie rule (p. 403)
-- statement:
--   Fix $n$ jobs and a bound function $LB$ that assigns a real number to every node (partial sequence). The procedure keeps a list of nodes ranked by $LB$, smallest first.
--
--   1. **Start.** The list holds only the root, the node that has scheduled no job.
--   2. **Terminal nodes.** A node is terminal when it has scheduled $n-1$ jobs; its last job is then forced.
--   3. **One step.** If the first node $P$ of the list is terminal, the procedure has stopped and the list is left unchanged. Otherwise $P$ is removed, a child $P$ followed by $j$ is created for every job $j$ not in $P$, and the children are inserted into the rest of the list one at a time, in increasing index $j$. A child $x$ is inserted at the first position whose node $y$ satisfies $LB(x)\le LB(y)$, so a new node goes before every node already on the list with the same bound, its earlier-inserted siblings included.
--   4. **Run.** $\mathrm{run}(k)$ is the list after $k$ steps. The procedure stops at the first $k$ for which the first node of $\mathrm{run}(k)$ is terminal.
--   5. **Created nodes.** $\mathrm{created}(k)$ counts the root plus every child formed in the first $k$ steps.
--
--   The paper states: "(1) Remove the first node from the list. (2) Create a new node for every job that the 'just removed' node has not yet scheduled. ... (3) Compute the lower bounds and other attributes for these newly created nodes and insert them ranked on the list. (4) Go to 1." Its example (p. 403) adds the tie rule "if a newly created node and another node had the same lower bound, the newly created node was put before the old node on the list".
--
--   **Formalization Note** The paper's stopping rule speaks of "a node that has scheduled all $n$ jobs"; here the procedure stops at depth $n-1$, whose node determines its full sequence. The paper forces this reading: its example stops at node 231 of a 4-job problem, whose bound "is the makespan for sequence 2314"; "a minimum of $\tfrac12 n(n+1)$ nodes must be created" counts the levels $0$ to $n-1$; and the formula for $LB$ needs a nonempty unscheduled set. For $n=1$ the root itself is terminal. Dominance discarding (pp. 403–405) is not part of the procedure. Where the paper leaves the order of inserting siblings open, the children are inserted in increasing job index; with the tie rule above this reproduces the creation order of the paper's LIST table.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 402, "The Branch-and-Bound Technique", and p. 403, An Example (tie rule)

import Mathlib

namespace IgnallSchrage.Makespan

noncomputable section

/-- A node of the tree is terminal when it has scheduled `n - 1` of the `n` jobs: its last job
is then forced, and its sequence is the node followed by the one unscheduled job. -/
def IsTerminal {n : ℕ} (P : List (Fin n)) : Prop :=
  P.length + 1 = n

instance {n : ℕ} (P : List (Fin n)) : Decidable (IsTerminal P) :=
  inferInstanceAs (Decidable (P.length + 1 = n))

/-- The children of node `P`: one node `P ++ [j]` for every job `j` not yet scheduled in `P`,
in increasing job index `j`. -/
def children {n : ℕ} (P : List (Fin n)) : List (List (Fin n)) :=
  ((List.finRange n).filter (fun j => decide (j ∉ P))).map (fun j => P ++ [j])

/-- Insert node `x` into a list ranked by the bound `LB`: `x` goes at the first position whose
node `y` has `LB x ≤ LB y`, i.e. before every node with a bound equal to its own (the tie rule
of p. 403: a newly created node is put before an old node with the same lower bound). -/
def insertNode {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n)) :
    List (List (Fin n)) → List (List (Fin n))
  | [] => [x]
  | y :: ys => if LB x ≤ LB y then x :: y :: ys else y :: insertNode LB x ys

/-- One step of the branch-and-bound procedure of p. 402 with bound `LB`. If the list is empty
or its first node is terminal (`IsTerminal`), nothing changes (the procedure has stopped).
Otherwise (1) the first node `P` is removed, (2) its children are created, and (3) they are
inserted ranked into the rest of the list one at a time, in increasing index of the attached job,
each by `insertNode`. -/
def step {n : ℕ} (LB : List (Fin n) → ℝ) : List (List (Fin n)) → List (List (Fin n))
  | [] => []
  | P :: rest =>
    if IsTerminal P then P :: rest
    else (children P).foldl (fun L x => insertNode LB x L) rest

/-- The list after `k` steps of the procedure, starting from the list holding only the root
node `[]` (no job scheduled). The procedure stops the first time the first node of the list is
terminal; after that `step` leaves the list unchanged. -/
def run {n : ℕ} (LB : List (Fin n) → ℝ) (k : ℕ) : List (List (Fin n)) :=
  (step LB)^[k] [[]]

/-- The number of nodes created in the first `k` steps: the root, plus the children formed by
every step whose first node is non-terminal. -/
def createdCount {n : ℕ} (LB : List (Fin n) → ℝ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    createdCount LB k +
      match run LB k with
      | [] => 0
      | P :: _ => if IsTerminal P then 0 else (children P).length

end

end IgnallSchrage.Makespan


