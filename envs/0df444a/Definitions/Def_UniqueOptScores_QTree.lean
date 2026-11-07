-- Prove2me | Definitions.Def_UniqueOptScores_QTree
-- name    : UniqueOptScores_QTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:20.589198+00:00
-- url     : https://prove2.me/theorems/9d30a6ba-9069-45f8-b70f-ef442dd61808
-- title:
--   Deterministic adaptive membership-query algorithms
-- statement:
--   A **query algorithm** with point set $\alpha$ and outputs in $\beta$ is a binary decision tree: it either returns a value $b \in \beta$, or queries whether a point $a \in \alpha$ is present and continues with the subtree of the Boolean reply. Under an oracle $O : \alpha \to \{0,1\}$ it follows the replies from the root to a leaf; $\mathrm{eval}(t, O)$ is the value at that leaf and $\mathrm{queries}(t, O)$ the list of queried points along the path (repeated queries are listed each time). The pair of a query and its reply forms the **query transcript**.
--
--   This models the paper's "total deterministic oracle algorithm" with adaptive queries and no running-time restriction beyond the query count.
--
--   **Formalization Note** A total deterministic algorithm that halts on every oracle is a finite decision tree (its tree of runs is well-founded and, by compactness, finite).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22; Section 2.3.1, pp.8–9 ("Queries may be adaptive")

import Mathlib

namespace UniqueOptScores

universe u v

/-- **Deterministic adaptive membership-query algorithms (decision trees).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "Each candidate is evaluated by a total deterministic oracle algorithm with
scores in {0, . . . , r} and at most q membership queries"; §2.3.1, p.8–9: "Queries may be
adaptive."

A `QTree α β` either returns a value of type `β` or asks whether the point `a : α` is present and
continues with the subtree of the Boolean reply. `eval t O` follows the replies of the oracle
`O : α → Bool`, and `queries t O` lists the queried points along that path, in order (a repeated
query is listed each time).

**Formalization Note.** A total deterministic oracle algorithm with no efficiency requirement is a
finite binary decision tree (it halts on every oracle, so its tree of runs is well-founded and, by
compactness, finite). The paper's query transcript is the list `queries t O` with the replies
`O a`. -/
inductive QTree (α : Type u) (β : Type v) : Type (max u v)
  /-- return a value -/
  | leaf (b : β) : QTree α β
  /-- query the point `a` and continue with the branch of the reply -/
  | query (a : α) (k : Bool → QTree α β) : QTree α β

namespace QTree

variable {α : Type u} {β : Type v}

/-- The value returned by the tree when the oracle answers according to `O`. -/
def eval : QTree α β → (α → Bool) → β
  | leaf b, _ => b
  | query a k, O => eval (k (O a)) O

/-- The queried points, in order, on the path selected by the oracle `O`. -/
def queries : QTree α β → (α → Bool) → List α
  | leaf _, _ => []
  | query a k, O => a :: queries (k (O a)) O

end QTree

end UniqueOptScores


