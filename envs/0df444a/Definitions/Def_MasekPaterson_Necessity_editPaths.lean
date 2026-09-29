-- Prove2me | Definitions.Def_MasekPaterson_Necessity_editPaths
-- name    : MasekPaterson_Necessity_editPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:18:51.204457+00:00
-- url     : https://prove2.me/theorems/eb9ad348-2849-4265-a4af-505252208650
-- title:
--   Edit paths through the edit matrix and their cost
-- statement:
--   Let $A$ and $B$ be strings over $\Sigma$, indexed from $1$, and let $\gamma$ be a cost function. The cells of the edit matrix are pairs $(p, q)$ of natural numbers, where $p$ indexes $A$ and $q$ indexes $B$. An **edit path** is a sequence of cells in which each successive cell increases $p$, $q$, or both by $1$; it need not start at $(0, 0)$. Its moves model edit operations:
--
--   1. $(p, q) \to (p + 1, q)$ deletes $A_{p+1}$ and costs $D_{A_{p+1}}$;
--   2. $(p, q) \to (p, q + 1)$ inserts $B_{q+1}$ and costs $I_{B_{q+1}}$;
--   3. $(p, q) \to (p + 1, q + 1)$ replaces $A_{p+1}$ by $B_{q+1}$ and costs $R_{A_{p+1}, B_{q+1}}$.
--
--   The **cost** of an edit path is the sum of the costs of its operations. The minimum cost of an edit path from a cell $x$ to a cell $y$ is the minimum of these costs over all edit paths from $x$ to $y$. The **eccentricity** of the cell $(i, j)$ is $|i - j|$.
--
--   Edit paths are the device of §4 of the paper: the example's edit distances are computed by comparing the costs of paths along the diagonals of the matrix.
--
--   **Formalization Note** An edit path is encoded by its starting cell and its list of moves; the visited cells include the starting and the last cell. The strings are passed as functions $\mathbb{N} \to \Sigma$ read from index $1$ (the value at $0$ is never used), which suits the infinite strings of §4. The minimum is written as `sInf`; when $y$ is reachable from $x$ the set of costs is nonempty and, for nonnegative costs, bounded below by $0$.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, pp. 24–25, Section 2.3 (Edit Paths); p. 27, Section 4.1 (eccentricity)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- A single move of an edit path through the edit matrix, whose entry `(p, q)` stands for
`δ_{p,q} = δ(γ, A^p, B^q)` (`p` indexes `A`, `q` indexes `B`):
* `del` goes from `(p, q)` to `(p + 1, q)` and deletes `A_{p+1}`;
* `ins` goes from `(p, q)` to `(p, q + 1)` and inserts `B_{q+1}`;
* `rep` goes from `(p, q)` to `(p + 1, q + 1)` and replaces `A_{p+1}` by `B_{q+1}`. -/
inductive Move
  | del
  | ins
  | rep
  deriving DecidableEq

/-- The matrix cell reached by a move from the cell `x = (p, q)`. -/
def Move.next : Move → ℕ × ℕ → ℕ × ℕ
  | .del, x => (x.1 + 1, x.2)
  | .ins, x => (x.1, x.2 + 1)
  | .rep, x => (x.1 + 1, x.2 + 1)

variable {α : Type*}

/-- The cost of a move made from the cell `x = (p, q)`, for the cost function `γ` and the
strings `A, B`, given as 1-based sequences of symbols (`A (p + 1)` is `A_{p+1}`):
`D_{A_{p+1}}` for a deletion, `I_{B_{q+1}}` for an insertion, `R_{A_{p+1}, B_{q+1}}` for a
replacement. -/
def Move.cost (γ : EditOp α → ℝ) (A B : ℕ → α) : Move → ℕ × ℕ → ℝ
  | .del, x => delCost γ (A (x.1 + 1))
  | .ins, x => insCost γ (B (x.2 + 1))
  | .rep, x => replCost γ (A (x.1 + 1)) (B (x.2 + 1))

/-- The last cell of the edit path that starts at `x` and makes the moves `ms` in order. -/
def pathEnd : ℕ × ℕ → List Move → ℕ × ℕ
  | x, [] => x
  | x, m :: ms => pathEnd (m.next x) ms

/-- All cells visited by the edit path that starts at `x` and makes the moves `ms`,
the starting cell and the last cell included. -/
def pathPoints : ℕ × ℕ → List Move → List (ℕ × ℕ)
  | x, [] => [x]
  | x, m :: ms => x :: pathPoints (m.next x) ms

/-- The cost of the edit path that starts at `x` and makes the moves `ms`: the sum of the
costs of its operations. -/
def pathCost (γ : EditOp α → ℝ) (A B : ℕ → α) : ℕ × ℕ → List Move → ℝ
  | _, [] => 0
  | x, m :: ms => m.cost γ A B x + pathCost γ A B (m.next x) ms

/-- The minimum cost of an edit path from the cell `x` to the cell `y` (the infimum of the
costs of all move lists from `x` that end at `y`). -/
noncomputable def pathMin (γ : EditOp α → ℝ) (A B : ℕ → α) (x y : ℕ × ℕ) : ℝ :=
  sInf {c : ℝ | ∃ ms : List Move, pathEnd x ms = y ∧ c = pathCost γ A B x ms}

/-- The eccentricity `|i - j|` of the cell `(i, j)`. -/
def ecc (x : ℕ × ℕ) : ℕ := ((x.1 : ℤ) - (x.2 : ℤ)).natAbs

end MasekPaterson.Necessity


