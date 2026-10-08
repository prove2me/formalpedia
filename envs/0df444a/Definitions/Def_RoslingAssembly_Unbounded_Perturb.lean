-- Prove2me | Definitions.Def_RoslingAssembly_Unbounded_Perturb
-- name    : RoslingAssembly_Unbounded_Perturb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:47.617059+00:00
-- url     : https://prove2.me/theorems/da29e692-f03b-487b-be74-0190b39091bd
-- title:
--   The one-more-unit policy of the proof of Theorem 4(i): δ extra units of the subsystem {i} ∪ B(i), held forever
-- statement:
--   Fix an item $i$ and the subsystem $\{i\} \cup B(i)$ formed by $i$ and all its predecessors. Let
--   $$M_m = \max_{k \in \{i\} \cup B(i)} M_k$$
--   be the greatest total lead time in the subsystem. Given a policy $\pi$ and an amount $\delta$, the perturbed policy $\pi^\delta$ makes the same decisions as $\pi$, except that for every item $k \in \{i\} \cup B(i)$ it raises $Y_{kt}$ by $\delta$ in every period
--   $$t \ge M_m - M_k + 1 .$$
--   In other words, $\delta$ more units of $k$ are ordered in period $M_m - M_k + 1$ and held in stock forever. Since $M_k = l_k + M_j$ for $k \in P(j)$, the extra units of a predecessor $k$ ordered in period $M_m - M_k + 1$ arrive in period $M_m - M_j + 1$, exactly when $j$ orders its own extra units; and $\delta$ more units of item $i$ are ordered in period $M_m - M_i + 1$.
--
--   This is the alternative policy of the proof of Theorem 4(i), with $\delta$ units in place of the paper's one unit, so that arbitrarily many units can be added.
--
--   **Formalization Note.** In Lean periods ($k' = t - 1$) the increment applies when $k' \ge M_m - M_k$. When $B(i) = \emptyset$, $M_m = M_i$ and the increment starts in period 1. The paper takes $\delta = 1$; the statements of the mission use $\delta \ge 0$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 578, Appendix B, Proof of Theorem 4 (i), first three sentences

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model

namespace RoslingAssembly.Unbounded

namespace Model

variable (S : Model)

/-- The greatest total lead time `max_{k ∈ {i} ∪ B(i)} M_k` in the subsystem `{i} ∪ B(i)`
(M_m of the proof of Theorem 4(i), p. 578). -/
noncomputable def Mmax (i : ℕ) : ℕ := (insert i (S.B i)).sup S.M

/-- The "one more unit" policy of the proof of Theorem 4(i) (p. 578), with `δ` extra units:
for every item `k ∈ {i} ∪ B(i)` it raises Y_kt by `δ` in every period `t ≥ M_m − M_k + 1`
(Lean period `k' ≥ M_m − M_k`), so that the extra units are ordered of `k` in period
`M_m − M_k + 1` and held in stock forever; all other decisions are those of `π`. -/
noncomputable def perturb (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) : RoslingAssembly.SeriesEquiv.Policy :=
  fun k' x j => π k' x j + if j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ k' then δ else 0

end Model

end RoslingAssembly.Unbounded


