-- Prove2me | Definitions.Def_CentralityGame_IsPath
-- name    : CentralityGame_IsPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:26.934154+00:00
-- url     : https://prove2.me/theorems/2ef527dd-f94a-4b0d-849c-02215eb2a076
-- title:
--   Path
-- statement:
--   A **path** is a walk $(r_0,r_1,\dots,r_l)$ such that $r_h\ne r_k$ for every $0\le h<k\le l$, except for possibly $r_0=r_l$.
--
--   Paths are the objects that a cut-set must intersect, and Theorem 1 produces a path along which hitting times decrease.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.5

import Mathlib
import Definitions.Def_CentralityGame_IsWalk

namespace CentralityGame

/-- A **path** (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.5): a walk `(r_0, …, r_l)` such that `r_h ≠ r_k` for
every `0 ≤ h < k ≤ l`, except for possibly `r_0 = r_l`. -/
def IsPath {V : Type*} (N : V → Finset V) {l : ℕ} (r : Fin (l + 1) → V) : Prop :=
  IsWalk N r ∧ ∀ h k : Fin (l + 1), h < k → r h = r k → h = 0 ∧ k = Fin.last l

end CentralityGame


