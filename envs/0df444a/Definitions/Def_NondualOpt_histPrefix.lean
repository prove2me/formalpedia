-- Prove2me | Definitions.Def_NondualOpt_histPrefix
-- name    : NondualOpt_histPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:42.973206+00:00
-- url     : https://prove2.me/theorems/4b161ad4-3d31-4c13-81bb-f39348ff1370
-- title:
--   The prefix $a_{<t}$ of a finite sequence
-- statement:
--   For a finite sequence $a=(a_1,\dots,a_n)$ and a round $t$, the **prefix** $a_{<t}=(a_1,\dots,a_{t-1})$ lists the entries before round $t$. It is used for sign paths $\varepsilon_{<t}$ in trees and for loss histories $\ell_{1:t-1}$.
--
--   **Formalization Note** Rounds are 0-based: the prefix at round $t$ is the first $t$ entries.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 1, p.8

import Mathlib

namespace NondualOpt

/-- The prefix `a_{<t} = (a_1, …, a_{t−1})` of a finite sequence `a = (a_1, …, a_n)` before
round `t` (with 0-based rounds: the first `t` entries). Used for sign paths `ε_{<t}`
(Definition 1) and loss histories `ℓ_{1:t−1}` (Proposition 4).
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 1, p.8. -/
def histPrefix {α : Type*} {n : ℕ} (a : Fin n → α) (t : Fin n) : Fin t → α :=
  fun i => a (Fin.castLE (Nat.le_of_lt t.isLt) i)

end NondualOpt


