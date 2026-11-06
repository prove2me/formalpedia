-- Prove2me | Definitions.Def_NondualOpt_Tree
-- name    : NondualOpt_Tree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:40.80588+00:00
-- url     : https://prove2.me/theorems/d843acf4-46db-4f31-84ab-a896f3bf6679
-- title:
--   Depth-$n$ predictable tree
-- statement:
--   A **depth-$n$ predictable tree** over a set $Z$ is a sequence $z=(z_t)_{t=1}^n$ of maps $z_t:\{\pm1\}^{t-1}\to Z$: the node at round $t$ is chosen from the signs $\varepsilon_{<t}$ seen so far.
--
--   **Formalization Note** Signs are booleans (`true` for $+1$) and rounds are 0-based.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 1, p.8

import Mathlib

namespace NondualOpt

/-- A depth-`n` predictable tree over `Z`: a sequence `z = (z_t)_{t=1}^n` with
`z_t : {±1}^{t−1} → Z`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 1, p.8.

**Formalization Note.** Signs `±1` are `Bool` (`true ↦ +1`); rounds are `Fin n` (0-based), and the
node at round `t` reads the `t` signs before it. -/
abbrev Tree (Z : Type*) (n : ℕ) : Type _ :=
  (t : Fin n) → (Fin t → Bool) → Z

end NondualOpt


