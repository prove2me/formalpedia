-- Prove2me | Definitions.Def_RoslingAssembly_Ypath
-- name    : RoslingAssembly_Ypath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:25.202274+00:00
-- url     : https://prove2.me/theorems/c35291e4-b1f6-44a7-afd2-eba4f868775b
-- title:
--   Echelon inventory position after ordering $Y_{it}$
-- statement:
--   $Y_{it}$ is the **echelon inventory position of item $i$ after ordering** in period $t$: the stock of $i$ on hand (including units already assembled into other items), plus units of $i$ in assembly or on order, minus the backlog of the end item. For $t\ge1$ it is the policy's decision; for $t\le 0$ it is a given pre-horizon history $Y_{it}$.
--
--   **Formalization Note** Periods are integers with the paper's numbering, so that expressions such as $Y_{k,t-l_k}$ are never truncated; Lean decision index $t-1$ is paper period $t$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib

namespace RoslingAssembly

/-- **Echelon inventory position after ordering**, Y_it (§1, p. 566). Rosling, *Optimal Inventory
Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 566
(unnumbered): "Y_it = echelon inventory position of item i after production decisions are made".

`Ypath Yh pol ω t i` is `Y_it` along the demand path `ω` for every period `t : ℤ`: the given
pre-horizon history `Yh t i` for `t ≤ 0`, and the policy's decision `pol (t − 1) ω i` for
`t ≥ 1`.

**Formalization Note.** Periods are integers with the paper's numbering (period 1 is the first
decision period), so that `t − 1` and `t − l_k` are never truncated; Lean decision index `t − 1`
is paper period `t`. The pre-horizon history (periods `t ≤ 0`, which (3) refers to through
`Y_{i,t−1}` and `Y_{k,t−l_k}`) is data. -/
def Ypath {N : ℕ} (Yh : ℤ → Fin N → ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (ω : ℕ → ℝ) (t : ℤ)
    (i : Fin N) : ℝ :=
  if t ≤ 0 then Yh t i else pol (t - 1).toNat ω i

end RoslingAssembly


