-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Node
-- name    : KallMayerSLP_Multistage_ex31Node
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:01.600996+00:00
-- url     : https://prove2.me/theorems/d2652b21-49db-4abe-abd9-aac882b16551
-- title:
--   Example 3.1: the nodes of the discretization
-- statement:
--   The nodes of the discretization of Example 3.1: one node in each of stages 1 and 2, and two nodes in stage 3, for the two cells of $\Xi^3$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.259 (PDF 268)

import Mathlib

namespace KallMayerSLP.Multistage

/-- The nodes of the discretization tree of Example 3.1 (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, Example 3.1, p.259, PDF 268): one node in each of stages 1 and 2,
and the two nodes of stage 3, `false` for `[0, 1/2)` and `true` for `[1/2, 1]`. The other values of
`t` are unused. -/
def ex31Node : ℕ → Type
  | 0 => Unit
  | 1 => Unit
  | 2 => Unit
  | 3 => Bool
  | _ + 4 => Empty

/-- The nodes of the tree of Example 3.1 are finite. -/
instance ex31Node.instFintype : ∀ t, Fintype (ex31Node t)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype Unit)
  | 2 => inferInstanceAs (Fintype Unit)
  | 3 => inferInstanceAs (Fintype Bool)
  | _ + 4 => inferInstanceAs (Fintype Empty)

end KallMayerSLP.Multistage


