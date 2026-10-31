-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Cell
-- name    : KallMayerSLP_Multistage_ex31Cell
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:17:09.726545+00:00
-- url     : https://prove2.me/theorems/fe674d13-e79f-454f-b216-0471eee8d27c
-- title:
--   Example 3.1: the cells of the discretization
-- statement:
--   The partitions of Example 3.1: the trivial partition $\{\Xi^2\}$ at stage 2, and $\{[0,\tfrac12),[\tfrac12,1]\}$ at stage 3.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.259 (PDF 268)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ex31Support
import Definitions.Def_KallMayerSLP_Multistage_ex31Node

namespace KallMayerSLP.Multistage

/-- The cells of the discretization of Example 3.1 (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 3, Example 3.1, p.259, PDF 268): the trivial partition `{Ξ^2}` at stage 2 and
`{[0, 1/2), [1/2, 1]}` at stage 3. -/
def ex31Cell : ∀ t, ex31Node t → Set (Fin (ex31Data.r t) → ℝ)
  | 0, _ => Set.univ
  | 1, _ => Set.univ
  | 2, _ => ex31Support 2
  | 3, b => {v | ∀ i, v i ∈ cond (show Bool from b) (Set.Icc (1 / 2 : ℝ) 1) (Set.Ico (0 : ℝ) (1 / 2))}
  | _ + 4, e => (e : Empty).elim

end KallMayerSLP.Multistage


