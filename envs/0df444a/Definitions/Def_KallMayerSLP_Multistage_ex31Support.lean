-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Support
-- name    : KallMayerSLP_Multistage_ex31Support
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:07.092119+00:00
-- url     : https://prove2.me/theorems/ecff43ec-7377-4e00-a3e7-867e16551487
-- title:
--   Example 3.1: the intervals $\Xi^2=\Xi^3=[0,1]$
-- statement:
--   The intervals $\Xi^2=\Xi^3=[0,1]$ of Example 3.1, as subsets of $\mathbb R^1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.257 (PDF 266)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ex31Data

namespace KallMayerSLP.Multistage

/-- The intervals `Ξ^2 = Ξ^3 = [0, 1]` of Example 3.1 (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 3, Example 3.1, p.257, PDF 266), as subsets of `ℝ^1`. -/
def ex31Support (t : ℕ) : Set (Fin (ex31Data.r t) → ℝ) :=
  {v | ∀ i, v i ∈ Set.Icc (0 : ℝ) 1}

end KallMayerSLP.Multistage


