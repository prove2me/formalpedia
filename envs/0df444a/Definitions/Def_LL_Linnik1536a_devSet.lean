-- Prove2me | Definitions.Def_LL_Linnik1536a_devSet
-- name    : LL_Linnik1536a_devSet
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-27T21:43:38.583429+00:00
-- url     : https://prove2.me/theorems/306a026a-6b63-4254-9b31-ffabe65bb63c
-- title:
--   The large deviation set of $G_L$
-- statement:
--   The set of $x\in[0,1]$ with $|G_L(x)|>dL$.

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
namespace LL_Linnik1536a
open Real MeasureTheory Finset

def devSet (L : ℕ) (d : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ d * L < ‖Gpow L x‖}

end LL_Linnik1536a


