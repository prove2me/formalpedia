-- Prove2me | Definitions.Def_LL_Decomp1526a_evenBlock
-- name    : LL_Decomp1526a_evenBlock
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:03:26.158721+00:00
-- url     : https://prove2.me/theorems/2035f080-638c-4061-93a1-6ab51a2c5a3d
-- title:
--   Even integers of a dyadic block
-- statement:
--   For real $X$, the finite set of even natural numbers $N$ with $\lfloor X\rfloor<N\le\lfloor 2X\rfloor$.

import Mathlib

namespace LL_Decomp1526a

noncomputable section

open Finset Real
open scoped Chebyshev Classical

def evenBlock (X : ℝ) : Finset ℕ := (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter Even

end

end LL_Decomp1526a


