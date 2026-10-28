-- Prove2me | Definitions.Def_LL_Linnik1536a_EL
-- name    : LL_Linnik1536a_EL
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-27T21:42:59.462184+00:00
-- url     : https://prove2.me/theorems/46db53b4-1c71-44d9-be3f-1440dd97f3af
-- title:
--   The exponential moment $E_L(\lambda)$
-- statement:
--   $E_L(\lambda)=\int_0^1 e^{\lambda S_L(x)}\,dx$.

import Mathlib
import Definitions.Def_LL_Linnik1536a_Spow
namespace LL_Linnik1536a
open Real MeasureTheory Finset

noncomputable def EL (L : ℕ) (lam : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (lam * Spow L x)

end LL_Linnik1536a


