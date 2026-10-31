-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Xi
-- name    : KallMayerSLP_Multistage_ex31Xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:20.706994+00:00
-- url     : https://prove2.me/theorems/6d7a45db-7850-4a0f-af5a-f7288b16f902
-- title:
--   Example 3.1: the random vectors
-- statement:
--   The random vectors of Example 3.1, realized on $\Omega=\mathbb R^2$ as the coordinates: $\xi_2(\omega)=\omega_1$ and $\xi_3(\omega)=\omega_2$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.257 (PDF 266)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ex31Data

namespace KallMayerSLP.Multistage

/-- The random vectors of Example 3.1 (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, Example 3.1, p.257, PDF 266), as the coordinates of `ω = (ξ_2, ξ_3) ∈ ℝ²`: `ξ_2` is the
first and `ξ_3` the second. Only `t = 2, 3` are used. -/
def ex31Xi (t : ℕ) (ω : ℝ × ℝ) : Fin (ex31Data.r t) → ℝ :=
  fun _ => if t = 2 then ω.1 else ω.2

end KallMayerSLP.Multistage


