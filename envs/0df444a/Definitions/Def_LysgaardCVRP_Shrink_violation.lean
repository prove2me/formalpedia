-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_violation
-- name    : LysgaardCVRP_Shrink_violation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:32:44.078956+00:00
-- url     : https://prove2.me/theorems/2405be96-6b4f-4ffe-bc3e-16f3b84a1243
-- title:
--   Violation $2\rho(T) - x(\delta(T))$ of a capacity-type inequality
-- statement:
--   Let $\rho$ assign a natural number $\rho(T)$ to every vertex set $T$, and consider the inequality $x(\delta(T)) \ge 2\rho(T)$. Its **violation** at the point $x$ is
--
--   $$2\rho(T) - x(\delta(T)).$$
--
--   The inequality is violated at $x$ exactly when the violation is positive, and one inequality is violated by at least as much as another when its violation is at least as large.
--
--   Taking $\rho = r$ (the bin-packing number) gives the capacity inequalities; taking $\rho = k$ (the rounded capacity bound) gives the rounded capacity inequalities.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), §2.1 and proof of Proposition 1

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut

namespace LysgaardCVRP.Shrink

/-- The violation of the capacity-type inequality $x(\delta(T)) \ge 2\rho(T)$ at the point $x$:
$2\rho(T) - x(\delta(T))$. The inequality is violated exactly when this number is positive, and a
larger number is a larger violation (Lysgaard, Letchford & Eglese, Math. Program. Ser. A 100
(2004), §2.1 and proof of Proposition 1, p. 426, PDF p. 4).

**Formalization Note.** The right-hand-side function `ρ` is a parameter: `ρ = binPackingNumber q Q`
gives the capacity inequalities (2) and `ρ = roundedCapacityBound q Q` the rounded capacity
inequalities. -/
def violation {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (ρ : Finset (Fin (n + 1)) → ℕ)
    (T : Finset (Fin (n + 1))) : ℝ :=
  2 * (ρ T : ℝ) - cut x T

end LysgaardCVRP.Shrink


