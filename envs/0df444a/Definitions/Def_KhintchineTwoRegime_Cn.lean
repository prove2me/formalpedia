-- Prove2me | Definitions.Def_KhintchineTwoRegime_Cn
-- name    : KhintchineTwoRegime_Cn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:32.227699+00:00
-- url     : https://prove2.me/theorems/adb09ca1-c9f0-4438-9680-ae70bcc87aa8
-- title:
--   $\mathcal C_n(\tau)$: proper unit vectors at distance $\tau$ from $\omega^*$
-- statement:
--   For $\tau\in\mathbb R$,
--   $$
--   \mathcal C_n(\tau)=\{\omega\in\mathbb R^n:\ \|\omega-\omega^*\|_2=\tau,\ \omega\in\mathfrak C\}
--   $$
--   is the set of proper unit vectors at Euclidean distance $\tau$ from the classical minimizer $\omega^*$. The two-regime inequality bounds $K_n$ from below on each $\mathcal C_n(\tau)$. For a value of $\tau$ that is not an admissible distance the set is empty.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4 (also §1.1, p.2)

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_omegaStar
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- `C_n(τ) = {ω : ‖ω − ω*‖₂ = τ, ω ∈ C}`, the proper unit vectors of `ℝⁿ` at Euclidean
distance `τ` from `ω*` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4; also §1.1, p.2).

**Formalization Note** The distance is the Euclidean norm `l2Norm`; `C` is `IsProper`. For
a `τ` that is not an admissible distance the set is empty. -/
def Cn (n : ℕ) (τ : ℝ) : Set (Fin n → ℝ) :=
  {ω | IsProper ω ∧ l2Norm (ω - omegaStar n) = τ}

end KhintchineTwoRegime


