-- Prove2me | Definitions.Def_ScalarMultiRisk_phiReal
-- name    : ScalarMultiRisk_phiReal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:20.881538+00:00
-- url     : https://prove2.me/theorems/cfe8d2fa-26bf-4a08-9096-852c5438990e
-- title:
--   The real version of $\phi^S_t$
-- statement:
--   $\phi^S_t$ read as a real-valued map, which is how Proposition 4.9 treats it for $S\in\mathcal S_t$.
--
--   **Formalization Note** The real part sends $\pm\infty$ to $0$. Proposition 4.9 states that $\phi^S_t(Z)$ is a.s. equal to this real version, so that value occurs only on a null set.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.9, p.22

import Mathlib
import Definitions.Def_ScalarMultiRisk_phiS

open MeasureTheory

namespace ScalarMultiRisk

/-- **The real version of `φ^S_t`.** Proposition 4.9 of arXiv:1807.10694v5, p.22, says that
`φ^S_t` is a map into `L∞_t(ℝ)`; this is the same map with its values read as reals.

**Formalization Note.** `EReal.toReal` sends `±∞` to `0`; Proposition 4.9 states alongside that
`φ^S_t(Z)` is a.s. equal to this real version, so that junk value is confined to a null set. -/
noncomputable def phiReal {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (S : Fin (T + 1) → Ω → Fin d → ℝ) (t : Fin (T + 1)) (Z : Ω → ℝ) : Ω → ℝ :=
  fun ω => (phiS A ρ S t Z ω).toReal

end ScalarMultiRisk


