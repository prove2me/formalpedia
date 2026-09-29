-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_LocalIncrementSup
-- name    : HighDimStat_MetricEntropy_LocalIncrementSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:51.81452+00:00
-- url     : https://prove2.me/theorems/dd498b6c-7cb6-4c71-92d4-a9010c049835
-- title:
--   The delta-localized supremum of process increments
-- statement:
--   The $\delta$-localized increment supremum $\sup_{\rho_X(\gamma,\gamma')\le\delta}(X_\gamma -
--   X_{\gamma'})$ appearing on the right-hand side of both Proposition 5.17 and Theorem 5.22, as a
--   function of the outcome $\omega$.
--
--   $$
--   \mathrm{LocalIncrementSup}(\delta,\omega) \;:=\; \sup_{\substack{\gamma,\gamma'\in T \\ \rho_X(\gamma,\gamma')\le\delta}} \big(X_\gamma(\omega) - X_{\gamma'}(\omega)\big).
--   $$
--
--   **Formalization Note** Realized as `⨆` over the subtype of pairs `(γ,γ')` with
--   `dist γ γ' ≤ δ`. This subtype is finite (a subtype of the finite type `T × T`) and, whenever
--   `δ ≥ 0`, nonempty (the diagonal pair `(θ,θ)` always has distance `0 ≤ δ`), so the value is the
--   true maximum rather than Mathlib's junk value `0`, throughout the range `δ ∈ [0,D]` this
--   mission's theorems use.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 135 (PDF p. 155), Eq. (5.33)

import Mathlib

namespace HighDimStat.MetricEntropy

/-- The `δ`-localized increment supremum `sup_{γ,γ' ∈ T, ρX(γ,γ')≤δ} (Xγ(ω) - Xγ'(ω))` appearing
on the right-hand side of Wainwright, *High-Dimensional Statistics* (2019), Proposition 5.17 and
Theorem 5.22 (Eqs. (5.33), (5.46)). Realized as `⨆` over the subtype of pairs within distance `δ`;
this subtype is always nonempty when `δ ≥ 0` and `T` is nonempty (the pair `(θ,θ)` has distance
`0 ≤ δ`), and finite since it is a subtype of the finite type `T × T`, so the value is the true
maximum, not the junk value `0`, whenever the hypotheses `δ ≥ 0` under which this definition is
used in this mission's theorems hold. -/
noncomputable def LocalIncrementSup {T Ω : Type*} [Fintype T] [PseudoMetricSpace T]
    (X : T → Ω → ℝ) (δ : ℝ) (ω : Ω) : ℝ :=
  ⨆ p : {p : T × T // dist p.1 p.2 ≤ δ}, (X p.1.1 ω - X p.1.2 ω)

end HighDimStat.MetricEntropy


