-- Prove2me | Definitions.Def_ScalarMultiRisk_riskAcceptance
-- name    : ScalarMultiRisk_riskAcceptance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:56.786985+00:00
-- url     : https://prove2.me/theorems/51746c44-486e-4a29-bafc-9f8940a9ea3f
-- title:
--   The acceptance set $A_t$ of $\rho_t$
-- statement:
--   $A_t=\{X\in L^\infty(\mathbb R^d)\mid\rho_t(X)\le0\text{ a.s.}\}$ is the set of portfolios that need no capital at time $t$.
--
--   **Formalization Note** The paper defines $A_t=\{X\mid0\in R_t(X)\}$; the two agree by Theorem 3.2.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Assumption 3.3, p.8

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market
import Definitions.Def_ScalarMultiRisk_acceptanceSet

open MeasureTheory

namespace ScalarMultiRisk

/-- **The acceptance set `A_t`.** arXiv:1807.10694v5, Assumption 3.3, p.8:
`A_t = {X ∈ L∞(ℝ^d) | 0 ∈ R_t(X)}`, which is `{X ∈ L∞(ℝ^d) | ρ_t(X) ≤ 0 a.s.}` because
`R_t(X) = (ρ_t(X) + L∞_t(ℝ₊))e₁` (Theorem 3.2). -/
def riskAcceptance {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (t : Fin (T + 1)) : Set (Ω → Fin d → ℝ) :=
  acceptanceSet A.toFilteredSpace fun X ω => (ρ t X ω : EReal)

end ScalarMultiRisk


