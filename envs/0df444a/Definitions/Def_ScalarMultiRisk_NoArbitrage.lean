-- Prove2me | Definitions.Def_ScalarMultiRisk_NoArbitrage
-- name    : ScalarMultiRisk_NoArbitrage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:11.346993+00:00
-- url     : https://prove2.me/theorems/8740085c-606e-425d-bbfa-f1677ec455f9
-- title:
--   Definition 4.3 — the no-arbitrage condition (NA)
-- statement:
--   A price process $S\in\mathcal S$ satisfies **(NA)** if
--
--   $$\Big[\sum_{s=0}^T\Gamma_s(S_s)\Big]\cap\big[-\Gamma_T(S_T)\big]\subseteq\Gamma_T(S_T).$$
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.3, p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_Gamma

open MeasureTheory

namespace ScalarMultiRisk

/-- **The no-arbitrage condition (NA).** arXiv:1807.10694v5, Definition 4.3, p.18:
`[∑_{s=0}^T Γ_s(S_s)] ∩ [−Γ_T(S_T)] ⊆ Γ_T(S_T)`.

**Formalization Note.** The Minkowski sum is taken on a.e.-classes. -/
def NoArbitrage {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (B : FilteredSpace Ω T)
    (S : Fin (T + 1) → Ω → Fin d → ℝ) : Prop :=
  ∀ X : Ω → Fin d → ℝ, (∃ f : Fin (T + 1) → Ω → Fin d → ℝ,
      (∀ s, f s ∈ Gamma B S s) ∧ X =ᵐ[B.P] ∑ s, f s) →
    -X ∈ Gamma B S (Fin.last T) → X ∈ Gamma B S (Fin.last T)

end ScalarMultiRisk


