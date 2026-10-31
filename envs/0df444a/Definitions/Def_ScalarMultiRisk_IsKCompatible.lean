-- Prove2me | Definitions.Def_ScalarMultiRisk_IsKCompatible
-- name    : ScalarMultiRisk_IsKCompatible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:12.445896+00:00
-- url     : https://prove2.me/theorems/6acd8883-0697-4fca-993c-8b830b190492
-- title:
--   Definition 3.1 — $\mathbb K_t$-compatibility
-- statement:
--   A risk measure $\rho_t$ is **$\mathbb K_t$-compatible** if
--
--   $$\rho_t(X)=\operatorname*{ess\,inf}_{k\in\mathbb K_t}\rho_t(X-k)$$
--
--   for every $X\in L^\infty(\mathbb R^d)$: trading from time $t$ on cannot lower the capital requirement.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.1, p.7

import Mathlib
import Definitions.Def_ScalarMultiRisk_KK
import Definitions.Def_ScalarMultiRisk_LinftyFull
import Definitions.Def_ScalarMultiRisk_IsEssInf

open MeasureTheory

namespace ScalarMultiRisk

/-- **`𝕂_t`-compatibility.** arXiv:1807.10694v5, Definition 3.1, p.7:
`ρ_t(X) = ess inf_{k ∈ 𝕂_t} ρ_t(X − k)` for every `X ∈ L∞(ℝ^d)`. -/
def IsKCompatible {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (t : Fin (T + 1)) (r : (Ω → Fin d → ℝ) → Ω → ℝ) : Prop :=
  ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
    IsEssInf A.P (fun k : KK A t => fun ω => (r (X - k.1) ω : EReal)) fun ω => (r X ω : EReal)

end ScalarMultiRisk


