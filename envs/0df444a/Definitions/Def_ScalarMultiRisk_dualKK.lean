-- Prove2me | Definitions.Def_ScalarMultiRisk_dualKK
-- name    : ScalarMultiRisk_dualKK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:38.463007+00:00
-- url     : https://prove2.me/theorems/129aa7bc-c930-4578-a47d-f52ac74e767c
-- title:
--   The dual cone $\mathbb K_T^+$ in $L^1$
-- statement:
--   $\mathbb K_T^+=\{v\in L^1(\mathbb R^d)\mid\mathbb E[v^{\mathsf T}u]\ge0\ \text{for all }u\in\mathbb K_T\}$, with $\mathbb K_T=L^\infty_T(K_T)$.
--
--   **Formalization Note** $v$ is integrable by definition and $u$ is bounded, so $v^{\mathsf T}u$ is integrable.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §2, p.6

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market
import Definitions.Def_ScalarMultiRisk_Linfty

open MeasureTheory Matrix

namespace ScalarMultiRisk

/-- **The dual cone `𝕂_T⁺`.** arXiv:1807.10694v5, §2, p.6:
`C⁺ = {v ∈ L¹_t(ℝ^d) | 𝔼[vᵀu] ≥ 0 ∀ u ∈ C}`, for `C = 𝕂_T = L∞_T(K_T)`.

**Formalization Note.** The expectation is a Bochner integral, and `v` is integrable by
definition, while `u` is bounded, so `vᵀu` is integrable. -/
def dualKK {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d) :
    Set (Ω → Fin d → ℝ) :=
  {v | Integrable v A.P ∧
    ∀ u ∈ Linfty A.toFilteredSpace (Fin.last T)
      (fun ω => (A.K (Fin.last T) ω : Set (Fin d → ℝ))),
      0 ≤ ∫ ω, v ω ⬝ᵥ u ω ∂A.P}

end ScalarMultiRisk


