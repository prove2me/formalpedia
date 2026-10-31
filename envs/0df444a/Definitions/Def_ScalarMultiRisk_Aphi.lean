-- Prove2me | Definitions.Def_ScalarMultiRisk_Aphi
-- name    : ScalarMultiRisk_Aphi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:52.608663+00:00
-- url     : https://prove2.me/theorems/4197d76b-20f6-4568-b41c-6e5a79c255da
-- title:
--   The acceptance set $A^\phi_t$
-- statement:
--   $A^\phi_t=\{Z\in L^\infty(\mathbb R)\mid\phi^S_t(Z)\le0\}$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proof of Corollary 4.10, p.22

import Mathlib
import Definitions.Def_ScalarMultiRisk_phiS
import Definitions.Def_ScalarMultiRisk_acceptanceSet

open MeasureTheory

namespace ScalarMultiRisk

/-- **The acceptance set `A^φ_t`.** arXiv:1807.10694v5, proof of Corollary 4.10, p.22:
`A^φ_t = {Z ∈ L∞(ℝ) | φ^S_t(Z) ≤ 0}`. -/
def Aphi {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t : Fin (T + 1)) : Set (Ω → ℝ) :=
  acceptanceSet A.toFilteredSpace (phiS A ρ S t)

end ScalarMultiRisk


