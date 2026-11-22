-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
-- name    : Formalism_LogVandermondeBounds_UpperPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:36.668636+00:00
-- url     : https://prove2.me/theorems/ae8206ca-80a7-45aa-b8b9-01c4e4640609
-- title:
--   Upper Place
-- statement:
--   Definitions and structural lemmas for Upper Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/UpperPlace.lean

import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioUpperBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
def UpperPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ C₃ : ℝ) (u v b w : ℕ → ℝ),
    2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ≤ k → 1 ≤ Δ → 1 ≤ C₃ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    (∀ i j, i < j → j < k → 1 ≤ u i - u j) →
    0 < dimVN u k ∧ 0 < dTau k m (rowPar k v b) ∧
    Real.log (4 * dTau k m (rowPar k v b) *
        (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) * (v 0 + b (m - 1))) ^
          ((k - 1 + m / 2) * (m / 2))) - Real.log (dimVN u k)
      ≤ (k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10)
end Formalism.LogVandermondeBounds.StandardLattice


