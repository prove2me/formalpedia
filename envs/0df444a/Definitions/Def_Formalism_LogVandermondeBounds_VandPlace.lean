-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
-- name    : Formalism_LogVandermondeBounds_VandPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:17.18442+00:00
-- url     : https://prove2.me/theorems/dd0f10cb-54fb-4adc-a1a9-ecb1ed3f3862
-- title:
--   Vand Place
-- statement:
--   Definitions and structural lemmas for Vand Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/VandPlace.lean

import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioLowerBound
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
def VandPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ), 2 ≤ k → 1 ≤ m → 1 ≤ Δ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧
    ((k : ℝ) - 1) * ∑ j ∈ range m, Real.log (b j)
      - 2 * k * Real.log (8 * (x * Real.exp (x ^ ε))) - 2 * k * (1 + Real.log k)
      ≤ Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k)
end Formalism.LogVandermondeBounds.StandardLattice


