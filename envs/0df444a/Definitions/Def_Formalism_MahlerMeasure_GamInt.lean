-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_GamInt
-- name    : Formalism_MahlerMeasure_GamInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:22.106847+00:00
-- url     : https://prove2.me/theorems/03f90b5d-c1af-4d7a-b653-ed09dd9491f0
-- title:
--   Gam Int
-- statement:
--   Definitions and structural lemmas for Gam Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/GamInt.lean

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
def GamInt : Prop :=
  ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ PolZ p r LL → f' ∈ PolZ p r LL →
    ∃ c : ℕ → ℤ_[p], ∀ n, LL.total ≤ n →
      ((p : ℚ_[p]) ^ (C * (N + 3) * r ^ 2 * (Nat.log p (LL.total + LL.deg (Fin.last N) + r) + 1))) *
          tieGam p LL ρ z n f f' =
        ∑ i ∈ range (LL.total + LL.deg (Fin.last N) + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])
end Formalism.GM.M


