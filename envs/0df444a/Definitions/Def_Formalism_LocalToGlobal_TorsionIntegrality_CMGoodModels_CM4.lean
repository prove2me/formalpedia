-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_CM4
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_CM4
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:33.563847+00:00
-- url     : https://prove2.me/theorems/f8ff8584-d7fc-486e-bfb9-a08b515e2f62
-- title:
--   CM4
-- statement:
--   Definitions and structural lemmas for CM4, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/CM4.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.CM
def CM4 : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
      (lam ^ 4 * ι L.g₂) ∈ MaximalUnramifiedExtension l → (lam ^ 6 * ι L.g₃) ∈ MaximalUnramifiedExtension l → ‖lam ^ 4 * ι L.g₂‖ ≤ 1 →
      ‖lam ^ 6 * ι L.g₃‖ ≤ 1 → ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      lam ^ 2 * ι (L.weierstrassP z) ∈ MaximalUnramifiedExtension l ∧ lam ^ 3 * ι (L.derivWeierstrassP z) ∈ MaximalUnramifiedExtension l ∧
        ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1
end Formalism.L2.Th1.CM


