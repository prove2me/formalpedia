-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HCFdeg
-- name    : Formalism_PeriodIntegrals_HCFdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:23.37027+00:00
-- url     : https://prove2.me/theorems/61057357-66e8-4036-b7ce-7959d318c352
-- title:
--   HCFdeg
-- statement:
--   Definitions and structural lemmas for HCFdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HCFdeg.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open PI.UpqRep
def HCFdeg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      IsFdeg (muG ε) σ (c * fdegHC lam)
end PI


