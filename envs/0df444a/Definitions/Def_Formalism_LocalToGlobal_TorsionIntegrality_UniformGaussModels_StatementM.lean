-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementM
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementM
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:11.019285+00:00
-- url     : https://prove2.me/theorems/907babce-55d0-4aae-b970-4d0c2d98d702
-- title:
--   Statement M
-- statement:
--   Definitions and structural lemmas for Statement M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/StatementM.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)
def GoodModelUniform : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
    ∃ (c : ℂ) (hc : c ≠ 0), ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
      IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)
def ThetaZScale : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ),
    ω₀ / 2 ∉ L.lattice →
  ∀ (κ n : Type) [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ),
    MvPowerSeries.rescale (fun _ : n => ι c)
        (thetaZ p (Formalism.L2.Th1.F.scalePair L c hc) ι (c * ω₀) r (fun k i => c * s k i)) =
      thetaZ p L ι ω₀ r s
end Formalism.L2.Th1.Top


