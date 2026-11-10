-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_SuccessEvent
-- name    : SmoothedPlanted_FFK_SuccessEvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:34:42.037719+00:00
-- url     : https://prove2.me/theorems/1708e375-dfc3-4650-ba66-85dfa7a96378
-- title:
--   Adaptive recovery success event
-- statement:
--   After sampling all outside constraints, require the recovery inequalities simultaneously for every planted assignment and every full instance extending that outside sample whose planted part is $\Delta$-consistent. The cut labels are unrestricted and may therefore depend on the sample. The algorithm receives only the full observable instance, $n,k$, and the nonnegative integer floor of $\Delta$. The event is evaluated under the outside product measure. Universal adversarial choices are inside this event, not outside the probability bound.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Adaptive recovery success event, printed p. 17 (PDF p. 19), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Encoding
import Definitions.Def_SmoothedPlanted_FFK_Consistent
import Definitions.Def_SmoothedPlanted_FFK_Rounding
import Definitions.Def_SmoothedPlanted_FFK_OutsideLaw

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

/-- Universal quantification after the outside draw permits an adaptive adversary. -/
def successEvent {q n : ℕ} (alg : RecoveryInput q → List Bool)
    (S : Finset (Fin n)) (k : ℕ) (Δ η : ℝ) : Set (CSP (↑Sᶜ) q) :=
  {ω | ∀ (σ : S → Fin q) (Y : CSP (Fin n) q),
    restrictCSP Y Sᶜ = ω → Consistent Y S σ Δ →
    Recovery S (outputSet n (alg ⟨n, k, ⌊Δ⌋₊, Y⟩)) k η}

end SmoothedPlanted.FFK


