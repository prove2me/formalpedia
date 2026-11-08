-- Prove2me | Definitions.Def_FairFacilityLoc_scoreBalancedOver
-- name    : FairFacilityLoc_scoreBalancedOver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:46.206141+00:00
-- url     : https://prove2.me/theorems/0296a1a3-4ff7-4f22-a0cf-7a449226c42b
-- title:
--   The Score-Balanced mechanism over a family
-- statement:
--   The cut at $t$ **wins over** $W$ if its left set $S=L_r(t;x)$ satisfies $\sigma_W(S)\ge\sigma_W(N\setminus S)$. The mechanism returns in each coordinate the smallest report at which the cut wins over $W$. The penalty parameter is $b_d$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §3.3, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_cutOutput
import Definitions.Def_FairFacilityLoc_weightScore

namespace FairFacilityLoc

/-- **Winning sets over a family**, §3.3, p.47, PDF p.49: `σ_W(S) ≥ σ_W(N ∖ S)` (Yan, Zhou, manuscript, sha256
642a1268…). -/
def IsWinningOver (d : ℕ) {n : ℕ} (W : Finset (Fin n → ℝ)) (S : Finset (Fin n)) : Prop :=
  maxWeightScore (penalty d) W Sᶜ ≤ maxWeightScore (penalty d) W S

/-- **The Score-Balanced mechanism over a family `W`**, §3.3, p.47, PDF p.49: the smallest report at which the
cut wins over `W`. Every statement has the clause or the hypotheses that make the minimum exist. -/
noncomputable def scoreBalancedOver (d : ℕ) {n : ℕ} (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) : GeoSemialgCSP.E d :=
  cutOutput (fun _ S => IsWinningOver d W S) x

end FairFacilityLoc


