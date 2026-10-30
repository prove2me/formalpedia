-- Prove2me | Definitions.Def_PermBlockchain_Transfers_expValue
-- name    : PermBlockchain_Transfers_expValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:15.98223+00:00
-- url     : https://prove2.me/theorems/72f98952-7c2d-42d2-955e-a7ab7b2be6a2
-- title:
--   Expected good value $\mathbb E[V_{ik}\mid\mathcal F_k]$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   Under a belief $\beta'$ on type assignments, the expected value of manufacturer $i$'s good to a consumer of type $t$ is
--   $$\mathbb E[V_{ik}\mid\mathcal F_k]=\sum_{\theta'\in\Theta}\beta'(\theta')\,V(\theta'(i),t).$$
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), display (6)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Assignments
import Definitions.Def_PermBlockchain_Transfers_goodValue

namespace PermBlockchain.Transfers

/-- **Expected good value `E[V_ik | F_k]` under a belief, display (6).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), (6): `u_ik = E[V_ik | F_k] − P_i`.

`expValue H L h l β' i t` is the expectation, under the distribution `β'` on type assignments, of
the value `goodValue H L h l (θ' i) t` of manufacturer `i`'s good to a consumer of type `t`. -/
noncomputable def expValue {m : ℕ} (H L h l : ℝ) (β' : (Mfr m → MType) → ℝ) (i : Mfr m)
    (t : Horiz) : ℝ :=
  ∑ θ' ∈ Assignments m, β' θ' * goodValue H L h l (θ' i) t

end PermBlockchain.Transfers


