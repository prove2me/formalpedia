-- Prove2me | Definitions.Def_PermBlockchain_Transfers_optionValue
-- name    : PermBlockchain_Transfers_optionValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:34.006646+00:00
-- url     : https://prove2.me/theorems/ef04fc3e-53ad-485b-9036-086a8d8db6cc
-- title:
--   Value of a purchase option
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The value of the outside option is $\phi_k$ and the value of buying from manufacturer $i$ is $u_{ik}$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_utility

namespace PermBlockchain.Transfers

/-- **The value of a purchase option: `φ_k` for the outside option, `u_ik` for manufacturer `i`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13). -/
noncomputable def optionValue {m : ℕ} (H L h l : ℝ) (β' : (Mfr m → MType) → ℝ) (x : Hist m)
    (t : Horiz) (φ : ℝ) : Option (Mfr m) → ℝ
  | none => φ
  | some i => utility H L h l β' x i t

end PermBlockchain.Transfers


