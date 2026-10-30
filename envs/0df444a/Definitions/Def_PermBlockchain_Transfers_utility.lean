-- Prove2me | Definitions.Def_PermBlockchain_Transfers_utility
-- name    : PermBlockchain_Transfers_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:12.021208+00:00
-- url     : https://prove2.me/theorems/5830303e-08a4-464f-81c4-500c923f610a
-- title:
--   Consumer utility $u_{ik}$, display (6)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The utility of consumer $k$ from buying from manufacturer $i$ is
--   $$u_{ik}=\mathbb E[V_{ik}\mid\mathcal F_k]-P_i,$$
--   with the price $P_i$ read from the public history.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), display (6)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_expValue
import Definitions.Def_PermBlockchain_Transfers_Hist

namespace PermBlockchain.Transfers

/-- **Consumer utility `u_ik = E[V_ik | F_k] − P_i`, display (6).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), (6). The price `P_i` is read off the public history `x`. -/
noncomputable def utility {m : ℕ} (H L h l : ℝ) (β' : (Mfr m → MType) → ℝ) (x : Hist m)
    (i : Mfr m) (t : Horiz) : ℝ :=
  expValue H L h l β' i t - x.2 i

end PermBlockchain.Transfers


