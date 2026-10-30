-- Prove2me | Definitions.Def_PermBlockchain_Transfers_consistentSet
-- name    : PermBlockchain_Transfers_consistentSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:24.315529+00:00
-- url     : https://prove2.me/theorems/4d83087f-6d20-43b7-88ad-65d42630fbd4
-- title:
--   Type assignments consistent with a public history
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   For a strategy profile and a public history $x$, the consistent set is the set of type assignments $\theta\in\Theta$ under which the profile produces exactly the history $x$. It is nonempty exactly when $x$ is on the equilibrium path, and the uniform prior conditioned on $x$ is the uniform distribution on this set.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13); proof of Proposition 4.9, pp. 36–37 (PDF pp. 37–38)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Assignments
import Definitions.Def_PermBlockchain_Transfers_histOf
import Definitions.Def_PermBlockchain_Transfers_onPath

namespace PermBlockchain.Transfers

open Classical in
/-- **The type assignments that a strategy maps to a given public history.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13): "it is public knowledge that there are exactly m manufacturers
of each type, and consumers assume each manufacturer is equally likely to be of each type ex
ante"; with the proof of Proposition 4.9, pp. 36–37 (PDF pp. 37–38), where consumers infer
vertical types from prices.

**Formalization Note.** `consistentSet act x` is the set of `θ ∈ Θ` with
`histOf (onPath act θ) = x`; it is nonempty exactly when `x` is on the path of `act`. -/
noncomputable def consistentSet {m : ℕ} (act : Strategy m) (x : Hist m) :
    Finset (Mfr m → MType) :=
  (Assignments m).filter (fun θ' => histOf (onPath act θ') = x)

end PermBlockchain.Transfers


