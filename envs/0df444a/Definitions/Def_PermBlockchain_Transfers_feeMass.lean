-- Prove2me | Definitions.Def_PermBlockchain_Transfers_feeMass
-- name    : PermBlockchain_Transfers_feeMass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:01:16.833708+00:00
-- url     : https://prove2.me/theorems/542e3318-029b-4c8f-a10f-8e8414d10b55
-- title:
--   Fee mass $\mu_\kappa$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The mass of consumers who pay the fee at history $x$ is
--   $$\mu_\kappa=\mu(\{k:b_k=1\})=\frac12\sum_{t\in\{A,B\}}G\bigl(\{\phi:\text{fee}(t,\phi,x)=1\}\bigr).$$
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_FeeRule

namespace PermBlockchain.Transfers

/-- **The mass `μ_κ = μ({k : b_k = 1})` of consumers who pay the fee.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 21 (PDF p. 22): "the measure µκ of the set of consumers who pay the access fee κ
is given by µκ = µ({k : bk = 1})".

**Formalization Note.** As in `demand`, consumers are (uniform on `{A, B}`) ⊗ `ν`. -/
noncomputable def feeMass {m : ℕ} (ν : MeasureTheory.Measure ℝ) (fee : FeeRule m) (x : Hist m) :
    ℝ :=
  (1 / 2 : ℝ) * ∑ t : Horiz, (ν {φ : ℝ | fee t φ x = true}).toReal

end PermBlockchain.Transfers


