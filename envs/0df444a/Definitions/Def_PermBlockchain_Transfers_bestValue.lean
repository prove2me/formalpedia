-- Prove2me | Definitions.Def_PermBlockchain_Transfers_bestValue
-- name    : PermBlockchain_Transfers_bestValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:37.229999+00:00
-- url     : https://prove2.me/theorems/c378b212-cc50-4680-b394-ab1e3a12b205
-- title:
--   Best value $\max\{\max_i u_{ik},\phi_k\}$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The best value available to a consumer with outside option $\phi_k$ is
--   $$\max\Bigl\{\max_{i\in M}u_{ik},\ \phi_k\Bigr\},$$
--   the integrand of the consumer's fee problem (16).
--
--   **Formalization Note** It is computed as a fold of $\max$ over the finite set of manufacturers, so it is always the true maximum.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), display (16)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_utility

namespace PermBlockchain.Transfers

/-- **The consumer's best value `max{max_{i∈M} u_ik, φ_k}`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, p. 20 (PDF p. 21), the integrand of (16); §3.1, p. 12 (PDF p. 13).

**Formalization Note.** Written as a fold of `max` over the finite set of manufacturers starting
from `φ`, so it is always the true maximum (no `⨆` junk value). -/
noncomputable def bestValue {m : ℕ} (H L h l : ℝ) (β' : (Mfr m → MType) → ℝ) (x : Hist m)
    (t : Horiz) (φ : ℝ) : ℝ :=
  Finset.univ.fold max φ (fun i => utility H L h l β' x i t)

end PermBlockchain.Transfers


