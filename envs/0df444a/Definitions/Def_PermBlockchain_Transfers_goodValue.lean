-- Prove2me | Definitions.Def_PermBlockchain_Transfers_goodValue
-- name    : PermBlockchain_Transfers_goodValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:45.760995+00:00
-- url     : https://prove2.me/theorems/67b29273-b9c9-4524-b434-ccf2ae502583
-- title:
--   Consumer value $V_{ik}=\eta_{ik}+\xi_i$, displays (1)–(2)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The value to consumer $k$ of the good of manufacturer $i$ is
--   $$V_{ik}=\eta_{ik}+\xi_i,\qquad \eta_{ik}=H\cdot\mathcal I(q_i=t_k)+L\cdot\mathcal I(q_i\neq t_k),$$
--   where $0\le L<H$ and the vertical component is the number $h$ or $l$ with $0\le l<h$. The function returns $V$ for a manufacturer of type $\tau=(q,\xi)$ and a consumer of type $t$.
--
--   **Formalization Note** The inequalities $0\le L<H$, $0\le l<h$ are hypotheses of the theorems, not part of this definition.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 9 (PDF p. 10), displays (1)–(2)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType

namespace PermBlockchain.Transfers

/-- **Consumer value `V_ik = η_ik + ξ_i` of a good of manufacturer type `τ`, displays (1)–(2).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 9 (PDF p. 10), (1) `V_ik = η_ik + ξ_i` and (2)
`η_ik = H · I(q_i = t_k) + L · I(q_i ≠ t_k)`, where `0 ≤ L < H`; the vertical component is the
number `h` or `l` (`0 ≤ l < h`, p. 8).

`goodValue H L h l τ t` is the value to a consumer of type `t` of a good from a manufacturer of
type `τ = (q, ξ)`.

**Formalization Note.** The paper uses `h`, `l` both as labels and as the numbers `h > l ≥ 0`;
here the labels are `Vert.hi`, `Vert.lo` and the numbers are the real arguments `h`, `l`. The
standing inequalities are hypotheses of the statements, not part of this definition. -/
noncomputable def goodValue (H L h l : ℝ) (τ : MType) (t : Horiz) : ℝ :=
  (if τ.1 = t then H else L) + (match τ.2 with
    | .hi => h
    | .lo => l)

end PermBlockchain.Transfers


