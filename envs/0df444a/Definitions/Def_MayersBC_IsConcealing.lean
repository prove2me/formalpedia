-- Prove2me | Definitions.Def_MayersBC_IsConcealing
-- name    : MayersBC_IsConcealing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:12.010393+00:00
-- url     : https://prove2.me/theorems/133f1c78-22da-44db-858f-419ef41e3dbe
-- title:
--   Bob's security criterion $|\mathrm{PE} - \tfrac12| \le \varepsilon$
-- statement:
--   Mayers' criterion for security against Bob: for a uniformly random bit, Bob's best guess after the commit phase must have probability of error within $\varepsilon$ of $\tfrac12$,
--
--   $$
--   |\mathrm{PE} - \tfrac12| \le \varepsilon .
--   $$
--
--   Here $\rho_0, \rho_1$ satisfy the criterion when **every** binary guess $\{Q, I - Q\}$ with $0 \le Q \le I$ on Bob's system has $|\mathrm{PE} - \tfrac12| \le \varepsilon$. The paper takes $\varepsilon = 1/25$.
--
--   This is the hypothesis of the paper's main argument: if the commitment conceals the bit in this sense, Alice can cheat.
--
--   **Formalization Note** Any guess Bob can compute, from any measurement, is a two-outcome measurement, so this covers his best guess. Conversely the best guess has $\mathrm{PE} \le \tfrac12$ (take $Q = 0$), and exchanging $Q$ with $I - Q$ replaces $\mathrm{PE}$ by $1 - \mathrm{PE}$, so the condition on the best guess is equivalent to the condition on every $Q$.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersBC_guessError
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.7, the criterion for security against Bob:
"Let X be the random variable which represents the best guess for the bit b chosen by Alice that
can be made by Bob after the commit phase. … The criteria is that, for a perfectly random bit b
chosen by Alice, we must have |PE − 1/2| ≤ ε." Here: for **every** two-outcome measurement
`{Q, I − Q}` on the photons (every effect `0 ≤ Q ≤ I`), `|PE − ½| ≤ ε`.

**Formalization Note.** A guess computed from any measurement is a two-outcome measurement, so
quantifying over every effect `Q` covers the best guess. Conversely the best guess has
`PE ≤ ½` (take `Q = 0`), and `PE` of `{I − Q, Q}` is `1 − PE` of `{Q, I − Q}`, so
`|PE_best − ½| ≤ ε` holds exactly when `|PE_Q − ½| ≤ ε` for all `Q`. The paper's value is
`ε = 1/25`; here `ε` is a parameter. -/
def IsConcealing {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℝ) (ρ0 ρ1 : Matrix ι ι ℂ) : Prop :=
  ∀ Q : Matrix ι ι ℂ, IsEffect Q → |guessError ρ0 ρ1 Q - 1 / 2| ≤ ε

end MayersBC


