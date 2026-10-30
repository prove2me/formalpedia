-- Prove2me | Definitions.Def_BBPSSW_Distill_bxorTable
-- name    : BBPSSW_Distill_bxorTable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:12.802918+00:00
-- url     : https://prove2.me/theorems/0c06b99e-db98-4484-a263-bded4d6f815c
-- title:
--   Table (6): BXOR on pairs of Bell states
-- statement:
--   The paper's Table (6) of how BXOR maps (source, target) Bell labels, phases omitted ("n.c." = no change):
--
--   | source | target | source after | target after |
--   |---|---|---|---|
--   | $\Phi^\pm$ | $\Phi^+$ | n.c. | n.c. |
--   | $\Psi^\pm$ | $\Phi^+$ | n.c. | $\Psi^+$ |
--   | $\Psi^\pm$ | $\Psi^+$ | n.c. | $\Phi^+$ |
--   | $\Phi^\pm$ | $\Psi^+$ | n.c. | n.c. |
--   | $\Phi^\pm$ | $\Phi^-$ | $\Phi^\mp$ | n.c. |
--   | $\Psi^\pm$ | $\Phi^-$ | $\Psi^\mp$ | $\Psi^-$ |
--   | $\Psi^\pm$ | $\Psi^-$ | $\Psi^\mp$ | $\Phi^-$ |
--   | $\Phi^\pm$ | $\Psi^-$ | $\Phi^\mp$ | n.c. |
--
--   The definition transcribes the table row by row (16 cases). The theorem `bxor_bell_table` states that BXOR acts this way.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Table (6), p. 2

import Mathlib
import Definitions.Def_BBPSSW_Distill_BellLabel

namespace BBPSSW.Distill

/-- **Table (6): the action of BXOR on pairs of Bell states.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Table (6), p. 2 ("The result of applying BXOR to other combinations of Bell states is
shown below, omitting phases"; columns Before: Source, Target | After: Source, Target;
"n.c. = no change"):

| Before: source | target | After: source | target |
|---|---|---|---|
| Φ± | Φ+ | n.c. | n.c. |
| Ψ± | Φ+ | n.c. | Ψ+ |
| Ψ± | Ψ+ | n.c. | Φ+ |
| Φ± | Ψ+ | n.c. | n.c. |
| Φ± | Φ− | Φ∓ | n.c. |
| Ψ± | Φ− | Ψ∓ | Ψ− |
| Ψ± | Ψ− | Ψ∓ | Φ− |
| Φ± | Ψ− | Φ∓ | n.c. |

`bxorTable s t = (s', t')`: the source and target labels after BXOR, transcribed row by row
(each "±" row is two cases). The theorem `bxor_bell_table` states that `bxor` acts this way
up to phase. -/
def bxorTable : BellLabel → BellLabel → BellLabel × BellLabel
  | .phiPlus, .phiPlus => (.phiPlus, .phiPlus)
  | .phiMinus, .phiPlus => (.phiMinus, .phiPlus)
  | .psiPlus, .phiPlus => (.psiPlus, .psiPlus)
  | .psiMinus, .phiPlus => (.psiMinus, .psiPlus)
  | .psiPlus, .psiPlus => (.psiPlus, .phiPlus)
  | .psiMinus, .psiPlus => (.psiMinus, .phiPlus)
  | .phiPlus, .psiPlus => (.phiPlus, .psiPlus)
  | .phiMinus, .psiPlus => (.phiMinus, .psiPlus)
  | .phiPlus, .phiMinus => (.phiMinus, .phiMinus)
  | .phiMinus, .phiMinus => (.phiPlus, .phiMinus)
  | .psiPlus, .phiMinus => (.psiMinus, .psiMinus)
  | .psiMinus, .phiMinus => (.psiPlus, .psiMinus)
  | .psiPlus, .psiMinus => (.psiMinus, .phiMinus)
  | .psiMinus, .psiMinus => (.psiPlus, .phiMinus)
  | .phiPlus, .psiMinus => (.phiMinus, .psiMinus)
  | .phiMinus, .psiMinus => (.phiPlus, .psiMinus)

end BBPSSW.Distill


