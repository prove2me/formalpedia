-- Prove2me | Definitions.Def_BBPSSW_Distill_unilMap
-- name    : BBPSSW_Distill_unilMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:53.330593+00:00
-- url     : https://prove2.me/theorems/5199d4e0-a71d-462d-beaf-feacec72302e
-- title:
--   Bell-state permutations of unilateral Pauli rotations
-- statement:
--   The permutation of the Bell labels produced by a Pauli rotation of one particle, as listed in the paper:
--
--   1. $\sigma_x$: $\Psi^\pm\leftrightarrow\Phi^\pm$;
--   2. $\sigma_y$: $\Psi^\pm\leftrightarrow\Phi^\mp$;
--   3. $\sigma_z$: $\Psi^\pm\leftrightarrow\Psi^\mp$ and $\Phi^\pm\leftrightarrow\Phi^\mp$.
--
--   The theorem `unilateral_pauli_bell` states that the Pauli matrices act this way up to phase.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet ("σx maps Ψ± ↔ Φ±; σz maps Ψ± ↔ Ψ∓ and Φ± ↔ Φ∓, while σy maps Ψ± ↔ Φ∓")

import Mathlib
import Definitions.Def_BBPSSW_Distill_Axis
import Definitions.Def_BBPSSW_Distill_BellLabel

namespace BBPSSW.Distill

/-- **The permutation of Bell states effected by a unilateral Pauli rotation.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet): "thus σx maps Ψ± ↔ Φ±; σz maps Ψ± ↔ Ψ∓ and Φ± ↔ Φ∓, while σy
maps Ψ± ↔ Φ∓."

* `x`: Ψ⁻ ↔ Φ⁻, Ψ⁺ ↔ Φ⁺;
* `y`: Ψ⁺ ↔ Φ⁻, Ψ⁻ ↔ Φ⁺;
* `z`: Ψ⁻ ↔ Ψ⁺, Φ⁺ ↔ Φ⁻.

A transcription of the paper's list of label maps; the theorem `unilateral_pauli_bell` states
that the Pauli matrices act this way. -/
def unilMap : Axis → BellLabel → BellLabel
  | .x, .psiMinus => .phiMinus
  | .x, .psiPlus => .phiPlus
  | .x, .phiPlus => .psiPlus
  | .x, .phiMinus => .psiMinus
  | .y, .psiMinus => .phiPlus
  | .y, .psiPlus => .phiMinus
  | .y, .phiPlus => .psiMinus
  | .y, .phiMinus => .psiPlus
  | .z, .psiMinus => .psiPlus
  | .z, .psiPlus => .psiMinus
  | .z, .phiPlus => .phiMinus
  | .z, .phiMinus => .phiPlus

end BBPSSW.Distill


