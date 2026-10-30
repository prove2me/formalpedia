-- Prove2me | Definitions.Def_BBPSSW_Distill_bilMap
-- name    : BBPSSW_Distill_bilMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:54.544105+00:00
-- url     : https://prove2.me/theorems/ff7e22e2-31bf-4c3f-9bea-eb17425195b8
-- title:
--   Bell-state permutations of the bilateral rotations $B_x,B_y,B_z$
-- statement:
--   The permutation of the Bell labels produced by a bilateral $\pi/2$ rotation, as listed in the paper: each fixes the singlet $\Psi^-$ and one triplet and exchanges the other two,
--
--   1. $B_x$: $\Phi^+\leftrightarrow\Psi^+$ (fixing $\Psi^-,\Phi^-$);
--   2. $B_y$: $\Phi^-\leftrightarrow\Psi^+$ (fixing $\Psi^-,\Phi^+$);
--   3. $B_z$: $\Phi^+\leftrightarrow\Phi^-$ (fixing $\Psi^-,\Psi^+$).
--
--   The theorem `bilateral_rotation_bell` states that the bilateral rotations act this way up to phase.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet ("Bx mapping Φ+ ↔ Ψ+, By mapping Φ− ↔ Ψ+, and Bz mapping Φ+ ↔ Φ−")

import Mathlib
import Definitions.Def_BBPSSW_Distill_Axis
import Definitions.Def_BBPSSW_Distill_BellLabel

namespace BBPSSW.Distill

/-- **The permutation of Bell states effected by a bilateral π/2 rotation.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet): "Each of these operations leaves the singlet state and a
different one of the triplets invariant, interchanging the other two triplets, with Bx mapping
Φ+ ↔ Ψ+, By mapping Φ− ↔ Ψ+, and Bz mapping Φ+ ↔ Φ−."

* `x`: Φ⁺ ↔ Ψ⁺, fixing Ψ⁻ and Φ⁻;
* `y`: Φ⁻ ↔ Ψ⁺, fixing Ψ⁻ and Φ⁺;
* `z`: Φ⁺ ↔ Φ⁻, fixing Ψ⁻ and Ψ⁺.

A transcription of the paper's list; the theorem `bilateral_rotation_bell` states that the
bilateral rotations act this way. -/
def bilMap : Axis → BellLabel → BellLabel
  | .x, .phiPlus => .psiPlus
  | .x, .psiPlus => .phiPlus
  | .y, .phiMinus => .psiPlus
  | .y, .psiPlus => .phiMinus
  | .z, .phiPlus => .phiMinus
  | .z, .phiMinus => .phiPlus
  | _, b => b

end BBPSSW.Distill


