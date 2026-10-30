-- Prove2me | Definitions.Def_BBPSSW_Distill_wernerState
-- name    : BBPSSW_Distill_wernerState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:44.345671+00:00
-- url     : https://prove2.me/theorems/386325d9-f276-4dda-b46c-f3070115e301
-- title:
--   Werner state $W_F$, Eq. (4)
-- statement:
--   The Werner state of purity $F$ is the mixture of the singlet with weight $F$ and the three triplets with equal weights:
--
--   $$W_F=F\,|\Psi^-\rangle\langle\Psi^-|+\frac{1-F}{3}\Big(|\Psi^+\rangle\langle\Psi^+|+|\Phi^+\rangle\langle\Phi^+|+|\Phi^-\rangle\langle\Phi^-|\Big).$$
--
--   It is the state produced by a random bilateral rotation of any two-spin state with singlet fidelity $F$, and it is the input of the recurrence step.
--
--   **Formalization Note** Defined for every real $F$; it is a density matrix exactly when $0\le F\le1$.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (4), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_bellVec

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **The Werner state `W_F` of purity `F`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (4), p. 2:
"W_F = F·|Ψ−⟩⟨Ψ−| + (1−F)/3 |Ψ+⟩⟨Ψ+| + (1−F)/3 |Φ+⟩⟨Φ+| + (1−F)/3 |Φ−⟩⟨Φ−| (4)".

**Formalization Note.** `QAlgorithms.pureDensity ψ` is the rank-one matrix |ψ⟩⟨ψ|. The matrix
is defined for every real `F`; it is a density matrix exactly when `0 ≤ F ≤ 1`. -/
noncomputable def wernerState (F : ℝ) : Matrix QQ QQ ℂ :=
  (F : ℂ) • QAlgorithms.pureDensity (bellVec .psiMinus) +
    (((1 - F) / 3 : ℝ) : ℂ) • (QAlgorithms.pureDensity (bellVec .psiPlus) +
      QAlgorithms.pureDensity (bellVec .phiPlus) + QAlgorithms.pureDensity (bellVec .phiMinus))

end BBPSSW.Distill


