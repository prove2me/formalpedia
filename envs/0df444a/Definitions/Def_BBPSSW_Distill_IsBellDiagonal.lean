-- Prove2me | Definitions.Def_BBPSSW_Distill_IsBellDiagonal
-- name    : BBPSSW_Distill_IsBellDiagonal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:14.5192+00:00
-- url     : https://prove2.me/theorems/288c6b93-ded1-4c3c-a5d4-47cd7c6c6505
-- title:
--   Bell-diagonal two-qubit states
-- statement:
--   A two-spin state $W$ is Bell-diagonal if it is a mixture of the four Bell states,
--
--   $$W=\sum_{b\in\{\Psi^-,\Psi^+,\Phi^+,\Phi^-\}}q_b\,|b\rangle\langle b|,\qquad q_b\ge0,\ \sum_b q_b=1 .$$
--
--   Werner states are Bell-diagonal. Breeding takes Bell-diagonal pairs as input.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 3, step B1 ("any Bell-diagonal density matrix W")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_bellVec

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **Bell-diagonal two-qubit states.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 3, step B1 ("n impure pairs described by any Bell-diagonal density matrix W") and
p. 2 ("Mixtures of the four states Ψ± and Φ±—known as the four Bell states").

`W` is Bell-diagonal if `W = ∑_b q_b |b⟩⟨b|` over the four Bell states for some probability
vector `q` (`q_b ≥ 0`, `∑ q_b = 1`). Such a `W` is a density matrix. -/
def IsBellDiagonal (W : Matrix QQ QQ ℂ) : Prop :=
  ∃ q : BellLabel → ℝ, (∀ b, 0 ≤ q b) ∧ ∑ b, q b = 1 ∧
    W = ∑ b, (q b : ℂ) • QAlgorithms.pureDensity (bellVec b)

end BBPSSW.Distill


