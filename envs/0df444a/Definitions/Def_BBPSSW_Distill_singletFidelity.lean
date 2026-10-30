-- Prove2me | Definitions.Def_BBPSSW_Distill_singletFidelity
-- name    : BBPSSW_Distill_singletFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:53.182983+00:00
-- url     : https://prove2.me/theorems/c4db4c5a-2f1a-4d77-b7f3-293cce1350b7
-- title:
--   Singlet fidelity $F=\langle\Psi^-|M|\Psi^-\rangle$
-- statement:
--   The purity of a two-spin state $M$ is its fidelity with a perfect singlet,
--
--   $$F=\langle\Psi^-|M|\Psi^-\rangle .$$
--
--   **Formalization Note** The value is the real part of $\langle\Psi^-|M|\Psi^-\rangle$ (the reused `quad`), which is the whole value for Hermitian $M$, in particular for a density matrix.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (2), pp. 1–2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_bellVec

open QAlgorithms.Papers.Independent.Information100.P21 (QQ quad)

namespace BBPSSW.Distill

/-- **Singlet fidelity `F = ⟨Ψ⁻|M|Ψ⁻⟩`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (2), pp. 1–2: "The purity of M can be conveniently expressed by its fidelity
F = ⟨Ψ−|M|Ψ−⟩ (2) relative to a perfect singlet."

**Formalization Note.** `quad M v` (`…Information100.P21.quad`) is the real part of
`∑ i j, conj (v i) * M i j * v j` = Re ⟨v|M|v⟩; on a Hermitian `M` (in particular a density
matrix) this is the whole value ⟨Ψ⁻|M|Ψ⁻⟩. -/
noncomputable def singletFidelity (M : Matrix QQ QQ ℂ) : ℝ :=
  quad M (bellVec .psiMinus)

end BBPSSW.Distill


